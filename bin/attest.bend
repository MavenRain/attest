import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel.bend as K
import ../lib/kernel_primitives.bend as G
import ../lib/kernel_eval.bend as V
import ../lib/kernel_metadata.bend as M
import ../lib/erasure.bend as R
import ../erase/opaque.bend as O
import ../surface/elab.bend as E
import ../surface/io.bend as I

type Cli.display is Data:
  Cli.Summary{}
  Cli.Checked_form{}
  Cli.Axioms{}

type Cli.command is Data:
  Cli.Spec_count{}
  Cli.Check_file{mode: Cli.display, path: String}
  Cli.Erase_file{path: String}
  Cli.Arguments{}

def Cli.usage() -> String:
  "usage: attest check [--print|--axioms] FILE.att | attest build --erase FILE.att | attest spec-count"

def Cli.parse_one(spec: Bool) -> Cli.command:
  match spec:
    case True{}: Cli.Spec_count{}
    case False{}: Cli.Arguments{}

def Cli.parse_two(check: Bool, path: String) -> Cli.command:
  match check:
    case True{}: Cli.Check_file{Cli.Summary{}, path}
    case False{}: Cli.Arguments{}

def Cli.parse_three(check: Bool, build: Bool, print: Bool, axioms: Bool, erase: Bool, path: String) -> Cli.command:
  match check build print axioms erase:
    case True{} _ True{} _ _: Cli.Check_file{Cli.Checked_form{}, path}
    case True{} _ _ True{} _: Cli.Check_file{Cli.Axioms{}, path}
    case _ True{} _ _ True{}: Cli.Erase_file{path}
    case _ _ _ _ _: Cli.Arguments{}

def Cli.parse(args: List<String>) -> Cli.command:
  match args:
    case [name]: Cli.parse_one(String.eq(name, "spec-count"))
    case [name, path]: Cli.parse_two(String.eq(name, "check"), path)
    case [+name, +option, path]: Cli.parse_three(String.eq(name, "check"), String.eq(name, "build"), String.eq(option, "--print"), String.eq(option, "--axioms"), String.eq(option, "--erase"), path)
    case _: Cli.Arguments{}

def Cli.valid_extension(path: String) -> Bool:
  match path:
    case SCon{Chr{46}, SCon{Chr{97}, SCon{Chr{116}, SCon{Chr{116}, SNil{}}}}}: True{}
    case SCon{Chr{46}, SCon{Chr{107}, SCon{Chr{97}, SCon{Chr{110}, SNil{}}}}}: True{}
    case SCon{head, tail}: Cli.valid_extension(tail)
    case SNil{}: False{}

def Cli.read_valid(valid: Bool, path: String) -> IO(Result<&2, &2, String, String>):
  match valid:
    case True{}: I.Sys_io.read_file(path)
    case False{}: IO.pure(Result<&2, &2, String, String>, Fail{"expected a .att or inherited .kan source"})

def Cli.read_file(+path: String) -> IO(Result<&2, &2, String, String>):
  Cli.read_valid(Cli.valid_extension(path), path)

def Cli.definitions(rows: E.Elab.rows) -> Nat:
  match rows:
    case Nil{}: 0n
    case Con{F.Pair2{name, F.Global.Def{entry}}, tail}: (1n + Cli.definitions(tail) : Nat)
    case Con{head, tail}: Cli.definitions(tail)

def Cli.axiom_lines(names: List<&2, String>) -> String:
  match names:
    case Nil{}: ""
    case Con{name, tail}: "AXIOM " ++ name ++ "\n" ++ Cli.axiom_lines(tail)

def Cli.axioms(path: String, +names: List<&2, String>) -> String:
  Cli.axiom_lines(names) ++ "AXIOMS " ++ path ++ " count=" ++ Nat.show(List.length(&2, String, names)) ++ "\n"

def Cli.render(mode: Cli.display, path: String, +rows: E.Elab.rows) -> String:
  match mode:
    case Cli.Summary{}: "CHECK " ++ path ++ " defs=" ++ Nat.show(Cli.definitions(rows)) ++ " ok\n"
    case Cli.Checked_form{}: E.Elab.checked_form(rows) ++ "CHECK " ++ path ++ " defs=" ++ Nat.show(Cli.definitions(rows)) ++ " ok\n"
    case Cli.Axioms{}: Cli.axioms(path, E.Elab.axiom_names(rows))

def Cli.check_failure(path: String, error: F.Error.t) -> IO(Unit):
  +message : String = F.Error.to_string(error)
  do IO<Unit>:
    printed : Unit <- IO.write("CHECK " ++ path ++ " FAIL " ++ message ++ "\n")
    IO.die(Unit, 1, "attest: check: " ++ message)

def Cli.checked(result: Result<&2, &2, F.Error.t, E.Elab.rows>, mode: Cli.display, path: String) -> IO(Unit):
  match result:
    case Fail{error}: Cli.check_failure(path, error)
    case Done{rows}: IO.write(Cli.render(mode, path, rows))

def Cli.check_read(result: Result<&2, &2, String, String>, mode: Cli.display, path: String) -> IO(Unit):
  match result:
    case Fail{message}: IO.die(Unit, 64, "attest: check: " ++ path ++ ": " ++ message)
    case Done{source}: Cli.checked(E.Elab.check_text(G.Global.initial, source), mode, path)

def Cli.semantics() -> R.Erase.Semantics:
  R.Erase.Semantics{ctx => term => K.Check.infer_univ_stateful(ctx, term), ctx => mode => term => K.Check.infer_stateful(ctx, mode, term), globals => size => value => V.Eval.quote(globals, size, value)}

def Cli.erased(result: Result<&2, &2, F.Error.t, List<&2, F.Pair2<String, R.Erase.entry>>>, path: String) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit, 2, "attest: erase: " ++ path ++ ": " ++ F.Error.to_string(error))
    case Done{rows}: IO.write(R.Erase.print(rows))

def Cli.erase_checked(result: Result<&2, &2, F.Error.t, E.Elab.checked>, path: String) -> IO(Unit):
  match result:
    case Fail{error}: Cli.check_failure(path, error)
    case Done{F.Pair2{globals, rows}}: Cli.erased(O.Opaque.program(Cli.semantics, C.Budget.unlimited, globals, rows), path)

def Cli.erase_read(result: Result<&2, &2, String, String>, path: String) -> IO(Unit):
  match result:
    case Fail{message}: IO.die(Unit, 64, "attest: check: " ++ path ++ ": " ++ message)
    case Done{source}: Cli.erase_checked(E.Elab.check_in(G.Global.initial, source), path)

def Cli.counts(valid: Bool) -> IO(Unit):
  match valid:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.die(Unit, 1, "attest: spec-count: expected two formers and five shapes")

def Cli.run(command: Cli.command) -> IO(Unit):
  match command:
    case Cli.Arguments{}: IO.die(Unit, 64, Cli.usage)
    case Cli.Spec_count{}:
      do IO<Unit>:
        printed : Unit <- IO.write(M.SpecCount.print)
        Cli.counts(M.SpecCount.valid)
    case Cli.Check_file{mode, +path}:
      do IO<Unit>:
        result : Result<&2, &2, String, String> <- Cli.read_file(path)
        Cli.check_read(result, mode, path)
    case Cli.Erase_file{+path}:
      do IO<Unit>:
        result : Result<&2, &2, String, String> <- Cli.read_file(path)
        Cli.erase_read(result, path)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Cli.run(Cli.parse(args))
