import Base
import ../lib/foundation.bend as F
import ../lib/kernel_primitives.bend as K
import ../surface/io.bend as I
import ../surface/parser.bend as P
import ../surface/syntax.bend as S
import ../surface/elab.bend as E

# Base.IO.now has millisecond resolution. Batch 100 identical passes for a useful mean.
def Bench.parse_loop(count: Nat, +source: String, last: List<&2, S.Syntax.decl>) -> Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>:
  match count:
    case Zero{}:
      Done{last}
    case Succ{rest}:
      do Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>:
        parsed: List<&2, S.Syntax.decl> <- P.Parser.parse(source)
        Bench.parse_loop(rest, source, parsed)

def Bench.check_loop(count: Nat, +decls: List<&2, S.Syntax.decl>) -> Result<&2, &2, F.Error.t, Unit>:
  match count:
    case Zero{}:
      Done{Unit{}}
    case Succ{rest}:
      do Result<&2, &2, F.Error.t, Unit>:
        checked: E.Elab.checked <- E.Elab.elab_program_in(K.Global.initial, decls)
        Bench.check_loop(rest, decls)

def Bench.pad(text: String, short: Bool) -> String:
  match short:
    case True{}:
      "0" ++ text
    case False{}:
      text

def Bench.fraction(+value: Nat) -> String:
  Bench.pad(F.Text.nat(value), Nat.is_lt(value, 10n))

def Bench.milliseconds(+elapsed: Nat) -> String:
  F.Text.nat(Nat.div(elapsed, 100n)) ++ "." ++ Bench.fraction(Nat.mod(elapsed, 100n)) ++ "0000"

def Bench.finish(parse_ms: Nat, check_ms: Nat, result: Result<&2, &2, F.Error.t, Unit>) -> IO(Unit):
  match result:
    case Fail{error}:
      IO.die(Unit, 1, F.Error.to_string(error))
    case Done{unit}:
      IO.print("parse " ++ Bench.milliseconds(parse_ms) ++ "\nelaborate-check " ++ Bench.milliseconds(check_ms))

def Bench.parsed(parse_ms: Nat, result: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> IO(Unit):
  match result:
    case Fail{error}:
      IO.die(Unit, 1, F.Error.to_string(error))
    case Done{decls}:
      do IO<Unit>:
        start: Nat <- IO.now()
        checked: Result<&2, &2, F.Error.t, Unit> <- IO.pure(Result<&2, &2, F.Error.t, Unit>, Bench.check_loop(100n, decls))
        finish: Nat <- IO.now()
        Bench.finish(parse_ms, Nat.sub(finish, start), checked)

def Bench.read(result: Result<&2, &2, String, String>) -> IO(Unit):
  match result:
    case Fail{message}:
      IO.die(Unit, 64, message)
    case Done{source}:
      do IO<Unit>:
        start: Nat <- IO.now()
        parsed: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>> <- IO.pure(Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>, Bench.parse_loop(100n, source, []))
        finish: Nat <- IO.now()
        Bench.parsed(Nat.sub(finish, start), parsed)

def main() -> IO(Unit):
  do IO<Unit>:
    source: Result<&2, &2, String, String> <- I.Sys_io.read_file("/dev/stdin")
    Bench.read(source)
