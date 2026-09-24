import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel.bend as K
import ../lib/kernel_primitives.bend as G
import ../lib/kernel_eval.bend as V
import ../lib/kernel_pp.bend as Pp
import ../lib/kernel_order.bend as O
import ../lib/erasure.bend as R
import ../surface/elab.bend as E
import ../surface/parser.bend as P
import ../surface/syntax.bend as S
import ../surface/io.bend as I
import ../test/surface.bend as T

def Suite.semantics() -> R.Erase.Semantics:
  R.Erase.Semantics{ctx => term => K.Check.infer_univ_stateful(ctx, term), ctx => mode => term => K.Check.infer_stateful(ctx, mode, term), globals => size => value => V.Eval.quote(globals, size, value)}

def Suite.assert(equal: Bool, error: F.Error.t) -> Result<&2, &2, F.Error.t, Unit>:
  match equal:
    case True{}: Done{Unit{}}
    case False{}: Fail{error}

def Suite.normal(+globals: F.Global.t, name: String) -> Result<&2, &2, F.Error.t, String>:
  do Result<&2, &2, F.Error.t, String>:
    value : F.Value.t <- V.Eval.eval(globals, Nil{}, F.Term.Global{name})
    term : F.Term.t <- V.Eval.quote(globals, 0n, value)
    return Pp.Pp.term(Nil{}, term)

@unsafe
def Suite.computations(pairs: List<&2, F.Pair2<String, String>>, +globals: F.Global.t) -> Result<&2, &2, F.Error.t, Unit>:
  match pairs:
    case Nil{}: Done{Unit{}}
    case Con{F.Pair2{+actual, expected}, tail}:
      do Result<&2, &2, F.Error.t, Unit>:
        +got : String <- Suite.normal(globals, actual)
        want : String <- Suite.normal(globals, expected)
        same : Unit <- Suite.assert(String.eq(got, want), F.Error.Mismatch{actual ++ " did not compute: " ++ got})
        Suite.computations(tail, globals)

def Suite.is_neutral(value: F.Value.t, message: String) -> Result<&2, &2, F.Error.t, Unit>:
  match value:
    case F.Value.VNeutral{head, spine}: Done{Unit{}}
    case _: Fail{F.Error.Mismatch{message}}

@unsafe
def Suite.neutrals(names: List<&2, String>, +globals: F.Global.t) -> Result<&2, &2, F.Error.t, Unit>:
  match names:
    case Nil{}: Done{Unit{}}
    case Con{+name, tail}:
      do Result<&2, &2, F.Error.t, Unit>:
        value : F.Value.t <- V.Eval.eval(globals, Nil{}, F.Term.Global{name})
        neutral : Unit <- Suite.is_neutral(value, name ++ " unfolded before its guarded argument")
        Suite.neutrals(tail, globals)

def Suite.neutral_leg(legs: List<&2, F.Value.vleg>, globals: F.Global.t) -> Result<&2, &2, F.Error.t, Unit>:
  match legs:
    case [F.Value.Leg{binders, closure}]:
      do Result<&2, &2, F.Error.t, Unit>:
        body : F.Value.t <- V.Eval.open_closure(globals, closure, [F.Value.var(0n)])
        Suite.is_neutral(body, "recursive call unfolded on a neutral argument")
    case _: Fail{F.Error.Mismatch{"neutral leg"}}

def Suite.neutral_body(value: F.Value.t, globals: F.Global.t) -> Result<&2, &2, F.Error.t, Unit>:
  match value:
    case F.Value.VSec{shape, legs}: Suite.neutral_leg(legs, globals)
    case _: Fail{F.Error.Mismatch{"neutral lambda"}}

def Suite.opaque(entry: Maybe<&2, F.Global.entry>, globals: F.Global.t) -> Result<&2, &2, F.Error.t, Unit>:
  match entry:
    case None{}: Fail{F.Error.Unbound{"double"}}
    case Some{F.Global.Def{F.Global.DefEntry{ty, body, reducible, rec_arg, partial}}}:
      do Result<&2, &2, F.Error.t, Unit>:
        value : F.Value.t <- V.Eval.eval(F.Global.add("double", F.Global.Def{F.Global.DefEntry{ty, body, False{}, rec_arg, partial}}, globals), Nil{}, F.Term.Global{"doubled"})
        Suite.is_neutral(value, "an explicitly opaque recursive definition unfolded")
    case Some{entry}: Fail{F.Error.Mismatch{"double definition"}}

def Suite.recursive_checked(checked: E.Elab.checked) -> Result<&2, &2, F.Error.t, Unit>:
  F.Pair2{+globals, rows} = checked
  do Result<&2, &2, F.Error.t, Unit>:
    computed : Unit <- Suite.computations([F.Pair2{"doubled", "four"}, F.Pair2{"mutualValue", "two"}, F.Pair2{"helper", "z"}, F.Pair2{"helperDirect", "z"}, F.Pair2{"spare", "z"}, F.Pair2{"kept", "seven"}, F.Pair2{"chosen", "seven"}, F.Pair2{"indexed", "one"}], globals)
    guarded : Unit <- Suite.neutrals(["double", "keep", "partial"], globals)
    neutral : F.Value.t <- V.Eval.eval(globals, Nil{}, F.Term.Global{"neutral"})
    body : Unit <- Suite.neutral_body(neutral, globals)
    Suite.opaque(F.Global.find("double", globals), globals)

def Suite.recursive_values() -> Result<&2, &2, F.Error.t, Unit>:
  do Result<&2, &2, F.Error.t, Unit>:
    checked : E.Elab.checked <- E.Elab.check_in(G.Global.initial, T.SurfaceTest.recursive_source)
    Suite.recursive_checked(checked)

def Suite.result(result: Result<&2, &2, F.Error.t, Unit>) -> IO(Unit):
  match result:
    case Done{unit}: IO.pure(Unit, Unit{})
    case Fail{error}: IO.die(Unit, 1, F.Error.to_string(error))

def Suite.refusal_equal(equal: Bool, message: String) -> IO(Unit):
  match equal:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.die(Unit, 1, "the message is \"" ++ message ++ "\"")

def Suite.smu_result(result: Result<&2, &2, F.Error.t, F.Value.t>) -> IO(Unit):
  match result:
    case Done{value}: IO.die(Unit, 1, "the right former at a mu shape is admitted at M1")
    case Fail{error}:
      +message : String = F.Error.message(error)
      Suite.refusal_equal(String.eq(message, "a right former at a mu shape arrives at M2"), message)

def Suite.guarded_self() -> F.Term.t:
  +arrow : F.Shape.t<F.Term.t> = F.Shape.SPi{F.Quantity.Many{}, "n", F.Term.Global{"N"}}
  F.Term.Sec{arrow, [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "n"}],
    F.Term.Elim{F.Term.Elimination{F.Shape.SMu{"N", Nil{}}, F.Term.Var{0n}, F.Quantity.Many{},
      Some{F.Term.Motive{Some{"N"}, Nil{}, "x", F.Term.Global{"N"}}},
      [F.Pair2{F.Term.ACtor{"succ"}, F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "m"}], F.Term.Out{arrow, F.Term.APt{F.Quantity.Many{}, F.Term.Var{0n}}, F.Term.Global{"self"}}}}]}}}]}

def Suite.guarded_result(result: Result<&2, &2, F.Error.t, Maybe<&2, Nat>>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit, 1, "the message is \"" ++ F.Error.message(error) ++ "\"")
    case Done{None{}}: IO.die(Unit, 1, "the guarded self reference answers no position")
    case Done{Some{0n}}: IO.pure(Unit, Unit{})
    case Done{Some{position}}: IO.die(Unit, 1, "the guarded position is " ++ Nat.show(position))

def Suite.self_result(result: Result<&2, &2, F.Error.t, Maybe<&2, Nat>>) -> IO(Unit):
  match result:
    case Done{position}: IO.die(Unit, 1, "the unguarded self reference is admitted at M1")
    case Fail{error}:
      +message : String = F.Error.message(error)
      do IO<Unit>:
        refused : Unit <- Suite.refusal_equal(String.eq(message, "recursive definition self failed the structural termination guard"), message)
        Suite.guarded_result(O.Totality.guard(G.Global.initial, "self", F.Term.Global{"Nat"}, Suite.guarded_self))

type Suite.mode is Data:
  Suite.Parse{}
  Suite.Checked{}
  Suite.Erased{}
  Suite.Check_error{}
  Suite.Erase_error{}

def Suite.tree_equal(equal: Bool) -> IO(Unit):
  match equal:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.die(Unit, 1, "the printed text parses to a different tree")

def Suite.parsed_second(first: List<&2, S.Syntax.decl>, second: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> IO(Unit):
  match second:
    case Fail{error}: IO.die(Unit, 1, F.Error.message(error))
    case Done{second}: Suite.tree_equal(S.Syntax.equal_declarations(first, second))

def Suite.parsed(result: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit, 1, F.Error.message(error))
    case Done{+tree}: Suite.parsed_second(tree, P.Parser.parse(S.Syntax.print(tree)))

def Suite.checked(result: Result<&2, &2, F.Error.t, E.Elab.rows>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit, 1, F.Error.to_string(error))
    case Done{rows}: IO.write(E.Elab.checked_form(rows))

def Suite.check_error(result: Result<&2, &2, F.Error.t, E.Elab.rows>) -> IO(Unit):
  match result:
    case Fail{error}: IO.write(F.Error.message(error))
    case Done{rows}: IO.die(Unit, 2, "the file checks and the negative expects it to fail")

def Suite.erased(result: Result<&2, &2, F.Error.t, List<&2, F.Pair2<String, R.Erase.entry>>>, negative: Bool) -> IO(Unit):
  match result negative:
    case Fail{error} True{}: IO.write(F.Error.message(error))
    case Fail{error} False{}: IO.die(Unit, 1, F.Error.to_string(error))
    case Done{rows} True{}: IO.die(Unit, 2, "the file erases and the negative expects the erasure to fail")
    case Done{rows} False{}: IO.write(R.Erase.print(rows))

def Suite.erase_checked(result: Result<&2, &2, F.Error.t, E.Elab.checked>, negative: Bool) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit, 1, F.Error.to_string(error))
    case Done{F.Pair2{globals, rows}}: Suite.erased(R.Erase.program(Suite.semantics, C.Budget.unlimited, globals, rows), negative)

def Suite.source(result: Result<&2, &2, String, String>, mode: Suite.mode) -> IO(Unit):
  match result:
    case Fail{message}: IO.die(Unit, 1, message)
    case Done{source}:
      match mode:
        case Suite.Parse{}: Suite.parsed(P.Parser.parse(source))
        case Suite.Checked{}: Suite.checked(E.Elab.check_text(G.Global.initial, source))
        case Suite.Erased{}: Suite.erase_checked(E.Elab.check_in(G.Global.initial, source), False{})
        case Suite.Check_error{}: Suite.check_error(E.Elab.check_text(G.Global.initial, source))
        case Suite.Erase_error{}: Suite.erase_checked(E.Elab.check_in(G.Global.initial, source), True{})

def Suite.file(mode: Maybe<&2, Suite.mode>, path: String) -> IO(Unit):
  match mode:
    case None{}: IO.die(Unit, 64, "unknown suite probe mode")
    case Some{mode}:
      do IO<Unit>:
        source : Result<&2, &2, String, String> <- I.Sys_io.read_file(path)
        Suite.source(source, mode)

def Suite.mode_of(parse: Bool, checked: Bool, erased: Bool, check_error: Bool, erase_error: Bool) -> Maybe<&2, Suite.mode>:
  match parse checked erased check_error erase_error:
    case True{} _ _ _ _: Some{Suite.Parse{}}
    case _ True{} _ _ _: Some{Suite.Checked{}}
    case _ _ True{} _ _: Some{Suite.Erased{}}
    case _ _ _ True{} _: Some{Suite.Check_error{}}
    case _ _ _ _ True{}: Some{Suite.Erase_error{}}
    case _ _ _ _ _: None{}

def Suite.direct(smu: Bool, self: Bool, recursive: Bool) -> IO(Unit):
  match smu self recursive:
    case True{} _ _: Suite.smu_result(K.Check.infer(C.Check.make(G.Global.initial, C.Budget.unlimited), F.Quantity.Many{}, F.Term.Ran{F.Shape.SMu{"F", [F.Term.Univ{F.Level.zero}]}, F.Term.Sec{F.Shape.SColl{0n}, Nil{}}}))
    case _ True{} _: Suite.self_result(O.Totality.guard(G.Global.initial, "self", F.Term.Global{"Nat"}, F.Term.Global{"self"}))
    case _ _ True{}: Suite.result(Suite.recursive_values)
    case _ _ _: IO.die(Unit, 64, "unknown suite probe mode")

def Suite.args(args: List<String>) -> IO(Unit):
  match args:
    case [+name]: Suite.direct(String.eq(name, "kneg-smu"), String.eq(name, "kneg-self"), String.eq(name, "recursive-values"))
    case [+name, path]: Suite.file(Suite.mode_of(String.eq(name, "parse"), String.eq(name, "checked"), String.eq(name, "erased"), String.eq(name, "check-error"), String.eq(name, "erase-error")), path)
    case _: IO.die(Unit, 64, "usage: suite_probe MODE [FILE]")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Suite.args(args)
