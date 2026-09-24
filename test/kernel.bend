import Base
import ../lib/foundation.bend as F
import ../lib/kernel_primitives.bend as P
import ../lib/kernel_eval.bend as E
import ../lib/kernel_pp.bend as T
import ../lib/kernel_context.bend as C
import ../lib/kernel.bend as K
import ../lib/kernel_util.bend as U

def Test.lit(n: Nat) -> F.Term.t:
  F.Term.Lit{F.Literal.LInt{F.Bignum.from_nat(n)}}

def Test.render(result: Result<&2, &2, F.Error.t, F.Term.t>) -> String:
  match result:
    case Fail{error}: "ERROR " ++ F.Error.to_string(error)
    case Done{term}: T.Pp.term(Nil{}, term)

def Test.normal(+globals: F.Global.t, term: F.Term.t) -> String:
  Test.render(Result.bind(&2, &2, F.Error.t, F.Value.t, F.Term.t,
    E.Eval.eval(globals, Nil{}, term), value => E.Eval.quote(globals, 0n, value)))

def Test.app(fn: F.Term.t, arg: F.Term.t) -> F.Term.t:
  F.Term.Out{F.Shape.SPi{F.Quantity.Many{}, "x", P.Prim.nat_ty}, F.Term.APt{F.Quantity.Many{}, arg}, fn}

def Test.primitive(name: String, a: Nat, b: Nat, expected: String) -> Bool:
  String.eq(Test.normal(P.Global.initial, Test.app(Test.app(F.Term.Global{name}, Test.lit(a)), Test.lit(b))), expected)

def Test.identity() -> F.Term.t:
  F.Term.Sec{F.Shape.SPi{F.Quantity.Many{}, "x", P.Prim.nat_ty},
    [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "x"}], F.Term.Var{0n}}]}

def Test.is_error(result: Result<&2, &2, F.Error.t, F.Value.t>) -> Bool:
  match result:
    case Fail{error}: True{}
    case Done{value}: False{}

def Test.annotation() -> Bool:
  String.eq(Test.normal(P.Global.initial, P.Rules.unit_ty(F.Level.one)),
    "((Ran SColl 0 (Sec SColl 0 [])) : Type 1)")

def Test.guard_globals(reducible: Bool) -> F.Global.t:
  F.Global.add("guarded", F.Global.Def{F.Global.DefEntry{P.Rules.arrow(F.Quantity.Many{}, "x", P.Prim.nat_ty, P.Prim.nat_ty),
    F.Term.Sec{F.Shape.SPi{F.Quantity.Many{}, "x", P.Prim.nat_ty},
      [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "x"}], Test.lit(9n)}]}, reducible, Some{0n}, False{}}}, P.Global.initial)

def Test.neutral(result: Result<&2, &2, F.Error.t, F.Value.t>) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{value}: Maybe.is_some(&2, F.Pair2<F.Value.head, List<&2, F.Value.spine>>, F.Value.as_neutral(value))

def Test.guarded_ctor() -> F.Term.t:
  F.Term.In{F.Shape.SMu{"N", Nil{}}, F.Term.ACtor{"zero"}, Nil{}}

def Test.run() -> List<&2, Bool>:
  [Test.primitive("natAdd", 40n, 2n, "42"),
   Test.primitive("natSub", 2n, 40n, "0"),
   Test.primitive("natMul", 6n, 7n, "42"),
   Test.primitive("natEq", 2n, 2n, "(In SColl 2 (ALeg 1) [(Sec SColl 0 [])])"),
   Test.primitive("natLt", 3n, 2n, "(In SColl 2 (ALeg 0) [(Sec SColl 0 [])])"),
   String.eq(Test.normal(P.Global.initial, Test.app(Test.identity, Test.lit(42n))), "42"),
   String.eq(Test.normal(P.Global.initial, F.Term.Let{"x", P.Prim.nat_ty, Test.lit(5n), F.Term.Var{0n}}), "5"),
   Test.annotation,
   Test.is_error(E.Eval.eval(P.Global.initial, Nil{}, F.Term.Var{0n})),
   Test.is_error(E.Eval.eval(P.Global.initial, Nil{}, F.Term.Global{"missing"})),
   Test.is_error(E.Eval.eval(P.Global.initial, Nil{}, F.Term.Auto{})),
   Test.neutral(E.Eval.eval(Test.guard_globals(True{}), Nil{}, F.Term.Global{"guarded"})),
   String.eq(Test.normal(Test.guard_globals(True{}), Test.app(F.Term.Global{"guarded"}, Test.guarded_ctor)), "9"),
   Test.neutral(E.Eval.eval(Test.guard_globals(False{}), Nil{}, Test.app(F.Term.Global{"guarded"}, Test.guarded_ctor))),
   Test.neutral(E.Eval.eval(Test.guard_globals(True{}), [F.Value.var(0n)], Test.app(F.Term.Global{"guarded"}, F.Term.Var{0n}))),
   String.eq(T.Pp.literal(F.Literal.LString{"a\n\t\"\\"}), "\"a\\n\\t\\\"\\\\\"")]

def Test.ctx() -> C.Check.ctx:
  C.Check.make(P.Global.initial, C.Budget.unlimited)

def Test.unit_ok(result: Result<&2, &2, F.Error.t, Unit>) -> Bool:
  Result.is_done(&2, &2, F.Error.t, Unit, result)

def Test.value_ok(result: Result<&2, &2, F.Error.t, F.Value.t>) -> Bool:
  Result.is_done(&2, &2, F.Error.t, F.Value.t, result)

def Test.error(-A: Data, result: Result<&2, &2, F.Error.t, A>, message: String) -> Bool:
  match result:
    case Fail{error}: String.eq(F.Error.message(error), message)
    case Done{value}: False{}

def Test.bool_result(result: Result<&2, &2, F.Error.t, Bool>) -> Bool:
  Result.default(&2, &2, F.Error.t, Bool, result, False{})

def Test.function_type(q: F.Quantity.t) -> F.Term.t:
  P.Rules.arrow(q, "x", P.Prim.nat_ty, P.Prim.nat_ty)

def Test.lambda(q: F.Quantity.t, body: F.Term.t) -> F.Term.t:
  F.Term.Sec{F.Shape.SPi{F.Quantity.Many{}, "x", P.Prim.nat_ty}, [F.Term.Leg{[F.Pair2{q, "x"}], body}]}

def Test.check_lambda(+q: F.Quantity.t, body: F.Term.t) -> Result<&2, &2, F.Error.t, Unit>:
  do Result<&2, &2, F.Error.t, Unit>:
    ty: F.Value.t <- E.Eval.eval(P.Global.initial, Nil{}, Test.function_type(q))
    K.Check.check(Test.ctx, F.Quantity.Many{}, Test.lambda(q, body), ty)

def Test.check_as(term: F.Term.t, type_term: F.Term.t) -> Result<&2, &2, F.Error.t, Unit>:
  do Result<&2, &2, F.Error.t, Unit>:
    ty: F.Value.t <- E.Eval.eval(P.Global.initial, Nil{}, type_term)
    K.Check.check(Test.ctx, F.Quantity.Many{}, term, ty)

def Test.eta() -> Bool:
  +globals = F.Global.add("f", F.Global.Axiom{F.Global.AxiomEntry{Test.function_type(F.Quantity.Many{})}}, P.Global.initial)
  Test.bool_result((
    do Result<&2, &2, F.Error.t, Bool>:
      ty: F.Value.t <- E.Eval.eval(globals, Nil{}, Test.function_type(F.Quantity.Many{}))
      a: F.Value.t <- E.Eval.eval(globals, Nil{}, F.Term.Global{"f"})
      b: F.Value.t <- E.Eval.eval(globals, Nil{}, Test.lambda(F.Quantity.Many{}, Test.app(F.Term.Global{"f"}, F.Term.Var{0n})))
      K.Conv.conv(C.Check.make(globals, C.Budget.unlimited), ty, a, b)
  ))

def Test.prop_globals() -> F.Global.t:
  F.Global.add_family("P", F.Positivity.Family{"P", Nil{}, Nil{}, F.Level.zero,
    F.Positivity.Complete{["a", "b"]}, [F.Positivity.Ctor{"a", Nil{}, Nil{}, 0n, False{}}, F.Positivity.Ctor{"b", Nil{}, Nil{}, 0n, False{}}], True{}}, P.Global.initial)

def Test.proof_irrelevance() -> Bool:
  +shape = {F.Shape.SMu{"P", Nil{}} : F.Shape.t<F.Value.t>}
  Test.bool_result(K.Conv.conv(C.Check.make(Test.prop_globals, C.Budget.unlimited),
    F.Value.VLan{shape, F.Value.Closure{Nil{}, P.Rules.diagram_of(Nil{})}, None{}},
    F.Value.VIn{shape, F.Value.VACtor{"a"}, Nil{}}, F.Value.VIn{shape, F.Value.VACtor{"b"}, Nil{}}))

def Test.budget_remaining(budget: C.Budget.t, expected: Nat) -> Bool:
  match budget:
    case C.Budget.Unlimited{}: False{}
    case C.Budget.Steps{remaining}: Nat.is_eq(remaining, expected)

def Test.budget_success() -> Bool:
  +reply = K.Check.infer_stateful(C.Check.make(P.Global.initial, C.Budget.Steps{1n}), F.Quantity.Many{}, Test.lit(0n))
  Bool.and(Test.value_ok(U.Kernel.fst(Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t, reply)),
    Test.budget_remaining(U.Kernel.snd(Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t, reply), 0n))

def Test.budget_nested() -> Bool:
  +reply = K.Check.infer_stateful(C.Check.make(P.Global.initial, C.Budget.Steps{3n}), F.Quantity.Many{},
    P.Rules.arrow(F.Quantity.Many{}, "x", F.Term.Univ{F.Level.zero}, F.Term.Univ{F.Level.zero}))
  Bool.and(Test.value_ok(U.Kernel.fst(Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t, reply)),
    Test.budget_remaining(U.Kernel.snd(Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t, reply), 0n))

def Test.checker() -> List<&2, Bool>:
  [Test.value_ok(K.Check.infer_term(P.Global.initial, Test.lit(42n))),
   Test.value_ok(K.Check.infer_term(P.Global.initial, F.Term.Ann{Test.identity, Test.function_type(F.Quantity.Many{})})),
   Test.unit_ok(Test.check_lambda(F.Quantity.One{}, F.Term.Var{0n})),
   Test.error(Unit, Test.check_lambda(F.Quantity.One{}, Test.lit(0n)), "the linear binder x must be used exactly once on every runtime path"),
   Test.error(Unit, Test.check_lambda(F.Quantity.Zero{}, F.Term.Var{0n}), "the erased binder x is read in a runtime position"),
   Test.error(Unit, Test.check_as(Test.lambda(F.Quantity.One{}, F.Term.Var{0n}), Test.function_type(F.Quantity.Many{})), "the binder x is marked 1 and the type marks it w"),
   Test.error(F.Value.t, K.Check.infer_term(P.Global.initial, F.Term.Ran{F.Shape.SMu{"F", [F.Term.Univ{F.Level.zero}]}, P.Rules.diagram_of(Nil{})}), "a right former at a mu shape arrives at M2"),
   Test.error(F.Value.t, K.Check.infer_term(P.Global.initial, F.Term.Lan{F.Shape.SPar{P.Prim.nat_ty, P.Prim.nat_ty}, P.Rules.diagram_of(Nil{})}), "SPar arrives at M1"),
   Test.error(F.Value.t, K.Check.infer_term(P.Global.initial, F.Term.Lan{F.Shape.SNu{"F", Nil{}}, P.Rules.diagram_of(Nil{})}), "SNu arrives at M2"),
   Test.error(F.Value.t, K.Check.infer_term(P.Global.initial, P.Rules.unit_val), "a section has no type of its own;  it needs an expected type"),
   Test.unit_ok(Test.check_as(P.Rules.unit_val, P.Rules.unit_ty(F.Level.one))),
   Test.eta, Test.proof_irrelevance, Test.budget_success, Test.budget_nested,
   Test.error(F.Value.t, K.Check.infer(C.Check.make(P.Global.initial, C.Budget.Steps{0n}), F.Quantity.Many{}, Test.lit(0n)), "the check budget is exhausted"),
   Test.error(F.Value.t, K.Check.infer(C.Check.make(P.Global.initial, C.Budget.Steps{1n}), F.Quantity.Many{}, Test.function_type(F.Quantity.Many{})), "the check budget is exhausted")]

def Test.finish(passed: Nat, failed: Nat) -> IO(Unit):
  match failed:
    case Zero{}:
      IO.print("KERNEL passed=" ++ F.Text.nat(passed) ++ " failed=0")
    case Succ{more}:
      IO.die(Unit, 1, "KERNEL failed=" ++ F.Text.nat(Succ{more}) ++ " passed=" ++ F.Text.nat(passed))

def Test.report(cases: List<&2, Bool>, +index: Nat, passed: Nat, failed: Nat) -> IO(Unit):
  match cases:
    case Nil{}:
      Test.finish(passed, failed)
    case Con{result, rest}:
      match result:
        case True{}:
          Test.report(rest, Succ{index}, Succ{passed}, failed)
        case False{}:
          do IO<Unit>:
            unit: Unit <- IO.print("FAIL kernel case " ++ F.Text.nat(index))
            Test.report(rest, Succ{index}, passed, Succ{failed})

def main() -> IO(Unit):
  Test.report(List.append(&2, Bool, Test.run, Test.checker), 1n, 0n, 0n)
