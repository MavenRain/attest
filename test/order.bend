import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_order.bend as O

def Test.n() -> F.Term.t:
  F.Term.Global{"N"}

def Test.arrow() -> F.Shape.t<F.Term.t>:
  F.Shape.SPi{F.Quantity.Many{}, "n", Test.n}

def Test.lambda(body: F.Term.t) -> F.Term.t:
  F.Term.Sec{Test.arrow, [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "n"}], body}]}

def Test.call(name: String, arg: F.Term.t) -> F.Term.t:
  F.Term.Out{Test.arrow, F.Term.APt{F.Quantity.Many{}, arg}, F.Term.Global{name}}

def Test.motive() -> Maybe<&2, F.Term.motive>:
  Some{F.Term.Motive{Some{"N"}, [], "x", Test.n}}

def Test.elim(scrutinee: F.Term.t, motive: Maybe<&2, F.Term.motive>, key: F.Term.addr, body: F.Term.t) -> F.Term.t:
  F.Term.Elim{F.Term.Elimination{F.Shape.SMu{"N", []}, scrutinee, F.Quantity.Many{}, motive,
    [F.Pair2{key, F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "m"}], body}}]}}

def Test.guarded(name: String, arg: F.Term.t) -> F.Term.t:
  Test.lambda(Test.elim(F.Term.Var{0n}, Test.motive, F.Term.ACtor{"succ"}, Test.call(name, arg)))

def Test.cert_arg(expected: Nat, cert: Maybe<&2, O.Order.t>) -> Bool:
  match cert:
    case None{}:
      False{}
    case Some{value}:
      O.Order.Certificate{group, argument, rows} = value
      Nat.is_eq(argument, expected)

def Test.certified(expected: Nat, answer: Result<&2, &2, F.Error.t, Maybe<&2, O.Order.t>>) -> Bool:
  match answer:
    case Fail{error}:
      False{}
    case Done{cert}:
      Test.cert_arg(expected, cert)

def Test.refused(expected: String, answer: Result<&2, &2, F.Error.t, Maybe<&2, O.Order.t>>) -> Bool:
  match answer:
    case Fail{error}:
      String.eq(F.Error.message(error), expected)
    case Done{cert}:
      False{}

def Test.nonrecursive(answer: Result<&2, &2, F.Error.t, Maybe<&2, O.Order.t>>) -> Bool:
  match answer:
    case Fail{error}:
      False{}
    case Done{cert}:
      match cert:
        case None{}:
          True{}
        case Some{value}:
          False{}

def Test.good(-A: Data, answer: Result<&2, &2, F.Error.t, A>) -> Bool:
  match answer:
    case Fail{error}:
      False{}
    case Done{value}:
      True{}

def Test.bad(-A: Data, expected: String, answer: Result<&2, &2, F.Error.t, A>) -> Bool:
  match answer:
    case Fail{error}:
      String.eq(F.Error.message(error), expected)
    case Done{value}:
      False{}

def Test.budget_left(expected: Nat, budget: C.Budget.t) -> Bool:
  match budget:
    case C.Budget.Unlimited{}:
      False{}
    case C.Budget.Steps{remaining}:
      Nat.is_eq(expected, remaining)

def Test.spent(expected: Nat, answer: F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>) -> Bool:
  F.Pair2{result, budget} = answer
  Bool.and(Test.good(Unit, result), Test.budget_left(expected, budget))

def Test.exhausted(answer: F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>) -> Bool:
  F.Pair2{result, budget} = answer
  Bool.and(Test.bad(Unit, O.Totality.budget_msg, result), Test.budget_left(0n, budget))

def Test.order_error() -> String:
  "recursive definition self failed the structural termination guard"

def Test.cert() -> O.Order.t:
  O.Order.Certificate{["self"], 0n, [O.Order.Row{"self", [O.Order.Call{"self", [O.Order.Step{0n, Some{"succ"}}]}]}]}

def Test.family() -> F.Term.t:
  F.Term.Lan{F.Shape.SMu{"N", []}, F.Term.Univ{F.Level.zero}}

def Test.budget_tree() -> F.Term.t:
  F.Term.Elim{F.Term.Elimination{F.Shape.SMu{"N", [F.Term.Global{"I"}]}, F.Term.Var{0n}, F.Quantity.Many{}, Test.motive,
    [F.Pair2{F.Term.APt{F.Quantity.Many{}, F.Term.Var{0n}}, F.Term.Leg{[], F.Term.Var{0n}}}]}}

def Test.call_head(head: F.Term.t, arg: F.Term.t) -> F.Term.t:
  F.Term.Out{Test.arrow, F.Term.APt{F.Quantity.Many{}, arg}, head}

def Test.second_argument() -> F.Term.t:
  Test.lambda(Test.lambda(Test.elim(F.Term.Var{0n}, Test.motive, F.Term.ACtor{"succ"},
    Test.call_head(Test.call("self", F.Term.Var{2n}), F.Term.Var{0n}))))

def Test.results() -> List<&2, F.Pair2<String, Bool>>:
  [F.Pair2{"no group call", Test.nonrecursive(O.Order.certify([F.Pair2{"self", F.Term.Global{"other"}}]))},
   F.Pair2{"bare self refused", Test.refused(Test.order_error, O.Order.certify([F.Pair2{"self", F.Term.Global{"self"}}]))},
   F.Pair2{"guarded self", Test.certified(0n, O.Order.certify([F.Pair2{"self", Test.guarded("self", F.Term.Var{0n})}]))},
   F.Pair2{"principal is not smaller", Test.refused(Test.order_error, O.Order.certify([F.Pair2{"self", Test.lambda(Test.call("self", F.Term.Var{0n}))}]))},
   F.Pair2{"outer argument is not smaller", Test.refused(Test.order_error, O.Order.certify([F.Pair2{"self", Test.guarded("self", F.Term.Var{1n})}]))},
   F.Pair2{"nonvariable argument refused", Test.refused(Test.order_error, O.Order.certify([F.Pair2{"self", Test.guarded("self", F.Term.Global{"zero"})}]))},
   F.Pair2{"mutual descent", Test.certified(0n, O.Order.certify([F.Pair2{"self", Test.guarded("other", F.Term.Var{0n})}, F.Pair2{"other", Test.guarded("self", F.Term.Var{0n})}]))},
   F.Pair2{"nonrecursive helper does not constrain bound", Test.certified(0n, O.Order.certify([F.Pair2{"self", Test.guarded("self", F.Term.Var{0n})}, F.Pair2{"helper", Test.n}]))},
   F.Pair2{"second formal", Test.certified(1n, O.Order.certify([F.Pair2{"self", Test.second_argument}]))},
   F.Pair2{"translation succeeds", Test.good(F.Term.t, O.Order.translate(Test.cert, Test.guarded("self", F.Term.Var{0n})))},
   F.Pair2{"translation skips helper", Test.good(F.Term.t, O.Order.translate(Test.cert, Test.n))},
   F.Pair2{"translation requires head elimination", Test.bad(F.Term.t, O.Order.one_elim_msg, O.Order.translate(Test.cert, Test.lambda(Test.call("self", F.Term.Var{0n}))))},
   F.Pair2{"translation requires motive", Test.bad(F.Term.t, O.Order.motive_msg, O.Order.translate(Test.cert, Test.lambda(Test.elim(F.Term.Var{0n}, None{}, F.Term.ACtor{"succ"}, Test.call("self", F.Term.Var{0n})))))},
   F.Pair2{"translation requires constructor key", Test.bad(F.Term.t, O.Order.ctor_key_msg, O.Order.translate(Test.cert, Test.lambda(Test.elim(F.Term.Var{0n}, Test.motive, F.Term.ALeg{0n}, Test.call("self", F.Term.Var{0n})))))},
   F.Pair2{"name scan excludes families", Bool.not(O.Term.exists_name(False{}, ["N"], Test.family))},
   F.Pair2{"name scan includes families", O.Term.exists_name(True{}, ["N"], Test.family)},
   F.Pair2{"name scan includes point argument", O.Term.exists_name(False{}, ["target"], Test.call("other", F.Term.Global{"target"}))},
   F.Pair2{"name scan includes motive", O.Term.exists_name(False{}, ["N"], Test.elim(F.Term.Var{0n}, Test.motive, F.Term.ACtor{"succ"}, F.Term.Var{0n}))},
   F.Pair2{"positive family", Test.good(Unit, O.Positivity.positive(["N"], Test.family))},
   F.Pair2{"positive codomain", Test.good(Unit, O.Positivity.positive(["N"], F.Term.Ran{F.Shape.SPi{F.Quantity.Many{}, "x", F.Term.Global{"Bool"}}, Test.family}))},
   F.Pair2{"negative domain", Test.bad(Unit, O.Positivity.nonpositive_word, O.Positivity.positive(["N"], F.Term.Ran{Test.arrow, F.Term.Global{"Bool"}}))},
   F.Pair2{"family indices are absent", Test.bad(Unit, O.Positivity.nonpositive_word, O.Positivity.positive(["N"], F.Term.Lan{F.Shape.SMu{"N", [F.Term.Global{"N"}]}, F.Term.Univ{F.Level.zero}}))},
   F.Pair2{"nested inductive refused", Test.bad(Unit, O.Positivity.nonpositive_word, O.Positivity.positive(["N"], F.Term.Lan{F.Shape.SMu{"List", [Test.family]}, F.Term.Univ{F.Level.zero}}))},
   F.Pair2{"projection argument absent", Test.bad(Unit, O.Positivity.nonpositive_word, O.Positivity.positive(["N"], Test.call("Fn", Test.family)))},
   F.Pair2{"self recursion includes shape name", O.Positivity.self_rec(["N"], [F.Triple3{F.Quantity.Many{}, "x", Test.family}])},
   F.Pair2{"zero budget refuses first node", Test.exhausted(O.Totality.spend(C.Budget.Steps{0n}, Test.n))},
   F.Pair2{"one node exact budget", Test.spent(0n, O.Totality.spend(C.Budget.Steps{1n}, Test.n))},
   F.Pair2{"one node remainder", Test.spent(2n, O.Totality.spend(C.Budget.Steps{3n}, Test.n))},
   F.Pair2{"annotation counts three", Test.spent(0n, O.Totality.spend(C.Budget.Steps{3n}, F.Term.Ann{Test.n, F.Term.Univ{F.Level.zero}}))},
   F.Pair2{"annotation exact cutoff", Test.exhausted(O.Totality.spend(C.Budget.Steps{2n}, F.Term.Ann{Test.n, F.Term.Univ{F.Level.zero}}))},
   F.Pair2{"elimination counts six", Test.spent(0n, O.Totality.spend(C.Budget.Steps{6n}, Test.budget_tree))},
   F.Pair2{"elimination exact cutoff", Test.exhausted(O.Totality.spend(C.Budget.Steps{5n}, Test.budget_tree))}]

def Test.finish(passed: Nat, failed: Nat) -> IO(Unit):
  match failed:
    case Zero{}:
      IO.print("ORDER pass=" ++ F.Text.nat(passed) ++ " fail=0")
    case Succ{rest}:
      IO.die(Unit, 1, "ORDER failed")

def Test.run(cases: List<&2, F.Pair2<String, Bool>>, passed: Nat, failed: Nat) -> IO(Unit):
  match cases:
    case Nil{}:
      Test.finish(passed, failed)
    case Con{row, rest}:
      F.Pair2{name, result} = row
      match result:
        case True{}:
          Test.run(rest, Succ{passed}, failed)
        case False{}:
          do IO<Unit>:
            unit: Unit <- IO.print("FAIL " ++ name)
            Test.run(rest, passed, Succ{failed})

def main() -> IO(Unit):
  Test.run(Test.results, 0n, 0n)
