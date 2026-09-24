import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel_primitives.bend as G
import ../../lib/erasure.bend as R
import ../../surface/elab.bend as E
import ../opaque.bend as O
import ../inline.bend as I
import ./support.bend as T

def BudgetTest.spent(-A:Data,result:F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>) -> Result<&2,&2,F.Error.t,Nat>:
  match result:
    case F.Pair2{Done{value},C.Budget.Steps{remaining}}: Done{(1000n - remaining : Nat)}
    case F.Pair2{Fail{error},budget}: Fail{error}
    case F.Pair2{Done{value},C.Budget.Unlimited{}}: Fail{F.Error.Mismatch{"finite budget became unlimited"}}

def BudgetTest.exhausted(-A:Data,result:F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>) -> Bool:
  match result:
    case F.Pair2{Fail{error},C.Budget.Steps{0n}}: True{}
    case other: False{}

def BudgetTest.exact(-A:Data,result:F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>) -> Bool:
  match result:
    case F.Pair2{Done{value},C.Budget.Steps{0n}}: True{}
    case other: False{}

def BudgetTest.first(rows:List<&2,F.Pair2<String,F.Global.entry>>) -> Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,F.Global.entry>>>:
  match rows:
    case first <> rest: Done{[first]}
    case Nil{}: Fail{F.Error.Mismatch{"budget fixture has no rows"}}

def BudgetTest.classifier_result(result:F.Pair2<Result<&2,&2,F.Error.t,Maybe<&2,F.Term.t>>,C.Budget.t>) -> Bool:
  match result:
    case F.Pair2{Done{None{}},C.Budget.Steps{remaining}}: Bool.not(Nat.is_eq(remaining,10n))
    case other: False{}

def BudgetTest.swallowed() -> Bool:
  +checker:C.Check.ctx = C.Check.make(G.Global.initial,C.Budget.Steps{10n})
  BudgetTest.classifier_result(R.Erase.State.execute(Maybe<&2,F.Term.t>,I.Inline.inferred_type_state(~T.Test.semantics,R.Erase.semantic_infer_state(T.Test.semantics,checker,F.Quantity.Zero{},F.Term.Sec{F.Shape.SColl{0n},Nil{}}),checker),C.Budget.Steps{10n}))

def BudgetTest.run(checked:E.Elab.checked) -> Result<&2,&2,F.Error.t,F.Pair2<List<&2,Bool>,String>>:
  F.Pair2{+globals,+rows} = checked
  do Result<&2,&2,F.Error.t,F.Pair2<List<&2,Bool>,String>>:
    +one:List<&2,F.Pair2<String,F.Global.entry>> <- BudgetTest.first(rows)
    +single:Nat <- BudgetTest.spent(List<&2,F.Pair2<String,R.Erase.entry>>,R.Erase.program_stateful(~T.Test.semantics,C.Budget.Steps{1000n},globals,one))
    +double:Nat <- BudgetTest.spent(List<&2,F.Pair2<String,R.Erase.entry>>,R.Erase.program_stateful(~T.Test.semantics,C.Budget.Steps{1000n},globals,rows))
    +prepare:Nat <- BudgetTest.spent(E.Elab.checked,O.Opaque.prepare_stateful(~T.Test.semantics,C.Budget.Steps{1000n},globals,rows))
    +opaque:Nat <- BudgetTest.spent(List<&2,F.Pair2<String,R.Erase.entry>>,O.Opaque.program_stateful(~T.Test.semantics,C.Budget.Steps{1000n},globals,rows))
    +inline:Nat <- BudgetTest.spent(E.Elab.checked,I.Inline.prepare_stateful(~T.Test.semantics,C.Check.make(globals,C.Budget.Steps{1000n}),globals,rows))
    Done{F.Pair2{[
      # Original shared Budget.of_poll counts for this fixture are 2,4,4,8,2.
      Bool.and(Nat.is_eq(single,2n),Bool.and(Nat.is_eq(prepare,4n),Nat.is_eq(inline,2n))),
      Nat.is_eq(double,(single + single : Nat)),
      BudgetTest.exact(List<&2,F.Pair2<String,R.Erase.entry>>,R.Erase.program_stateful(~T.Test.semantics,C.Budget.Steps{single},globals,one)),
      BudgetTest.exhausted(List<&2,F.Pair2<String,R.Erase.entry>>,R.Erase.program_stateful(~T.Test.semantics,C.Budget.Steps{(single - 1n : Nat)},globals,one)),
      BudgetTest.exhausted(List<&2,F.Pair2<String,R.Erase.entry>>,R.Erase.program_stateful(~T.Test.semantics,C.Budget.Steps{single},globals,rows)),
      Nat.is_eq(opaque,(prepare + double : Nat)),
      BudgetTest.exhausted(List<&2,F.Pair2<String,R.Erase.entry>>,O.Opaque.program_stateful(~T.Test.semantics,C.Budget.Steps{prepare},globals,rows)),
      BudgetTest.exhausted(E.Elab.checked,I.Inline.prepare_stateful(~T.Test.semantics,C.Check.make(globals,C.Budget.Steps{(inline - 1n : Nat)}),globals,rows)),
      BudgetTest.exact(List<&2,F.Pair2<String,R.Erase.entry>>,R.Erase.program_stateful(~T.Test.semantics,C.Budget.Steps{0n},globals,Nil{})),
      BudgetTest.swallowed],
      "ERASURE-BUDGET single=" ++ F.Text.nat(single) ++ " double=" ++ F.Text.nat(double) ++ " prepare=" ++ F.Text.nat(prepare) ++ " opaque=" ++ F.Text.nat(opaque) ++ " inline=" ++ F.Text.nat(inline)}}

def BudgetTest.count(rows:List<&2,Bool>) -> Nat:
  match rows:
    case Nil{}: 0n
    case True{} <> rest: 1n+BudgetTest.count(rest)
    case False{} <> rest: BudgetTest.count(rest)

def BudgetTest.finish(result:Result<&2,&2,F.Error.t,F.Pair2<List<&2,Bool>,String>>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit,1,F.Error.to_string(error))
    case Done{F.Pair2{tests,report}}:
      +passed:Nat = BudgetTest.count(tests)
      do IO<Unit>:
        a:Unit <- IO.print(report)
        b:Unit <- IO.print("ERASURE-BUDGET pass=" ++ F.Text.nat(passed) ++ " total=10")
        T.Test.exit(Nat.is_eq(passed,10n))

def main() -> IO(Unit):
  BudgetTest.finish(R.Erase.bind(E.Elab.checked,F.Pair2<List<&2,Bool>,String>,E.Elab.check_in(G.Global.initial,"def a : Nat := 7\ndef b : Nat := 8"),checked => BudgetTest.run(checked)))
