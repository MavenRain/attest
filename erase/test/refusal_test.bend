import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel_primitives.bend as G
import ../../lib/erasure.bend as R
import ./support.bend as T

# These deliberately malformed core trees exercise the eraser's own guards.
# The frontend rejects most such trees before erasure, so source-only tests
# cannot cover these branches.
def Refusal.result(result:Result<&2,&2,F.Error.t,F.Pair2<R.Eterm.ktm,R.Erase.acc>>,expected:F.Error.t) -> Bool:
  match result:
    case Done{value}: False{}
    case Fail{error}: String.eq(F.Error.to_string(error),F.Error.to_string(expected))

def Refusal.check(term:F.Term.t,expected:F.Error.t) -> Bool:
  Refusal.result(R.Erase.term(~T.Test.semantics,R.Erase.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{},"refusal"},R.Erase.Acc{0n,Nil{},Nil{}},False{},Some{F.Value.VNeutral{F.Value.HGlobal{"Nat"},Nil{}}},term),expected)

def Refusal.cases() -> List<&2,Bool>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +point:F.Shape.t<F.Term.t> = F.Shape.SPi{F.Quantity.Many{},"x",univ}
  [Refusal.check(F.Term.Var{0n},F.Error.Unbound{"the erasure context has no binder at index 0"}),
   Refusal.check(F.Term.Auto{},F.Error.Not_yet{"instances arrive at M2"}),
   Refusal.check(F.Term.Sec{F.Shape.SPar{univ,univ},Nil{}},F.Error.Not_yet{"SPar arrives at M1"}),
   Refusal.check(F.Term.Sec{F.Shape.SMu{"Missing",Nil{}},Nil{}},F.Error.Not_yet{"a right former at a mu shape arrives at M2"}),
   Refusal.check(F.Term.Sec{F.Shape.SNu{"Missing",Nil{}},Nil{}},F.Error.Not_yet{"SNu arrives at M2"}),
   Refusal.check(F.Term.Sec{F.Shape.SColl{0n},Nil{}},F.Error.Mismatch{"a tuple stands at a type that is not a right former"}),
   Refusal.check(F.Term.In{point,F.Term.APt{F.Quantity.Many{},univ},Nil{}},F.Error.Mismatch{"an introduction stands at a type that is not a left former"}),
   Refusal.check(F.Term.In{F.Shape.SMu{"Missing",Nil{}},F.Term.ACtor{"missing"},Nil{}},F.Error.Mismatch{"an introduction stands at a type that is not a left former"}),
   Refusal.check(F.Term.Out{point,F.Term.ALeg{0n},univ},F.Error.Mismatch{"an application at a point shape with no point address"}),
   Refusal.check(F.Term.Out{F.Shape.SColl{0n},F.Term.APt{F.Quantity.Many{},univ},univ},F.Error.Mismatch{"a projection takes a leg address"}),
   Refusal.check(F.Term.Out{F.Shape.SColl{1n},F.Term.ALeg{0n},univ},F.Error.Mismatch{"a projection stands on a value that is not a right former"}),
   Refusal.check(F.Term.Elim{F.Term.Elimination{F.Shape.SColl{0n},univ,F.Quantity.Many{},None{},Nil{}}},F.Error.Mismatch{"an elimination stands on a value that is not a left former"}),
   Refusal.check(F.Term.Let{"x",F.Term.Global{"missing_type"},univ,univ},F.Error.Unbound{"missing_type"})]

def Refusal.count(cases:List<&2,Bool>) -> Nat:
  match cases:
    case Nil{}: 0n
    case True{} <> rest: 1n+Refusal.count(rest)
    case False{} <> rest: Refusal.count(rest)

def main() -> IO(Unit):
  +passed:Nat = Refusal.count(Refusal.cases)
  do IO<Unit>:
    wrote:Unit <- IO.print("ERASURE-REFUSAL pass=" ++ F.Text.nat(passed) ++ " total=13")
    T.Test.exit(Nat.is_eq(passed,13n))
