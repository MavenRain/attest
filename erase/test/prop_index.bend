import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_primitives.bend as G
import ../../surface/elab.bend as E

type Prop.case is Data:
  Prop.Case{name:String,source:String,refusal:Maybe<&2,String>}

def Prop.prefix(prefix:String,text:String) -> Bool:
  match prefix:
    case SNil{}: True{}
    case SCon{h,t}:
      match text:
        case SNil{}: False{}
        case SCon{x,xs}: Bool.and(Char.is_eq(h,x),Prop.prefix(t,xs))

def Prop.verdict(expected:Maybe<&2,String>,result:Result<&2,&2,F.Error.t,E.Elab.checked>) -> F.Pair2<Bool,String>:
  match expected result:
    case None{} Done{checked}: F.Pair2{True{},"accepted"}
    case None{} Fail{error}: F.Pair2{False{},F.Error.to_string(error)}
    case Some{prefix} Done{checked}: F.Pair2{False{},"unexpected acceptance"}
    case Some{prefix} Fail{error}:
      +detail:String = F.Error.to_string(error)
      F.Pair2{Prop.prefix(prefix,detail),detail}

def Prop.status(passed:Bool) -> String:
  match passed:
    case True{}: "OK"
    case False{}: "FAIL"

def Prop.count(passed:Bool) -> Nat:
  match passed:
    case True{}: 1n
    case False{}: 0n

def Prop.add(verdict:F.Pair2<Bool,String>,name:String,rest:F.Pair2<Nat,String>) -> F.Pair2<Nat,String>:
  F.Pair2{+passed,detail} = verdict
  F.Pair2{count,report} = rest
  F.Pair2{(Prop.count(passed) + count : Nat),"PROP-INDEX row=" ++ name ++ " " ++ Prop.status(passed) ++ " " ++ detail ++ "\n" ++ report}

def Prop.run(cases:List<&2,Prop.case>) -> F.Pair2<Nat,String>:
  match cases:
    case Nil{}: F.Pair2{0n,""}
    case Prop.Case{name,source,expected} <> rest:
      Prop.add(Prop.verdict(expected,E.Elab.check_in(G.Global.initial,source)),name,Prop.run(rest))

def Prop.cases() -> List<&2,Prop.case>:
  [
    Prop.Case{"nat-index","mu At : (0 n : Nat) -> Prop with\n| at : (0 n : Nat) -> At n\ndef witness : At 4 := at 4",None{}},
    Prop.Case{"high-universe-index","mu At : (0 A : Type 1) -> Prop with\n| at : (0 A : Type 1) -> At A\ndef witness : At (Type 0) := at (Type 0)",None{}},
    Prop.Case{"dependent-indices","mu At : (0 A : Type 0) -> (0 x : A) -> Prop with\n| at : (0 A : Type 0) -> (0 x : A) -> At A x\ndef witness : At Nat 4 := at Nat 4",None{}},
    Prop.Case{"reordered-indices","mu At : (0 n : Nat) -> (0 m : Nat) -> Prop with\n| at : (0 n : Nat) -> (0 m : Nat) -> At m n\ndef witness : At 3 4 := at 4 3",None{}},
    Prop.Case{"annotated-index","mu At : (0 n : Nat) -> Prop with\n| at : (0 n : Nat) -> At (n : Nat)\ndef witness : At 4 := at 4",None{}},
    Prop.Case{"accessibility-family","axiom R : Nat -> Nat -> Prop\nmu Acc : (0 x : Nat) -> Prop with\n| intro : (0 x : Nat) -> (0 next : (0 y : Nat) -> R y x -> Acc y) -> Acc x\naxiom next : (0 y : Nat) -> R y 0 -> Acc y\ndef accessible : Acc 0 := intro 0 next",None{}},
    Prop.Case{"indexed-singleton-elimination","mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At n\ndef step : (p : At 4) -> Nat := fun (p : At 4) =>\ncase p as q in At n return Nat with | at 0 n => 0",None{}},
    Prop.Case{"erased-index-read","mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At n\ndef step : (p : At 4) -> Nat := fun (p : At 4) =>\ncase p as q in At n return Nat with | at 0 n => n",Some{"quantity: the erased binder n is read in a runtime position"}},
    Prop.Case{"annotated-index-type","mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At (n : Type 0)",Some{"mismatch: the term has type Nat and the expected type is Type 1"}},
    Prop.Case{"result-index-type","mu At : (0 A : Type 0) -> Prop with | at : (0 n : Nat) -> At n",Some{"mismatch: the term has type Nat and the expected type is Type 1"}},
    Prop.Case{"runtime-index","mu At : (n : Nat) -> Prop with | at : At 0",Some{"index not zero:"}},
    Prop.Case{"type-index-bound","mu At : (0 A : Type 0) -> Type 0 with | at : At Nat",Some{"index above universe:"}},
    Prop.Case{"type-field-bound","mu Box : Type 0 with | box : (0 A : Type 0) -> Box",Some{"universe: a field of box exceeds its family universe"}},
    Prop.Case{"unindexed-proof-field","mu Box : Prop with | box : (0 n : Nat) -> Box",Some{"universe: a field of box exceeds its family universe"}},
    Prop.Case{"runtime-proof-field","mu At : (0 n : Nat) -> Prop with | at : (n : Nat) -> At n",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"constant-result-index","mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At 0",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"computed-result-index","mu At : (0 n : Nat) -> Prop with\n| at : (0 n : Nat) -> At (let m : Nat := n in m)",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"unindexed-first-field","mu At : (0 n : Nat) -> Prop with\n| at : (0 hidden : Nat) -> (0 n : Nat) -> At n",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"unindexed-last-field","mu At : (0 n : Nat) -> Prop with\n| at : (0 n : Nat) -> (0 hidden : Nat) -> At n",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"ill-typed-index","mu At : (0 n : 0) -> Prop with | at : At 0",Some{"universe: a term used as a type is not a universe"}},
    Prop.Case{"index-twice","mu At : (0 n : Nat) -> (0 m : Nat) -> Prop with\n| at : (0 n : Nat) -> At n n",None{}},
    Prop.Case{"index-in-later-field","axiom P : Nat -> Prop\nmu At : (0 n : Nat) -> Prop with\n| at : (0 n : Nat) -> (0 p : P n) -> At n",None{}},
    Prop.Case{"prop-typed-index","axiom P : Prop\nmu At : (0 p : P) -> Prop with\n| at : (0 p : P) -> At p",None{}},
    Prop.Case{"parameter-index","mu At (0 A : Type 0) : (0 x : A) -> Prop with\n| at : (0 x : A) -> At A x",None{}},
    Prop.Case{"computed-application-index","axiom f : Nat -> Nat\nmu At : (0 n : Nat) -> Prop with\n| at : (0 n : Nat) -> At (f n)",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"type-1-index-bound","mu At : (0 A : Type 1) -> Type 1 with | at : At Nat",Some{"index above universe: the index A of At lives at 3 and At is declared at 2"}},
    Prop.Case{"parameter-hidden-field","mu At (0 A : Type 0) : (0 x : A) -> Prop with\n| at : (0 hidden : A) -> (0 x : A) -> At A x",Some{"universe: a field of at exceeds its family universe"}},
    Prop.Case{"recursive-big-later-field","axiom R : Nat -> Nat -> Prop\nmu Acc : (0 x : Nat) -> Prop with\n| intro : (0 x : Nat) -> (0 next : (0 y : Nat) -> R y x -> Acc y) -> (0 big : Nat) -> Acc x",Some{"universe: a field of intro exceeds its family universe"}}
  ]

def Prop.exit(passed:Bool) -> IO(Unit):
  match passed:
    case True{}: IO.pure(Unit,Unit{})
    case False{}: IO.die(Unit,1,"")

def Prop.finish(+total:Nat,result:F.Pair2<Nat,String>) -> IO(Unit):
  F.Pair2{+count,report} = result
  +passed:Bool = Nat.is_eq(count,total)
  do IO<Unit>:
    wrote:Unit <- IO.write(report ++ "PROP-INDEX pass=" ++ F.Text.nat(count) ++ " total=" ++ F.Text.nat(total) ++ " " ++ Prop.status(passed) ++ "\n")
    Prop.exit(passed)

def main() -> IO(Unit):
  Prop.finish(List.length(&2,Prop.case,Prop.cases),Prop.run(Prop.cases))
