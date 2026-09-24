import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel_eval.bend as E
import ../../lib/kernel_primitives.bend as P
import ../../lib/erasure.bend as R

def universe_name(prop: Bool, runtime: Bool, name: String) -> Result<&2, &2, F.Error.t, F.Level.t>:
  match prop:
    case True{}: Done{F.Level.zero}
    case False{}:
      match runtime:
        case True{}: Done{F.Level.succ(F.Level.zero)}
        case False{}: Fail{F.Error.Unbound{name}}

def universe(checker: C.Check.ctx, ty: F.Term.t) -> Result<&2, &2, F.Error.t, F.Level.t>:
  match ty:
    case F.Term.Global{+name}: universe_name(String.eq(name, "P"), String.eq(name, "Nat"), name)
    case F.Term.Univ{level}: Done{F.Level.succ(level)}
    case other: Fail{F.Error.Cannot_infer{"outside representation fixture"}}

def inference(checker: C.Check.ctx, quantity: F.Quantity.t, term: F.Term.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  Fail{F.Error.Cannot_infer{"representation fixture does not infer terms"}}

def semantics() -> R.Erase.Semantics:
  R.Erase.Semantics{+checker => term => F.Pair2{universe(checker,term),C.Check.budget(checker)}, +checker => quantity => term => F.Pair2{inference(checker,quantity,term),C.Check.budget(checker)}, E.Eval.quote}

def check_repr(result: Result<&2, &2, F.Error.t, R.Eterm.repr>, expected: String) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{repr}: String.eq(R.Eterm.print_repr(repr), expected)

def check_runtime(result: Result<&2, &2, F.Error.t, Bool>, expected: Bool) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{value}: Bool.not(Bool.xor(value, expected))

def main() -> List<&2, Bool>:
  +globals = F.Global.add("Nat", F.Global.Axiom{F.Global.AxiomEntry{F.Term.Univ{F.Level.succ(F.Level.zero)}}}, F.Global.add("P", F.Global.Axiom{F.Global.AxiomEntry{F.Term.Univ{F.Level.zero}}}, F.Global.empty))
  +ec : R.Erase.ectx = R.Erase.Context{C.Check.make(globals, C.Budget.unlimited), Nil{}, "test"}
  +nat : F.Value.t = F.Value.VNeutral{F.Value.HGlobal{"Nat"}, Nil{}}
  +proof : F.Value.t = F.Value.VNeutral{F.Value.HGlobal{"P"}, Nil{}}
  +cod : F.Value.closure = F.Value.Closure{Nil{}, F.Term.Global{"Nat"}}
  +diagram : F.Value.closure = F.Value.Closure{Nil{}, P.Rules.diagram_of([F.Term.Global{"P"}, F.Term.Global{"Nat"}])}
  [check_repr(R.Erase.repr_of(~semantics, ec, nat), "union nat"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VRan{F.Shape.SPi{F.Quantity.Many{}, "n", nat}, cod, None{}}), "func fn<1>"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VRan{F.Shape.SPi{F.Quantity.Zero{}, "n", nat}, cod, None{}}), "func fn<0>"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VRan{F.Shape.SColl{2n}, diagram, None{}}), "struct tuple<union nat>"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VLan{F.Shape.SColl{2n}, diagram, None{}}), "union sum<unit|union nat>"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VLan{F.Shape.SPi{F.Quantity.Zero{}, "n", nat}, cod, None{}}), "struct pair<union nat>"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VLan{F.Shape.SPi{F.Quantity.Many{}, "p", proof}, cod, None{}}), "struct pair<union nat>"),
   check_repr(R.Erase.repr_of(~semantics, ec, F.Value.VLan{F.Shape.SMu{"Family", [nat]}, cod, None{}}), "union mu<Family>"),
   check_runtime(R.Erase.runtime_ty(~semantics, ec, nat), True{}),
   check_runtime(R.Erase.runtime_ty(~semantics, ec, proof), False{}),
   check_runtime(R.Erase.runtime_ty(~semantics, ec, F.Value.VUniv{F.Level.zero}), False{}),
   check_runtime(R.Erase.runtime_ty(~semantics, ec, F.Value.VLan{F.Shape.SColl{0n}, cod, None{}}), False{})]
