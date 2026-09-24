import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel_primitives.bend as G
import ../../lib/kernel_eval.bend as V
import ../../lib/erasure.bend as R
import ../../surface/elab.bend as E
import ../opaque.bend as O
import ../inline.bend as I
import ./support.bend as T

def OpaqueTest.inherited(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = prepared
  T.Test.require(T.Test.axiom("proof",globals),"inherited proof retained")

def OpaqueTest.guarded_prepared(original:E.Elab.checked,prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = original
  F.Pair2{+opaque,sealed} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- T.Test.require(T.Test.some(F.Global.def_entry,F.Global.find_def("proof",globals)),"source proof missing")
    b:Unit <- T.Test.require(T.Test.axiom("proof",opaque),"proof body retained")
    c:Unit <- T.Test.require(T.Test.some(F.Global.def_entry,F.Global.find_def("Layout",opaque)),"runtime type was sealed")
    d:Unit <- T.Test.require(T.Test.some(F.Positivity.family,F.Global.find_family("Equal",opaque)),"family table lost")
    e:Unit <- T.Test.require(Nat.is_eq(R.Erase.length(F.Pair2<String,F.Global.entry>,rows),R.Erase.length(F.Pair2<String,F.Global.entry>,sealed)),"declaration rows lost")
    value:F.Value.t <- T.Test.eval_global(opaque,"proof")
    f:Unit <- T.Test.require(T.Test.neutral_global(value,"proof"),"opaque evaluator unfolded proof")
    inherited:E.Elab.checked <- O.Opaque.prepare(~T.Test.semantics,C.Budget.unlimited,globals,Nil{})
    OpaqueTest.inherited(inherited)

def OpaqueTest.guarded(source:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    OpaqueTest.guarded_prepared(original,prepared)

def OpaqueTest.runtime_values(original:E.Elab.checked,prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = original
  F.Pair2{+opaque,sealed} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    before:F.Value.t <- T.Test.eval_global(globals,"value")
    after:F.Value.t <- T.Test.eval_global(opaque,"value")
    bt:F.Term.t <- V.Eval.quote(globals,0n,before)
    at:F.Term.t <- V.Eval.quote(opaque,0n,after)
    T.Test.require(I.Inline.term_equal(bt,at),"runtime computation changed")

def OpaqueTest.runtime() -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,"def value : Nat := 7")
    prepared:E.Elab.checked <- T.Test.prepare(original)
    OpaqueTest.runtime_values(original,prepared)

def OpaqueTest.classify(original:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = original
  do Result<&2,&2,F.Error.t,Unit>:
    definition:F.Global.def_entry <- T.Test.definition("proof",globals)
    T.Test.fails(E.Elab.checked,O.Opaque.prepare(~T.Test.semantics,C.Budget.unlimited,F.Global.add("proof",T.Test.replace_type(definition,F.Term.Global{"missing_type"}),globals),rows),"classification error was swallowed")

def OpaqueTest.isolate(globals:F.Global.t) -> F.Global.t:
  F.Global.with_entries(F.Global.entries(G.Global.initial),globals)

def OpaqueTest.body_value(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = prepared
  R.Erase.bind(F.Value.t,Unit,T.Test.eval_global(globals,"proof"),value => T.Test.require(T.Test.neutral_global(value,"proof"),"proof body evaluated"))

def OpaqueTest.body(original:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = original
  do Result<&2,&2,F.Error.t,Unit>:
    definition:F.Global.def_entry <- T.Test.definition("proof",globals)
    (+trap:F.Global.entry = T.Test.replace_body(definition,F.Term.Global{"missing_body"})
     R.Erase.bind(E.Elab.checked,Unit,O.Opaque.prepare(~T.Test.semantics,C.Budget.unlimited,F.Global.add("proof",trap,OpaqueTest.isolate(globals)),[F.Pair2{"proof",trap}]),prepared => OpaqueTest.body_value(prepared)))

def OpaqueTest.report(result:Result<&2,&2,F.Error.t,Unit>,name:String) -> IO(Unit):
  match result:
    case Done{unit}: IO.pure(Unit,Unit{})
    case Fail{error}: IO.print_err(name ++ ": " ++ F.Error.to_string(error))

def OpaqueTest.run(rows:List<&2,F.Pair2<String,Result<&2,&2,F.Error.t,Unit>>>,count:Nat) -> IO(Nat):
  match rows:
    case Nil{}: IO.pure(Nat,count)
    case F.Pair2{name,+result} <> rest:
      do IO<Nat>:
        reported:Unit <- OpaqueTest.report(result,name)
        OpaqueTest.run(rest,(count + T.Test.count_ok(result) : Nat))

def OpaqueTest.finish(+total:Nat,count:Nat) -> IO(Unit):
  +passed:Nat = count
  do IO<Unit>:
    wrote:Unit <- IO.print("OPAQUE-ERASE pass=" ++ F.Text.nat(passed) ++ " fail=" ++ F.Text.nat((total - passed : Nat)))
    T.Test.exit(Nat.is_eq(passed,total))

def OpaqueTest.f2_a() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef proof : Equal := refl\ndef Layout : Type 0 := case proof as p in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def OpaqueTest.proof_alias() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef proof : Equal := refl\ndef alias : Equal := proof\ndef Layout : Type 0 := case alias as p in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def OpaqueTest.proof_function() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef proof : (x : Nat) -> Equal := fun (x : Nat) => refl\ndef Layout : Type 0 := case (proof 3) as p in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def main() -> IO(Unit):
  +rows:List<&2,F.Pair2<String,Result<&2,&2,F.Error.t,Unit>>> = [
      F.Pair2{"global",OpaqueTest.guarded(OpaqueTest.f2_a)},
      F.Pair2{"alias",OpaqueTest.guarded(OpaqueTest.proof_alias)},
      F.Pair2{"function",OpaqueTest.guarded(OpaqueTest.proof_function)},
      F.Pair2{"runtime",OpaqueTest.runtime},
      F.Pair2{"classification",R.Erase.bind(E.Elab.checked,Unit,E.Elab.check_in(G.Global.initial,OpaqueTest.f2_a),checked => OpaqueTest.classify(checked))},
      F.Pair2{"body",R.Erase.bind(E.Elab.checked,Unit,E.Elab.check_in(G.Global.initial,OpaqueTest.f2_a),checked => OpaqueTest.body(checked))}]
  do IO<Unit>:
    count:Nat <- OpaqueTest.run(rows,0n)
    OpaqueTest.finish(List.length(&2,F.Pair2<String,Result<&2,&2,F.Error.t,Unit>>,rows),count)
