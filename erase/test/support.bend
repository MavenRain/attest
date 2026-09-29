import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel.bend as K
import ../../lib/kernel_eval.bend as V
import ../../lib/kernel_primitives.bend as G
import ../../lib/erasure.bend as R
import ../../surface/elab.bend as E
import ../opaque.bend as O
import ../inline.bend as I

def Test.semantics() -> R.Erase.Semantics:
  R.Erase.Semantics{ctx => term => K.Check.infer_univ_stateful(ctx,term),ctx => q => term => K.Check.infer_stateful(ctx,q,term),globals => size => value => V.Eval.quote(globals,size,value)}

def Test.require(condition:Bool,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  match condition:
    case True{}: Done{Unit{}}
    case False{}: Fail{F.Error.Mismatch{message}}

def Test.prepare(checked:E.Elab.checked) -> Result<&2,&2,F.Error.t,E.Elab.checked>:
  F.Pair2{globals,rows} = checked
  O.Opaque.prepare(~Test.semantics,C.Budget.unlimited,globals,rows)

def Test.prepared(source:String) -> Result<&2,&2,F.Error.t,E.Elab.checked>:
  R.Erase.bind(E.Elab.checked,E.Elab.checked,E.Elab.check_in(G.Global.initial,source),checked => Test.prepare(checked))

def Test.eval_global(+globals:F.Global.t,name:String) -> Result<&2,&2,F.Error.t,F.Value.t>:
  R.Erase.bind(F.Value.t,F.Value.t,V.Eval.eval(globals,Nil{},F.Term.Global{name}),value => V.Eval.whnf(globals,value))

def Test.neutral(value:F.Value.t) -> Bool:
  match value:
    case F.Value.VNeutral{head,spine}: True{}
    case other: False{}

def Test.neutral_global(value:F.Value.t,name:String) -> Bool:
  match value:
    case F.Value.VNeutral{F.Value.HGlobal{found},Nil{}}: String.eq(found,name)
    case other: False{}

def Test.some(-A:Data,value:Maybe<&2,A>) -> Bool:
  match value:
    case None{}: False{}
    case Some{x}: True{}

def Test.fails(-A:Data,value:Result<&2,&2,F.Error.t,A>,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  match value:
    case Fail{error}: Done{Unit{}}
    case Done{result}: Fail{F.Error.Mismatch{message}}

def Test.fails_with(-A:Data,value:Result<&2,&2,F.Error.t,A>,expected:String,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  match value:
    case Fail{error}: Test.require(String.eq(F.Error.message(error),expected),message)
    case Done{result}: Fail{F.Error.Mismatch{message}}

def Test.axiom(name:String,globals:F.Global.t) -> Bool:
  Test.some(F.Global.axiom_entry,F.Global.find_axiom(name,globals))

def Test.def_body(definition:F.Global.def_entry) -> F.Term.t:
  F.Global.DefEntry{ty,body,reducible,recursive,partial} = definition
  body

def Test.replace_body(definition:F.Global.def_entry,body:F.Term.t) -> F.Global.entry:
  F.Global.DefEntry{ty,old,reducible,recursive,partial} = definition
  F.Global.Def{F.Global.DefEntry{ty,body,reducible,recursive,partial}}

def Test.replace_type(definition:F.Global.def_entry,ty:F.Term.t) -> F.Global.entry:
  F.Global.DefEntry{old,body,reducible,recursive,partial} = definition
  F.Global.Def{F.Global.DefEntry{ty,body,reducible,recursive,partial}}

def Test.definition(+name:String,globals:F.Global.t) -> Result<&2,&2,F.Error.t,F.Global.def_entry>:
  R.Erase.require(F.Global.def_entry,F.Global.find_def(name,globals),F.Error.Mismatch{"missing definition " ++ name})

def Test.layout(globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  R.Erase.bind(F.Value.t,Unit,Test.eval_global(globals,"Layout"),value => Test.require(Test.neutral(value),"inline proof selected a layout"))

def Test.prefix(prefix:String,text:String) -> Bool:
  match prefix:
    case SNil{}: True{}
    case SCon{h,t}:
      match text:
        case SNil{}: False{}
        case SCon{x,xs}: Bool.and(Char.is_eq(h,x),Test.prefix(t,xs))

def Test.remove_rows(rows:List<&2,F.Pair2<String,F.Global.entry>>,+name:String) -> List<&2,F.Pair2<String,F.Global.entry>>:
  match rows:
    case Nil{}: Nil{}
    case F.Pair2{+found,entry} <> rest:
      +more:List<&2,F.Pair2<String,F.Global.entry>> = Test.remove_rows(rest,name)
      F.Data.choose(List<&2,F.Pair2<String,F.Global.entry>>,String.eq(found,name),more,F.Pair2{found,entry} <> more)

def Test.remove(+globals:F.Global.t,name:String) -> F.Global.t:
  F.Global.with_entries(Test.remove_rows(F.Global.entries(globals),name),globals)

def Test.count_ok(result:Result<&2,&2,F.Error.t,Unit>) -> Nat:
  match result:
    case Done{unit}: 1n
    case Fail{error}: 0n

def Test.status(passed:Bool) -> String:
  match passed:
    case True{}: "OK"
    case False{}: "FAIL"

def Test.exit(passed:Bool) -> IO(Unit):
  match passed:
    case True{}: IO.pure(Unit,Unit{})
    case False{}: IO.die(Unit,1,"")
