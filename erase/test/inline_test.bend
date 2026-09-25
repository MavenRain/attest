import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel.bend as K
import ../../lib/kernel_primitives.bend as G
import ../../lib/kernel_eval.bend as V
import ../../lib/erasure.bend as R
import ../../surface/elab.bend as E
import ../opaque.bend as O
import ../inline.bend as I
import ./support.bend as T
import ./fixtures.bend as X
import ./branch_fixtures.bend as B

def Suite.postulate(index:Nat) -> String:
  "__attest_inline_proof_" ++ F.Text.nat(index)

def Suite.is_generated(name:String) -> Bool:
  T.Test.prefix("__attest_inline_proof_",name)

def Suite.family_found(found:Maybe<&2,String>,name:String) -> Bool:
  match found:
    case None{}: False{}
    case Some{value}: String.eq(value,name)

def Suite.family_name(shape:F.Shape.t<F.Term.t>,name:String) -> Bool:
  Suite.family_found(F.Shape.family(F.Term.t,shape),name)

def Suite.name_here(term:F.Term.t,name:String) -> Bool:
  match term:
    case F.Term.Global{found}: String.eq(found,name)
    case F.Term.Lan{shape,diagram}: Suite.family_name(shape,name)
    case F.Term.Ran{shape,diagram}: Suite.family_name(shape,name)
    case F.Term.Sec{shape,legs}: Suite.family_name(shape,name)
    case F.Term.In{shape,address,args}: Suite.family_name(shape,name)
    case F.Term.Out{shape,address,head}: Suite.family_name(shape,name)
    case F.Term.Elim{F.Term.Elimination{shape,scrut,q,motive,branches}}: Suite.family_name(shape,name)
    case other: False{}

@unsafe
def Suite.names(tasks:List<&2,F.Pair2<Nat,F.Term.t>>,+name:String) -> Bool:
  match tasks:
    case Nil{}: False{}
    case F.Pair2{depth,+term} <> rest:
      Bool.or(Suite.name_here(term,name),Suite.names(I.Inline.append(F.Pair2<Nat,F.Term.t>,I.Inline.children(term),rest),name))

def Suite.contains(term:F.Term.t,name:String) -> Bool:
  Suite.names([F.Pair2{0n,term}],name)

def Suite.names_equal(a:List<&2,F.Pair2<String,F.Global.entry>>,b:List<&2,F.Pair2<String,F.Global.entry>>) -> Bool:
  match a b:
    case Nil{} Nil{}: True{}
    case F.Pair2{x,e} <> xs F.Pair2{y,f} <> ys: Bool.and(String.eq(x,y),Suite.names_equal(xs,ys))
    case other otherwise: False{}

def Suite.entry_matches(found:Maybe<&2,F.Global.entry>,entry:F.Global.entry) -> Bool:
  match found:
    case None{}: False{}
    case Some{value}: I.Inline.entry_equal(value,entry)

def Suite.consistent(rows:List<&2,F.Pair2<String,F.Global.entry>>,+globals:F.Global.t) -> Bool:
  match rows:
    case Nil{}: True{}
    case F.Pair2{name,entry} <> rest: Bool.and(Suite.entry_matches(F.Global.find(name,globals),entry),Suite.consistent(rest,globals))

def Suite.runtime_rows(rows:List<&2,F.Pair2<String,R.Erase.entry>>) -> List<&2,F.Pair2<String,R.Erase.entry>>:
  match rows:
    case Nil{}: Nil{}
    case F.Pair2{name,R.Erase.Dropped{}} <> rest: Suite.runtime_rows(rest)
    case row <> rest: row <> Suite.runtime_rows(rest)

def Suite.erase(checked:E.Elab.checked) -> Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,R.Erase.entry>>>:
  F.Pair2{globals,rows} = checked
  O.Opaque.program(~T.Test.semantics,C.Budget.unlimited,globals,rows)

def Suite.raw(checked:E.Elab.checked) -> Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,R.Erase.entry>>>:
  F.Pair2{globals,rows} = checked
  R.Erase.program(~T.Test.semantics,C.Budget.unlimited,globals,rows)

def Suite.same_output(+original:E.Elab.checked,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    before:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.raw(original)
    after:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(original)
    T.Test.require(String.eq(R.Erase.print(before),R.Erase.print(after)),message)

def Suite.layout_prepared(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = prepared
  T.Test.layout(globals)

def Suite.same_runtime(source:String,twin:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    sealed:E.Elab.checked <- E.Elab.check_in(G.Global.initial,twin)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    unit:Unit <- Suite.layout_prepared(prepared)
    before:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(original)
    after:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(sealed)
    T.Test.require(String.eq(R.Erase.print(Suite.runtime_rows(before)),R.Erase.print(Suite.runtime_rows(after))),"runtime differs from its sealed twin")

def Suite.check_generated_entry(entry:F.Global.entry,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  match entry:
    case F.Global.Axiom{F.Global.AxiomEntry{ty}}:
      R.Erase.bind(F.Level.t,Unit,K.Check.infer_univ(C.Check.make(globals,C.Budget.unlimited),ty),level => T.Test.require(F.Level.equal(level,F.Level.zero),"local postulate is not a closed proposition"))
    case other: Fail{F.Error.Mismatch{"local postulate has a body"}}

def Suite.generated_one(generated:Bool,entry:F.Global.entry,globals:F.Global.t) -> Result<&2,&2,F.Error.t,Nat>:
  match generated:
    case False{}: Done{0n}
    case True{}: R.Erase.bind(Unit,Nat,Suite.check_generated_entry(entry,globals),unit => Done{1n})

def Suite.generated(rows:List<&2,F.Pair2<String,F.Global.entry>>,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Nat>:
  match rows:
    case Nil{}: Done{0n}
    case F.Pair2{name,entry} <> rest:
      do Result<&2,&2,F.Error.t,Nat>:
        here:Nat <- Suite.generated_one(Suite.is_generated(name),entry,globals)
        more:Nat <- Suite.generated(rest,globals)
        Done{(here + more : Nat)}

def Suite.check_postulates(+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  R.Erase.bind(Nat,Unit,Suite.generated(F.Global.entries(globals),globals),count => T.Test.require(Bool.not(Nat.is_eq(count,0n)),"local proof has no postulate"))

def Suite.recheck_def(definition:F.Global.def_entry,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  F.Global.DefEntry{ty,body,reducible,recursive,partial} = definition
  R.Erase.bind(F.Value.t,Unit,V.Eval.eval(globals,Nil{},ty),expected => K.Check.check(C.Check.make(globals,C.Budget.unlimited),F.Quantity.One{},body,expected))

def Suite.recheck(+globals:F.Global.t,name:String) -> Result<&2,&2,F.Error.t,Unit>:
  R.Erase.bind(F.Global.def_entry,Unit,T.Test.definition(name,globals),definition => Suite.recheck_def(definition,globals))

def Suite.recheck_axiom(axiom:F.Global.axiom_entry,globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  F.Global.AxiomEntry{ty} = axiom
  R.Erase.bind(F.Level.t,Unit,K.Check.infer_univ(C.Check.make(globals,C.Budget.unlimited),ty),level => Done{Unit{}})

def Suite.host(host:Maybe<&2,F.Pair2<Bool,String>>,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  match host:
    case None{}: Done{Unit{}}
    case Some{F.Pair2{False{},name}}: Suite.recheck(globals,name)
    case Some{F.Pair2{True{},+name}}:
      R.Erase.bind(F.Global.axiom_entry,Unit,R.Erase.require(F.Global.axiom_entry,F.Global.find_axiom(name,globals),F.Error.Mismatch{"missing " ++ name}),axiom => Suite.recheck_axiom(axiom,globals))

def Suite.local_prepared(prepared:E.Elab.checked,host:Maybe<&2,F.Pair2<Bool,String>>) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- Suite.check_postulates(globals)
    b:Unit <- T.Test.require(Suite.consistent(rows,globals),"local declaration rows differ")
    c:Unit <- Suite.recheck(globals,"keep")
    Suite.host(host,globals)

def Suite.local_runtime(source:String,twin:String,host:Maybe<&2,F.Pair2<Bool,String>>) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    sealed:E.Elab.checked <- E.Elab.check_in(G.Global.initial,twin)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    unit:Unit <- Suite.local_prepared(prepared,host)
    before:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(original)
    after:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(sealed)
    T.Test.require(String.eq(R.Erase.print(Suite.runtime_rows(before)),R.Erase.print(Suite.runtime_rows(after))),"runtime differs from its sealed twin")

def Suite.sealed_count(prepared:E.Elab.checked,expected:Nat) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  R.Erase.bind(Nat,Unit,Suite.generated(F.Global.entries(globals),globals),count => T.Test.require(Nat.is_eq(count,expected),"a branch local proof fell back"))

def Suite.local_sealed(+source:String,twin:String,host:Maybe<&2,F.Pair2<Bool,String>>,expected:Nat) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    unit:Unit <- Suite.local_runtime(source,twin,host)
    original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    Suite.sealed_count(prepared,expected)

def Suite.inherited_finish(local:Bool,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  match local:
    case False{}: T.Test.layout(globals)
    case True{}:
      do Result<&2,&2,F.Error.t,Unit>:
        a:Unit <- Suite.check_postulates(globals)
        Suite.recheck(globals,"Layout")

def Suite.inherited_prepared(prepared:E.Elab.checked,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- T.Test.require(Nat.is_eq(R.Erase.length(F.Pair2<String,F.Global.entry>,rows),0n),"internal declarations escaped")
    Suite.inherited_finish(local,globals)

def Suite.inherited_checked(original:E.Elab.checked,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = original
  R.Erase.bind(E.Elab.checked,Unit,O.Opaque.prepare(~T.Test.semantics,C.Budget.unlimited,globals,Nil{}),prepared => Suite.inherited_prepared(prepared,local))

def Suite.inherited(source:String,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  R.Erase.bind(E.Elab.checked,Unit,E.Elab.check_in(G.Global.initial,source),original => Suite.inherited_checked(original,local))

def Suite.poison_scrut(scrut:F.Term.t,shape:F.Shape.t<F.Term.t>,q:F.Quantity.t,motive:Maybe<&2,F.Term.motive>,branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>>) -> Result<&2,&2,F.Error.t,F.Term.t>:
  match scrut:
    case F.Term.Ann{body,ty}: Done{F.Term.Elim{F.Term.Elimination{shape,F.Term.Ann{F.Term.Global{"missing_inline_body"},ty},q,motive,branches}}}
    case other: Fail{F.Error.Mismatch{"fixture lost its annotated scrutinee"}}

def Suite.poison(term:F.Term.t) -> Result<&2,&2,F.Error.t,F.Term.t>:
  match term:
    case F.Term.Let{name,ty,value,body}: Done{F.Term.Let{name,ty,F.Term.Global{"missing_inline_body"},body}}
    case F.Term.Elim{F.Term.Elimination{shape,scrut,q,motive,branches}}: Suite.poison_scrut(scrut,shape,q,motive,branches)
    case F.Term.Sec{shape,[F.Term.Leg{binders,body}]}:
      R.Erase.bind(F.Term.t,F.Term.t,Suite.poison(body),result => Done{F.Term.Sec{shape,[F.Term.Leg{binders,result}]}})
    case other: Fail{F.Error.Mismatch{"fixture lost its inline proof"}}

def Suite.poison_finish(prepared:E.Elab.checked,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = prepared
  Suite.inherited_finish(local,globals)

def Suite.poison_checked(original:E.Elab.checked,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = original
  do Result<&2,&2,F.Error.t,Unit>:
    +layout:F.Global.def_entry <- T.Test.definition("Layout",globals)
    body:F.Term.t <- Suite.poison(T.Test.def_body(layout))
    (+entry:F.Global.entry = T.Test.replace_body(layout,body)
     R.Erase.bind(E.Elab.checked,Unit,O.Opaque.prepare(~T.Test.semantics,C.Budget.unlimited,F.Global.add("Layout",entry,T.Test.remove(globals,"keep")),[F.Pair2{"Layout",entry}]),prepared => Suite.poison_finish(prepared,local)))

def Suite.poisoned(source:String,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  R.Erase.bind(E.Elab.checked,Unit,E.Elab.check_in(G.Global.initial,source),original => Suite.poison_checked(original,local))

def Suite.same_values(original:E.Elab.checked,prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = original
  F.Pair2{+opaque,sealed} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    before:F.Value.t <- T.Test.eval_global(globals,"value")
    after:F.Value.t <- T.Test.eval_global(opaque,"value")
    bt:F.Term.t <- V.Eval.quote(globals,0n,before)
    at:F.Term.t <- V.Eval.quote(opaque,0n,after)
    T.Test.require(I.Inline.term_equal(bt,at),"runtime let changed")

def Suite.runtime() -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,"def value : Nat := let n : Nat := 7 in n")
    prepared:E.Elab.checked <- T.Test.prepare(original)
    unit:Unit <- Suite.same_values(original,prepared)
    Suite.same_output(original,"runtime output changed")

def Suite.inline_prepared(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    keep:F.Global.def_entry <- T.Test.definition("keep",globals)
    a:Unit <- T.Test.require(Bool.not(T.Test.some(F.Global.entry,F.Global.find(Suite.postulate(0n),globals))),"no postulate leaked")
    T.Test.require(Bool.not(Suite.contains(T.Test.def_body(keep),Suite.postulate(0n))),"keep is postulate-free")

def Suite.stays_inline(source:String,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    unit:Unit <- Suite.inline_prepared(prepared)
    Suite.same_output(original,message)

def Suite.row_layout(layout:Bool,globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  match layout:
    case True{}: T.Test.layout(globals)
    case False{}: Done{Unit{}}

def Suite.rows_prepared(prepared:E.Elab.checked,original:E.Elab.checked,layout:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,+rows} = prepared
  F.Pair2{old,oldrows} = original
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- T.Test.require(Suite.names_equal(oldrows,rows),"declaration rows changed")
    b:Unit <- T.Test.require(Suite.consistent(rows,globals),"stale declaration reinserted")
    Suite.row_layout(layout,globals)

def Suite.rows(source:String,layout:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    Suite.rows_prepared(prepared,original,layout)

def Suite.collision_kind(family:Bool,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  match family:
    case False{}:
      T.Test.require(Suite.entry_matches(F.Global.find(Suite.postulate(0n),globals),F.Global.Axiom{F.Global.AxiomEntry{G.Prim.nat_ty}}),"fresh proof shadowed an existing name")
    case True{}:
      do Result<&2,&2,F.Error.t,Unit>:
        a:Unit <- T.Test.require(Bool.not(T.Test.some(F.Global.entry,F.Global.find(Suite.postulate(0n),globals))),"fresh proof collided with a family")
        T.Test.require(T.Test.axiom(Suite.postulate(1n),globals),"fresh proof skipped the next name")

def Suite.collision_prepared(prepared:E.Elab.checked,rows:List<&2,F.Pair2<String,F.Global.entry>>,family:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rewritten} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- Suite.collision_kind(family,globals)
    layout:F.Global.def_entry <- T.Test.definition("Layout",globals)
    b:Unit <- T.Test.require(Bool.not(Suite.contains(T.Test.def_body(layout),Suite.postulate(0n))),"fresh proof referenced an existing name")
    c:Unit <- T.Test.require(Suite.names_equal(rows,rewritten),"declaration rows changed")
    T.Test.layout(globals)

def Suite.rename_family(family:F.Positivity.family,name:String) -> F.Positivity.family:
  F.Positivity.Family{old,params,indices,level,status,ctors,positive} = family
  F.Positivity.Family{name,params,indices,level,status,ctors,positive}

def Suite.collision_scope(family:Bool,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,F.Global.t>:
  match family:
    case False{}: Done{F.Global.add(Suite.postulate(0n),F.Global.Axiom{F.Global.AxiomEntry{G.Prim.nat_ty}},globals)}
    case True{}:
      R.Erase.bind(F.Positivity.family,F.Global.t,R.Erase.require(F.Positivity.family,F.Global.find_family("Equal",globals),F.Error.Mismatch{"missing Equal"}),value => Done{F.Global.add_family(Suite.postulate(0n),Suite.rename_family(value,Suite.postulate(0n)),globals)})

def Suite.collision_checked(original:E.Elab.checked,+family:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,+rows} = original
  do Result<&2,&2,F.Error.t,Unit>:
    next:F.Global.t <- Suite.collision_scope(family,globals)
    prepared:E.Elab.checked <- O.Opaque.prepare(~T.Test.semantics,C.Budget.unlimited,next,rows)
    Suite.collision_prepared(prepared,rows,family)

def Suite.collision(family:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  R.Erase.bind(E.Elab.checked,Unit,E.Elab.check_in(G.Global.initial,X.Fixture.scrutinee_proof),original => Suite.collision_checked(original,family))

def Suite.lambda_sealed(term:F.Term.t) -> Bool:
  match term:
    case F.Term.Let{name,ty,F.Term.Global{proof},body}: Suite.is_generated(proof)
    case other: False{}

def Suite.lambda_prepared(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = prepared
  R.Erase.bind(F.Global.def_entry,Unit,T.Test.definition("Layout",globals),layout => T.Test.require(Suite.lambda_sealed(T.Test.def_body(layout)),"closed proof lambda was not sealed as a whole"))

def Suite.binders() -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- Suite.same_runtime(X.Fixture.lambda_proof,X.Fixture.lambda_proof_opaque)
    prepared:E.Elab.checked <- T.Test.prepared(X.Fixture.lambda_proof)
    b:Unit <- Suite.lambda_prepared(prepared)
    Suite.same_runtime(X.Fixture.binder_proof,X.Fixture.binder_proof_opaque)

def Suite.motive_term(term:F.Term.t,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  match term:
    case F.Term.Elim{F.Term.Elimination{shape,F.Term.Global{+name},q,motive,branches}}:
      do Result<&2,&2,F.Error.t,Unit>:
        a:Unit <- T.Test.require(Suite.is_generated(name),"motive-bearing proof was not replaced as a whole")
        T.Test.require(T.Test.axiom(name,globals),"motive-bearing proof lacks its postulate")
    case other: Fail{F.Error.Mismatch{"motive-bearing proof was not replaced as a whole"}}

def Suite.motive_prepared(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  R.Erase.bind(F.Global.def_entry,Unit,T.Test.definition("Layout",globals),layout => Suite.motive_term(T.Test.def_body(layout),globals))

def Suite.payload_indices(n:Nat,+index:Nat,+globals:F.Global.t,+ty:F.Term.t) -> Bool:
  match n:
    case 0n: True{}
    case 1n+rest:
      Bool.and(Bool.not(Bool.xor(T.Test.axiom(Suite.postulate(index),globals),Nat.is_eq(index,0n))),Bool.and(Bool.not(Bool.xor(Suite.contains(ty,Suite.postulate(index)),Nat.is_eq(index,0n))),Suite.payload_indices(rest,1n+index,globals,ty)))

def Suite.payload_axiom(axiom:F.Global.axiom_entry,globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  F.Global.AxiomEntry{ty} = axiom
  T.Test.require(Suite.payload_indices(8n,0n,globals,ty),"payload postulate orphaned, missing, or duplicated")

def Suite.payload_postulates(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  R.Erase.bind(F.Global.axiom_entry,Unit,R.Erase.require(F.Global.axiom_entry,F.Global.find_axiom("use",globals),F.Error.Mismatch{"use is not an axiom"}),axiom => Suite.payload_axiom(axiom,globals))

def Suite.universe_axiom(axiom:F.Global.axiom_entry,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  F.Global.AxiomEntry{+ty} = axiom
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- T.Test.require(Suite.contains(ty,"U"),"local domain lost its declared universe")
    b:Unit <- T.Test.require(Suite.contains(ty,"Equal"),"local postulate does not state the local proof")
    Suite.recheck(globals,"keep")

def Suite.universe_prepared(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- Suite.check_postulates(globals)
    axiom:F.Global.axiom_entry <- R.Erase.require(F.Global.axiom_entry,F.Global.find_axiom(Suite.postulate(0n),globals),F.Error.Mismatch{"missing local postulate"})
    Suite.universe_axiom(axiom,globals)

def Suite.proof_let_prepared(original:E.Elab.checked,prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{globals,rows} = original
  F.Pair2{+opaque,sealed} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    before:F.Global.def_entry <- T.Test.definition("Layout",globals)
    after:F.Global.def_entry <- T.Test.definition("Layout",opaque)
    a:Unit <- Suite.check_postulates(opaque)
    b:Unit <- T.Test.require(Bool.not(I.Inline.term_equal(T.Test.def_body(before),T.Test.def_body(after))),"local proof over a proof let was not sealed")
    c:Unit <- Suite.recheck(opaque,"Layout")
    Suite.recheck(opaque,"keep")

def Suite.proof_let() -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    +original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,X.Fixture.source_local_proof_let)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    Suite.proof_let_prepared(original,prepared)

def Suite.hypothesis_types(axiom:F.Global.axiom_entry,expected:F.Global.axiom_entry,+globals:F.Global.t) -> Result<&2,&2,F.Error.t,Unit>:
  F.Global.AxiomEntry{ty} = axiom
  F.Global.AxiomEntry{want} = expected
  do Result<&2,&2,F.Error.t,Unit>:
    sealed:F.Value.t <- V.Eval.eval(globals,Nil{},ty)
    wanted:F.Value.t <- V.Eval.eval(globals,Nil{},want)
    a:Unit <- K.Check.check(C.Check.make(globals,C.Budget.unlimited),F.Quantity.Zero{},F.Term.Global{"expected"},sealed)
    b:Unit <- K.Check.check(C.Check.make(globals,C.Budget.unlimited),F.Quantity.Zero{},F.Term.Global{Suite.postulate(0n)},wanted)
    Suite.recheck(globals,"g")

def Suite.hypothesis(prepared:E.Elab.checked) -> Result<&2,&2,F.Error.t,Unit>:
  F.Pair2{+globals,rows} = prepared
  do Result<&2,&2,F.Error.t,Unit>:
    a:Unit <- Suite.check_postulates(globals)
    axiom:F.Global.axiom_entry <- R.Erase.require(F.Global.axiom_entry,F.Global.find_axiom(Suite.postulate(0n),globals),F.Error.Mismatch{"missing local postulate"})
    expected:F.Global.axiom_entry <- R.Erase.require(F.Global.axiom_entry,F.Global.find_axiom("expected",globals),F.Error.Mismatch{"missing expected"})
    Suite.hypothesis_types(axiom,expected,globals)

type Suite.case is Type:
  Suite.Case{name:String,run:Unit -> Result<&2,&2,F.Error.t,Unit>}

def Suite.report(result:Result<&2,&2,F.Error.t,Unit>,name:String) -> IO(Unit):
  match result:
    case Done{unit}: IO.print("INLINE-ERASE row=" ++ name ++ " OK")
    case Fail{error}: IO.pure(Unit,Unit{})

def Suite.failure(result:Result<&2,&2,F.Error.t,Unit>,name:String) -> List<&2,String>:
  match result:
    case Done{unit}: Nil{}
    case Fail{error}: ["INLINE-ERASE row=" ++ name ++ " FAIL " ++ F.Error.to_string(error)]

def Suite.run(rows:List<Suite.case>,count:Nat,errors:List<&2,String>) -> IO(F.Pair2<Nat,List<&2,String>>):
  match rows:
    case Nil{}: IO.pure(F.Pair2<Nat,List<&2,String>>,F.Pair2{count,errors})
    case Suite.Case{+name,run} <> rest:
      +result:Result<&2,&2,F.Error.t,Unit> = run(Unit{})
      do IO<F.Pair2<Nat,List<&2,String>>>:
        reported:Unit <- Suite.report(result,name)
        Suite.run(rest,(count + T.Test.count_ok(result) : Nat),R.Erase.append(String,errors,Suite.failure(result,name)))

def Suite.errors(errors:List<&2,String>) -> IO(Unit):
  match errors:
    case Nil{}: IO.pure(Unit,Unit{})
    case error <> rest:
      do IO<Unit>:
        reported:Unit <- IO.print_err(error)
        Suite.errors(rest)

def Suite.finish(+total:Nat,summary:F.Pair2<Nat,List<&2,String>>) -> IO(Unit):
  F.Pair2{+count,errors} = summary
  +passed:Bool = Nat.is_eq(count,total)
  do IO<Unit>:
    reported:Unit <- Suite.errors(errors)
    wrote:Unit <- IO.print("INLINE-ERASE pass=" ++ F.Text.nat(count) ++ " total=" ++ F.Text.nat(total) ++ " " ++ T.Test.status(passed))
    T.Test.exit(passed)

def Suite.length(rows:List<Suite.case>,n:Nat) -> Nat:
  match rows:
    case Nil{}: n
    case Suite.Case{name,run} <> rest: Suite.length(rest,(n + 1n : Nat))

def Suite.branch_absent(state:R.Erase.State<Maybe<&2,I.Inline.context>>) -> Result<&2,&2,F.Error.t,Unit>:
  match state:
    case R.Erase.Return{None{}}: Done{Unit{}}
    case other: Fail{F.Error.Mismatch{"unsupported branch acquired a context"}}

def Suite.branch_fallback() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  params:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"n",F.Term.Global{"Nat"}}]
  family:F.Positivity.family = F.Positivity.Family{"Box",params,Nil{},F.Level.zero,F.Positivity.Complete{["box"]},[F.Positivity.Ctor{"box",Nil{},Nil{},0n,False{}}],True{}}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.branch_absent(I.Inline.branch_context_state(F.Shape.make_inductive(F.Term.t,"Missing",Nil{}),F.Term.ACtor{"box"},Nil{},context))
    Suite.branch_absent(I.Inline.branch_family_state(Some{family},"box",Nil{},context))

def Suite.branch_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +fields:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{}, "n", F.Term.Global{"Nat"}}]
  do Result<&2,&2,F.Error.t,Unit>:
    quantity: Unit <- T.Test.require(Bool.not(I.Inline.branch_fields_valid(fields, [F.Pair2{F.Quantity.One{}, "n"}], 0n)), "branch accepted a quantity mismatch")
    missing: Unit <- T.Test.require(Bool.not(I.Inline.branch_fields_valid(fields, Nil{}, 0n)), "branch accepted a missing binder")
    extra: Unit <- T.Test.require(Bool.not(I.Inline.branch_fields_valid(Nil{}, [F.Pair2{F.Quantity.Zero{}, "n"}], 0n)), "branch accepted an extra binder")
    outer: Unit <- T.Test.require(Bool.not(I.Inline.branch_fields_valid([F.Triple3{F.Quantity.Zero{}, "n", F.Term.Var{0n}}], [F.Pair2{F.Quantity.Zero{}, "n"}], 0n)), "branch metadata captured an outer variable")
    +pair:List<&2, F.Pair2<F.Quantity.t, String>> = [F.Pair2{F.Quantity.Zero{}, "n"}, F.Pair2{F.Quantity.Zero{}, "p"}]
    later: Unit <- T.Test.require(Bool.not(I.Inline.branch_fields_valid([F.Triple3{F.Quantity.Zero{}, "n", F.Term.Global{"Nat"}}, F.Triple3{F.Quantity.Zero{}, "p", F.Term.Var{1n}}], pair, 0n)), "second branch field captured an outer variable")
    T.Test.require(I.Inline.branch_fields_valid([F.Triple3{F.Quantity.Zero{}, "n", F.Term.Global{"Nat"}}, F.Triple3{F.Quantity.Zero{}, "p", F.Term.Var{0n}}], pair, 0n), "second branch field lost its earlier field")

def Suite.cases(+layout:Maybe<&2,F.Pair2<Bool,String>>) -> List<Suite.case>:
  [
      Suite.Case{"let-body",unit => Suite.poisoned(X.Fixture.let_proof,False{})},
      Suite.Case{"scrutinee-body",unit => Suite.poisoned(X.Fixture.scrutinee_proof,False{})},
      Suite.Case{"inherited",unit => Suite.inherited(X.Fixture.let_proof,False{})},
      Suite.Case{"name-collision",unit => Suite.collision(False{})},
      Suite.Case{"family-collision",unit => Suite.collision(True{})},
      Suite.Case{"runtime",unit => Suite.runtime},
      Suite.Case{"local-type",unit => Suite.stays_inline(X.Fixture.source_local_type,"type-only local escaped its binder")},
      Suite.Case{"rows",unit => Suite.rows(X.Fixture.let_proof,False{})},
      Suite.Case{"binders",unit => Suite.binders},
      Suite.Case{"motive",unit => R.Erase.bind(E.Elab.checked,Unit,T.Test.prepared(X.Fixture.binder_proof),prepared => Suite.motive_prepared(prepared))},
      Suite.Case{"shape-payload",unit => Suite.stays_inline(X.Fixture.payload_open_proof,"payload-open proof escaped its binder")},
      Suite.Case{"redeclared",unit => Suite.rows(X.Fixture.redeclared_proof,True{})},
      Suite.Case{"payload-postulates",unit => R.Erase.bind(E.Elab.checked,Unit,T.Test.prepared(X.Fixture.duplicate_payload),prepared => Suite.payload_postulates(prepared))},
      Suite.Case{"local-index",unit => Suite.local_runtime(X.Fixture.local_proof,X.Fixture.local_proof_opaque,layout)},
      Suite.Case{"local-dependent",unit => Suite.local_runtime(X.Fixture.local_dependent,X.Fixture.local_dependent_opaque,layout)},
      Suite.Case{"local-let",unit => Suite.local_runtime(X.Fixture.local_let,X.Fixture.local_let_opaque,layout)},
      Suite.Case{"local-let-alias",unit => Suite.local_runtime(X.Fixture.local_let_alias,X.Fixture.local_let_alias_opaque,layout)},
      Suite.Case{"local-diagram",unit => Suite.local_runtime(X.Fixture.local_diagram,X.Fixture.local_diagram_opaque,Some{F.Pair2{True{},"Function"}})},
      Suite.Case{"local-inherited",unit => Suite.inherited(X.Fixture.local_dependent,True{})},
      Suite.Case{"local-poison",unit => Suite.poisoned(X.Fixture.local_dependent,True{})},
      Suite.Case{"local-universe",unit => R.Erase.bind(E.Elab.checked,Unit,T.Test.prepared(X.Fixture.source_local_universe),prepared => Suite.universe_prepared(prepared))},
      Suite.Case{"local-proof-let",unit => Suite.proof_let},
      Suite.Case{"local-proof-let-value",unit => Suite.local_runtime(X.Fixture.local_proof_let_value,X.Fixture.local_proof_let_value_opaque,layout)},
      Suite.Case{"local-proof-let-type",unit => Suite.local_runtime(X.Fixture.local_proof_let_type,X.Fixture.local_proof_let_type_opaque,layout)},
      Suite.Case{"local-proof-let-alias",unit => Suite.local_runtime(X.Fixture.local_proof_let_alias,X.Fixture.local_proof_let_alias_opaque,layout)},
      Suite.Case{"local-proof-let-family",unit => Suite.local_runtime(X.Fixture.local_proof_let_family,X.Fixture.local_proof_let_family_opaque,layout)},
      Suite.Case{"local-proof-let-universe",unit => Suite.local_runtime(X.Fixture.local_proof_let_universe,X.Fixture.local_proof_let_universe_opaque,layout)},
      Suite.Case{"local-payload",unit => R.Erase.bind(E.Elab.checked,Unit,T.Test.prepared(X.Fixture.source_local_payload),prepared => Suite.local_prepared(prepared,None{}))},
      Suite.Case{"local-runtime-call",unit => Suite.local_runtime(X.Fixture.local_runtime_call,X.Fixture.local_runtime_call_opaque,layout)},
      Suite.Case{"local-hypothesis",unit => R.Erase.bind(E.Elab.checked,Unit,T.Test.prepared(X.Fixture.source_local_hypothesis),prepared => Suite.hypothesis(prepared))},
      Suite.Case{"branch-scope",unit => Suite.local_runtime(X.Fixture.branch_local_proof,X.Fixture.branch_local_proof_opaque,layout)},
      Suite.Case{"branch-dependent",unit => Suite.local_runtime(B.Fixture.branch_dependent,B.Fixture.branch_dependent_opaque,layout)},
      Suite.Case{"branch-nested",unit => Suite.local_runtime(B.Fixture.branch_nested,B.Fixture.branch_nested_opaque,layout)},
      Suite.Case{"branch-multi-ctor",unit => Suite.local_sealed(B.Fixture.branch_multi_ctor,B.Fixture.branch_multi_ctor_opaque,layout,2n)},
      Suite.Case{"alias-leg-scope",unit => Suite.stays_inline(X.Fixture.alias_leg_scope,"unknown binder was confused with an outer binder")},
      Suite.Case{"branch-metadata",unit => Suite.branch_guards},
      Suite.Case{"branch-fallback",unit => Suite.branch_fallback} ]

def main() -> IO(Unit):
  +layout:Maybe<&2,F.Pair2<Bool,String>> = Some{F.Pair2{False{},"Layout"}}
  do IO<Unit>:
    summary:F.Pair2<Nat,List<&2,String>> <- Suite.run(Suite.cases(layout),0n,Nil{})
    Suite.finish(Suite.length(Suite.cases(layout),0n),summary)
