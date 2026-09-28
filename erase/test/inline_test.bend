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
import ./parameter_fixtures.bend as PF
import ./motive_fixtures.bend as MF
import ./lambda_fixtures.bend as LF
import ../../lib/kernel_pp.bend as P

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

# Two constructors have the same field shape and different proof types.
# The proof is in the first constructor, then in the last constructor.
def Suite.parameter_ctors(+layout:Maybe<&2,F.Pair2<Bool,String>>) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    first:Unit <- Suite.local_sealed(PF.Fixture.branch_parameter_ctor,PF.Fixture.branch_parameter_ctor_opaque,layout,1n)
    Suite.local_sealed(PF.Fixture.branch_parameter_ctor_last,PF.Fixture.branch_parameter_ctor_last_opaque,layout,1n)

def Suite.axiom_term(axiom:F.Global.axiom_entry) -> Result<&2,&2,F.Error.t,F.Term.t>:
  F.Global.AxiomEntry{ty} = axiom
  Done{ty}

def Suite.axiom_type(prepared:E.Elab.checked,+name:String) -> Result<&2,&2,F.Error.t,F.Term.t>:
  F.Pair2{globals,rows} = prepared
  R.Erase.bind(F.Global.axiom_entry,F.Term.t,R.Erase.require(F.Global.axiom_entry,F.Global.find_axiom(name,globals),F.Error.Mismatch{"missing " ++ name}),axiom => Suite.axiom_term(axiom))

# The sealed postulate type must keep the source syntax of the specialized
# field: universes and annotations must match the twin axiom exactly.
def Suite.sealed_syntax(+source:String,+twin:String,host:Maybe<&2,F.Pair2<Bool,String>>) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    unit:Unit <- Suite.local_sealed(source,twin,host,1n)
    original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    prepared:E.Elab.checked <- T.Test.prepare(original)
    sealed:E.Elab.checked <- E.Elab.check_in(G.Global.initial,twin)
    +generated:F.Term.t <- Suite.axiom_type(prepared,Suite.postulate(0n))
    +expected:F.Term.t <- Suite.axiom_type(sealed,"proof")
    T.Test.require(I.Inline.term_equal(generated,expected),"sealed postulate type lost its source syntax: " ++ P.Pp.term(Nil{},generated) ++ " is not " ++ P.Pp.term(Nil{},expected))

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

def Suite.branch_absent_as(state:R.Erase.State<Maybe<&2,I.Inline.context>>,label:String) -> Result<&2,&2,F.Error.t,Unit>:
  match state:
    case R.Erase.Return{None{}}: Done{Unit{}}
    case other: Fail{F.Error.Mismatch{label}}

def Suite.branch_absent(state:R.Erase.State<Maybe<&2,I.Inline.context>>) -> Result<&2,&2,F.Error.t,Unit>:
  Suite.branch_absent_as(state,"unsupported branch acquired a context")

def Suite.branch_fallback() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  params:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"n",F.Term.Global{"Nat"}}]
  family:F.Positivity.family = F.Positivity.Family{"Box",params,Nil{},F.Level.zero,F.Positivity.Complete{["box"]},[F.Positivity.Ctor{"box",Nil{},Nil{},0n,False{}}],True{}}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.branch_absent(I.Inline.branch_context_state(F.Shape.make_inductive(F.Term.t,"Missing",Nil{}),F.Term.ACtor{"box"},Nil{},context))
    Suite.branch_absent(I.Inline.branch_family_state(Some{family},"box",Nil{},context))

def Suite.parameter_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  +params:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"n",F.Term.Global{"Nat"}}]
  +ctor:Maybe<&2,F.Positivity.ctor> = Some{F.Positivity.Ctor{"box",Nil{},Nil{},0n,False{}}}
  +args:List<&2,F.Term.t> = [F.Term.Global{"Nat"}]
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Box",Nil{})
  +diagram:F.Term.t = F.Term.Sec{F.Shape.make_collection(F.Term.t,1n),[F.Term.Leg{Nil{},F.Term.Global{"Nat"}}]}
  do Result<&2,&2,F.Error.t,Unit>:
    absent:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,None{},Nil{},context))
    missing:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,Some{Nil{}},Nil{},context))
    extra:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,Some{[F.Term.Global{"Nat"},F.Term.Global{"Nat"}]},Nil{},context))
    free:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,Some{[F.Term.Var{0n}]},Nil{},context))
    field:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(Some{F.Positivity.Ctor{"box",[F.Triple3{F.Quantity.Zero{},"x",F.Term.Var{1n}}],Nil{},1n,False{}}},params,Some{args},[F.Pair2{F.Quantity.Zero{},"x"}],context))
    family:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,I.Inline.branch_arguments(Some{F.Term.Lan{F.Shape.make_inductive(F.Term.t,"Other",Nil{}),diagram}},shape),Nil{},context))
    indices:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,I.Inline.branch_arguments(Some{F.Term.Lan{F.Shape.make_inductive(F.Term.t,"Box",[F.Term.Global{"Nat"}]),diagram}},shape),Nil{},context))
    width:Unit <- Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,I.Inline.parameter_diagram(F.Term.Sec{F.Shape.make_collection(F.Term.t,0n),[F.Term.Leg{Nil{},F.Term.Global{"Nat"}}]}),Nil{},context))
    Suite.branch_absent(I.Inline.parameterized_ctor_state(ctor,params,I.Inline.parameter_diagram(F.Term.Sec{F.Shape.make_collection(F.Term.t,1n),[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"x"}],F.Term.Var{0n}}]}),Nil{},context))

def Suite.motive_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +family:F.Positivity.family = F.Positivity.Family{"Box",Nil{},[F.Triple3{F.Quantity.One{},"index",F.Term.Global{"Nat"}}],F.Level.one,F.Positivity.Complete{Nil{}},Nil{},True{}}
  globals:F.Global.t = F.Global.add_family("Box",family,F.Global.add_family("Other",Suite.rename_family(family,"Other"),G.Global.initial))
  +context:I.Inline.context = I.Inline.Context{C.Check.make(globals,C.Budget.unlimited),Nil{}}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Box",[F.Term.Global{"Nat"}])
  +scrut:F.Term.t = F.Term.Global{"unknown"}
  +params:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"A",F.Term.Univ{F.Level.one}}]
  +fields:F.Positivity.telescope = [F.Triple3{F.Quantity.One{},"index",F.Term.Var{0n}}]
  +names:List<&2,String> = ["k"]
  +args:Maybe<&2,List<&2,F.Term.t>> = Some{[F.Term.Global{"Nat"}]}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.branch_absent(I.Inline.motive_context_state(F.Shape.make_inductive(F.Term.t,"Missing",[F.Term.Global{"Nat"}]),scrut,Some{"Missing"},names,"self",context))
    unnamed:Unit <- Suite.branch_absent(I.Inline.motive_context_state(shape,scrut,None{},names,"self",context))
    family:Unit <- Suite.branch_absent(I.Inline.motive_context_state(shape,scrut,Some{"Other"},names,"self",context))
    shape_count:Unit <- Suite.branch_absent(I.Inline.motive_context_state(F.Shape.make_inductive(F.Term.t,"Box",Nil{}),scrut,Some{"Box"},names,"self",context))
    unavailable:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,fields,names,"self",None{},context))
    short:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,fields,names,"self",Some{Nil{}},context))
    long:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,fields,names,"self",Some{[F.Term.Global{"Nat"},F.Term.Global{"Nat"}]},context))
    open:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,fields,names,"self",Some{[F.Term.Var{0n}]},context))
    index_count:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,fields,Nil{},"self",args,context))
    extra_index:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,fields,["k","extra"],"self",args,context))
    free_domain:Unit <- Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,[F.Triple3{F.Quantity.Zero{},"k",F.Term.Var{1n}}],names,"self",args,context))
    Suite.branch_absent(I.Inline.motive_arguments_state("Box",params,[F.Triple3{F.Quantity.Zero{},"x",F.Term.Global{"Nat"}},F.Triple3{F.Quantity.Zero{},"k",F.Term.Var{2n}}],["j","k"],"self",args,context))

def Suite.motive_quantities_scope(scope:Maybe<&2,I.Inline.context>) -> Result<&2,&2,F.Error.t,Unit>:
  match scope:
    case Some{I.Inline.Context{C.Check.Ctx{globals,env,Con{F.Triple3{self,sq,sty},Con{F.Triple3{index,iq,ity},Nil{}}},size,budget},domains}}:
      T.Test.require(Bool.and(Nat.is_eq(size,2n),Bool.and(String.eq(self,"self"),Bool.and(String.eq(index,"k"),Bool.and(F.Quantity.equal(sq,F.Quantity.Zero{}),F.Quantity.equal(iq,F.Quantity.Zero{}))))),"motive binders are not erased")
    case other: Fail{F.Error.Mismatch{"motive binder context missing"}}

def Suite.motive_quantities() -> Result<&2,&2,F.Error.t,Unit>:
  context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  fields:F.Positivity.telescope = [F.Triple3{F.Quantity.One{},"index",F.Term.Global{"Nat"}}]
  do Result<&2,&2,F.Error.t,Unit>:
    scope:Maybe<&2,I.Inline.context> <- R.Erase.State.finish(Maybe<&2,I.Inline.context>,I.Inline.motive_fields_state(fields,["k"],"self",F.Term.Global{"Nat"},context),C.Budget.unlimited)
    Suite.motive_quantities_scope(scope)

def Suite.application_equal(actual:Maybe<&2,F.Term.t>,expected:F.Term.t) -> Result<&2,&2,F.Error.t,Unit>:
  match actual:
    case None{}: Fail{F.Error.Mismatch{"application source type missing"}}
    case Some{ty}: T.Test.require(I.Inline.term_equal(ty,expected),"application substitution captured an outer variable")

def Suite.application_absent(actual:Maybe<&2,F.Term.t>,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  match actual:
    case None{}: Done{Unit{}}
    case Some{ty}: Fail{F.Error.Mismatch{message}}

def Suite.application_capture() -> Result<&2,&2,F.Error.t,Unit>:
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero})
  codomain:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Many{},"x",F.Term.Var{0n}),F.Term.Var{3n}}
  expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Many{},"x",F.Term.Var{1n}),F.Term.Var{2n}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.application_type(Some{F.Term.Ran{point,codomain}},F.Term.APt{F.Quantity.Zero{},F.Term.Var{1n}},2n)
    Suite.application_equal(actual,expected)

def Suite.application_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero})
  +arg:F.Term.addr = F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}}
  +ty:F.Term.t = F.Term.Ran{point,F.Term.Var{0n}}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Maybe<&2,F.Term.t> <- I.Inline.application_type(None{},arg,0n)
    missing_ok:Unit <- Suite.application_absent(missing,"application missing head type accepted")
    scalar:Maybe<&2,F.Term.t> <- I.Inline.application_type(Some{F.Term.Global{"Nat"}},arg,0n)
    scalar_ok:Unit <- Suite.application_absent(scalar,"application nonfunction accepted")
    projection:Maybe<&2,F.Term.t> <- I.Inline.application_type(Some{ty},F.Term.ALeg{0n},0n)
    projection_ok:Unit <- Suite.application_absent(projection,"application projection accepted")
    collection:Maybe<&2,F.Term.t> <- I.Inline.application_type(Some{F.Term.Ran{F.Shape.make_collection(F.Term.t,1n),F.Term.Global{"Nat"}}},arg,0n)
    collection_ok:Unit <- Suite.application_absent(collection,"application nonpoint former accepted")
    free_type:Maybe<&2,F.Term.t> <- I.Inline.application_type(Some{F.Term.Ran{point,F.Term.Var{1n}}},arg,0n)
    free_type_ok:Unit <- Suite.application_absent(free_type,"application free codomain accepted")
    free_arg:Maybe<&2,F.Term.t> <- I.Inline.application_type(Some{ty},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},0n)
    Suite.application_absent(free_arg,"application free argument accepted")

def Suite.alias_entry(body:F.Term.t) -> F.Global.entry:
  F.Global.Def{F.Global.DefEntry{F.Term.Univ{F.Level.one},body,True{},None{},False{}}}

def Suite.alias_global() -> Result<&2,&2,F.Error.t,Unit>:
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  globals:F.Global.t = F.Global.add("Fn",Suite.alias_entry(ty),F.Global.add("Alias",Suite.alias_entry(F.Term.Global{"Fn"}),G.Global.initial))
  +context:I.Inline.context = I.Inline.Context{C.Check.make(globals,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{F.Term.Global{"Alias"}},F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}},context)
    Suite.application_equal(actual,F.Term.Global{"Nat"})

def Suite.alias_local() -> Result<&2,&2,F.Error.t,Unit>:
  value:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Many{},"x",F.Term.Var{0n}),F.Term.Var{1n}}
  +locals:List<&2,I.Inline.local> = [I.Inline.Param{"y",F.Term.Global{"Nat"}},I.Inline.Local{"Alias",F.Term.Univ{F.Level.zero},value},I.Inline.Param{"A",F.Term.Univ{F.Level.zero}}]
  context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),locals}
  expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Many{},"x",F.Term.Var{2n}),F.Term.Var{3n}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.alias_type(4n,Some{F.Term.Var{1n}},context)
    Suite.application_equal(actual,expected)

# The local alias names a global alias, so the hop leaves the local list.
def Suite.alias_local_global() -> Result<&2,&2,F.Error.t,Unit>:
  ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  globals:F.Global.t = F.Global.add("Fn",Suite.alias_entry(ty),G.Global.initial)
  +locals:List<&2,I.Inline.local> = [I.Inline.Local{"Alias",F.Term.Univ{F.Level.zero},F.Term.Global{"Fn"}}]
  +context:I.Inline.context = I.Inline.Context{C.Check.make(globals,C.Budget.unlimited),locals}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{F.Term.Var{0n}},F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}},context)
    Suite.application_equal(actual,F.Term.Global{"Nat"})

# The chain uses every global entry, so the bound has no spare hop.
def Suite.alias_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  chain:F.Global.t = F.Global.add("A4",Suite.alias_entry(F.Term.Global{"A3"}),F.Global.add("A3",Suite.alias_entry(F.Term.Global{"A2"}),F.Global.add("A2",Suite.alias_entry(F.Term.Global{"A1"}),F.Global.add("A1",Suite.alias_entry(ty),F.Global.empty))))
  +context:I.Inline.context = I.Inline.Context{C.Check.make(chain,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    exhausted:Maybe<&2,F.Term.t> <- I.Inline.alias_type(0n,Some{ty},context)
    exhausted_ok:Unit <- Suite.application_absent(exhausted,"exhausted alias fuel accepted")
    actual:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{F.Term.Global{"A4"}},F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}},context)
    Suite.application_equal(actual,F.Term.Global{"Nat"})

def Suite.alias_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Many{},"x",F.Term.Global{"Nat"}),F.Term.Global{"Nat"}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  cycle:F.Global.t = F.Global.add("Cycle",Suite.alias_entry(F.Term.Global{"Cycle"}),G.Global.initial)
  context:I.Inline.context = I.Inline.Context{C.Check.make(cycle,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    opaque:Unit <- Suite.application_absent(I.Inline.global_alias(Some{F.Global.Def{F.Global.DefEntry{univ,ty,False{},None{},False{}}}}),"opaque alias unfolded")
    recursive:Unit <- Suite.application_absent(I.Inline.global_alias(Some{F.Global.Def{F.Global.DefEntry{univ,ty,True{},Some{0n},False{}}}}),"recursive alias unfolded")
    partial:Unit <- Suite.application_absent(I.Inline.global_alias(Some{F.Global.Def{F.Global.DefEntry{univ,ty,True{},None{},True{}}}}),"partial alias unfolded")
    free:Unit <- Suite.application_absent(I.Inline.global_alias(Some{Suite.alias_entry(F.Term.Var{0n})}),"free global alias accepted")
    axiom:Unit <- Suite.application_absent(I.Inline.global_alias(Some{F.Global.Axiom{F.Global.AxiomEntry{ty}}}),"axiom alias unfolded")
    missing:Unit <- Suite.application_absent(I.Inline.global_alias(None{}),"missing alias unfolded")
    param:Maybe<&2,F.Term.t> <- I.Inline.local_alias([I.Inline.Param{"A",univ}],0n,0n)
    param_ok:Unit <- Suite.application_absent(param,"parameter alias unfolded")
    self:Maybe<&2,F.Term.t> <- I.Inline.local_alias([I.Inline.Local{"A",univ,F.Term.Var{0n}}],0n,0n)
    self_ok:Unit <- Suite.application_absent(self,"self-referencing local alias accepted")
    absent:Maybe<&2,F.Term.t> <- I.Inline.local_alias(Nil{},0n,0n)
    absent_ok:Unit <- Suite.application_absent(absent,"missing local alias unfolded")
    loop:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{F.Term.Global{"Cycle"}},F.Term.APt{F.Quantity.Many{},F.Term.Global{"Nat"}},context)
    Suite.application_absent(loop,"cyclic alias accepted")

def Suite.lambda_absent(state:R.Erase.State<Maybe<&2,F.Pair2<I.Inline.context,F.Term.t>>>,label:String) -> Result<&2,&2,F.Error.t,Unit>:
  match state:
    case R.Erase.Return{None{}}: Done{Unit{}}
    case other: Fail{F.Error.Mismatch{label}}

def Suite.lambda_alias_refused(entry:F.Global.entry,label:String) -> Result<&2,&2,F.Error.t,Unit>:
  context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.add("Fn",entry,G.Global.initial),C.Budget.unlimited),Nil{}}
  leg:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"A"}],F.Term.Global{"Nat"}}
  Suite.lambda_absent(I.Inline.lambda_context_state(Some{F.Term.Global{"Fn"}},leg,context),label)

def Suite.lambda_alias_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  +univ:F.Term.t = F.Term.Univ{F.Level.one}
  do Result<&2,&2,F.Error.t,Unit>:
    opaque:Unit <- Suite.lambda_alias_refused(F.Global.Def{F.Global.DefEntry{univ,ty,False{},None{},False{}}},"opaque lambda alias unfolded")
    recursive:Unit <- Suite.lambda_alias_refused(F.Global.Def{F.Global.DefEntry{univ,ty,True{},Some{0n},False{}}},"recursive lambda alias unfolded")
    partial:Unit <- Suite.lambda_alias_refused(F.Global.Def{F.Global.DefEntry{univ,ty,True{},None{},True{}}},"partial lambda alias unfolded")
    free:Unit <- Suite.lambda_alias_refused(Suite.alias_entry(F.Term.Var{0n}),"free lambda alias accepted")
    missing:Unit <- Suite.lambda_alias_refused(Suite.alias_entry(F.Term.Global{"unknown"}),"missing lambda alias unfolded")
    cycle:Unit <- Suite.lambda_alias_refused(Suite.alias_entry(F.Term.Global{"Fn"}),"cyclic lambda alias accepted")
    axiom:Unit <- Suite.lambda_alias_refused(F.Global.Axiom{F.Global.AxiomEntry{univ}},"axiom lambda alias unfolded")
    computed:Unit <- Suite.lambda_absent(I.Inline.lambda_context_state(Some{F.Term.Ann{ty,F.Term.Var{0n}}},F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"A"}],F.Term.Global{"Nat"}},I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}),"open annotation acquired a lambda context")
    Suite.lambda_alias_refused(Suite.alias_entry(F.Term.Ran{F.Shape.make_collection(F.Term.t,1n),F.Term.Global{"Nat"}}),"nonpoint lambda alias acquired a context")

def Suite.lambda_alias_scope_result(state:R.Erase.State<Maybe<&2,F.Pair2<I.Inline.context,F.Term.t>>>,expected:F.Term.t) -> Result<&2,&2,F.Error.t,Unit>:
  match state:
    case R.Erase.Return{Some{F.Pair2{I.Inline.Context{C.Check.Ctx{globals,env,Con{F.Triple3{name,q,ty},Nil{}},size,budget},I.Inline.Param{local,domain} <> Nil{}},codomain}}}:
      do Result<&2,&2,F.Error.t,Unit>:
        scope:Unit <- T.Test.require(Bool.and(Nat.is_eq(size,1n),Bool.and(String.eq(name,"Item"),Bool.and(String.eq(local,"Item"),F.Quantity.equal(q,F.Quantity.Zero{})))),"lambda alias binder context changed")
        source:Unit <- T.Test.require(I.Inline.term_equal(domain,F.Term.Univ{F.Level.zero}),"lambda alias domain syntax changed")
        T.Test.require(I.Inline.term_equal(codomain,expected),"lambda alias codomain syntax changed")
    case other: Fail{F.Error.Mismatch{"lambda alias context missing"}}

def Suite.lambda_alias_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +codomain:F.Term.t = F.Term.Ann{F.Term.Var{0n},F.Term.Univ{F.Level.zero}}
  ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),codomain}
  globals:F.Global.t = F.Global.add("Fn",Suite.alias_entry(ty),F.Global.add("Alias",Suite.alias_entry(F.Term.Global{"Fn"}),F.Global.empty))
  context:I.Inline.context = I.Inline.Context{C.Check.make(globals,C.Budget.unlimited),Nil{}}
  leg:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"Item"}],F.Term.Var{0n}}
  Suite.lambda_alias_scope_result(I.Inline.lambda_context_state(Some{F.Term.Global{"Alias"}},leg,context),codomain)

def Suite.let_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  # Only source recovery runs here; size records the two outer variables.
  +context:I.Inline.context = I.Inline.Context{C.Check.Ctx{F.Global.empty,Nil{},Nil{},2n,C.Budget.unlimited},Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  value:F.Term.t = F.Term.Ann{F.Term.Var{1n},univ}
  body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Ann{F.Term.Var{3n},univ}}
  +ty:F.Term.t = F.Term.Let{"A",univ,value,body}
  expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{ty},context)
    syntax:Unit <- Suite.application_equal(actual,expected)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{ty},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})

def Suite.let_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.one}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  cycle:F.Global.entry = Suite.alias_entry(F.Term.Let{"T",univ,F.Term.Global{"Cycle"},F.Term.Var{0n}})
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.add("Cycle",cycle,F.Global.empty),C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    annotation:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Let{"T",F.Term.Var{0n},ty,F.Term.Var{0n}}},context)
    annotation_ok:Unit <- Suite.application_absent(annotation,"free let annotation accepted")
    value:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Let{"T",univ,F.Term.Var{0n},ty}},context)
    value_ok:Unit <- Suite.application_absent(value,"free unused let value accepted")
    body:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Let{"T",univ,ty,F.Term.Var{1n}}},context)
    body_ok:Unit <- Suite.application_absent(body,"free let body accepted")
    loop:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Global{"Cycle"}},context)
    Suite.application_absent(loop,"let alias cycle accepted")

def Suite.let_chain(count:Nat,+ty:F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n: F.Term.Let{"T",F.Term.Univ{F.Level.one},Suite.let_chain(n,ty),F.Term.Var{0n}}

def Suite.let_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(64n,ty)},context)
    exact_ok:Unit <- Suite.application_equal(exact,ty)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(65n,ty)},context)
    over_ok:Unit <- Suite.application_absent(over,"let reduction bound exceeded")
    zero:Maybe<&2,F.Term.t> <- I.Inline.source_let_type(0n,Some{ty},context)
    zero_ok:Unit <- Suite.application_equal(zero,ty)
    exhausted:Maybe<&2,F.Term.t> <- I.Inline.source_let_type(0n,Some{Suite.let_chain(1n,ty)},context)
    Suite.application_absent(exhausted,"exhausted let fuel accepted")

def Suite.lambda_let_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +codomain:F.Term.t = F.Term.Ann{F.Term.Var{0n},F.Term.Univ{F.Level.zero}}
  ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),codomain}
  expected:F.Term.t = F.Term.Let{"T",F.Term.Univ{F.Level.one},ty,F.Term.Var{0n}}
  context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  leg:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"Item"}],F.Term.Var{0n}}
  Suite.lambda_alias_scope_result(I.Inline.lambda_context_state(Some{expected},leg,context),codomain)

def Suite.plain_motive_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +scrut:F.Term.t = F.Term.Ann{F.Term.Global{"unknown"},F.Term.Global{"Nat"}}
  do Result<&2,&2,F.Error.t,Unit>:
    indices:Unit <- Suite.branch_absent_as(I.Inline.motive_context_state(shape,scrut,None{},["k"],"self",context),"plain motive index names acquired a context")
    inductive:Unit <- Suite.branch_absent_as(I.Inline.motive_context_state(F.Shape.make_inductive(F.Term.t,"Box",Nil{}),scrut,None{},Nil{},"self",context),"plain motive inductive shape acquired a context")
    missing_global:Unit <- Suite.branch_absent_as(I.Inline.motive_context_state(shape,F.Term.Global{"unknown"},None{},Nil{},"self",context),"plain motive missing global acquired a context")
    missing_local:Unit <- Suite.branch_absent_as(I.Inline.motive_context_state(shape,F.Term.Var{0n},None{},Nil{},"self",context),"plain motive missing local acquired a context")
    unavailable:Unit <- Suite.branch_absent_as(I.Inline.motive_context_state(shape,F.Term.Univ{F.Level.one},None{},Nil{},"self",context),"plain motive unavailable source type acquired a context")
    Suite.branch_absent_as(I.Inline.motive_context_state(shape,F.Term.Ann{F.Term.Global{"unknown"},F.Term.Var{0n}},None{},Nil{},"self",context),"plain motive free annotation acquired a context")

# The source type is not Nat, so a hardcoded Nat domain fails. The checker
# entry type is quoted and compared too, not only the Inline parameter.
def Suite.plain_motive_scope(scope:Maybe<&2,I.Inline.context>,+expected:F.Term.t) -> Result<&2,&2,F.Error.t,Unit>:
  match scope:
    case Some{I.Inline.Context{C.Check.Ctx{globals,env,Con{F.Triple3{self,quantity,ty},Nil{}},size,budget},Con{I.Inline.Param{name,domain},Nil{}}}}:
      do Result<&2,&2,F.Error.t,Unit>:
        checked:F.Term.t <- V.Eval.quote(globals,0n,ty)
        T.Test.require(Bool.and(Nat.is_eq(size,1n),Bool.and(String.eq(self,"self"),Bool.and(String.eq(name,"self"),Bool.and(I.Inline.term_equal(domain,expected),Bool.and(I.Inline.term_equal(checked,expected),F.Quantity.equal(quantity,F.Quantity.Zero{})))))),"plain motive self lost its source type or erased quantity")
    case other: Fail{F.Error.Mismatch{"plain motive binder context missing"}}

def Suite.plain_motive_quantity() -> Result<&2,&2,F.Error.t,Unit>:
  context:I.Inline.context = I.Inline.Context{C.Check.make(G.Global.initial,C.Budget.unlimited),Nil{}}
  +source:F.Term.t = F.Term.Univ{F.Level.zero}
  scrut:F.Term.t = F.Term.Ann{F.Term.Global{"unknown"},source}
  do Result<&2,&2,F.Error.t,Unit>:
    scope:Maybe<&2,I.Inline.context> <- R.Erase.State.finish(Maybe<&2,I.Inline.context>,I.Inline.motive_context_state(F.Shape.make_collection(F.Term.t,2n),scrut,None{},Nil{},"self",context),C.Budget.unlimited)
    Suite.plain_motive_scope(scope,source)

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

def Suite.beta_term(argument:F.Term.t,body:F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",F.Term.Univ{F.Level.one})
  F.Term.Out{shape,F.Term.APt{F.Quantity.Zero{},argument},F.Term.Sec{shape,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],body}]}}

# The let reduces while its application is still pending.
def Suite.let_head(argument:F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",F.Term.Univ{F.Level.one})
  body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Univ{F.Level.zero}}
  function:F.Term.t = F.Term.Sec{shape,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],body}]}
  F.Term.Out{shape,F.Term.APt{F.Quantity.Zero{},argument},F.Term.Let{"F",F.Term.Univ{F.Level.one},function,F.Term.Var{0n}}}

def Suite.projection_pair(index: Nat, first: F.Term.t, second: F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  F.Term.Out{shape,F.Term.ALeg{index},F.Term.Sec{shape,[F.Term.Leg{Nil{},first},F.Term.Leg{Nil{},second}]}}

def Suite.projection_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.Ctx{F.Global.empty,Nil{},Nil{},2n,C.Budget.unlimited},Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",univ)
  identity:F.Term.t = F.Term.Sec{point,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],F.Term.Var{0n}}]}
  do Result<&2,&2,F.Error.t,Unit>:
    first:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(0n,ty,univ)},context)
    first_ok:Unit <- Suite.application_equal(first,ty)
    last:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(1n,univ,ty)},context)
    last_ok:Unit <- Suite.application_equal(last,ty)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{Suite.projection_pair(1n,univ,ty)},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    applied_ok:Unit <- Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})
    pending:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Out{point,F.Term.APt{F.Quantity.Zero{},ty},Suite.projection_pair(1n,univ,identity)}},context)
    Suite.application_equal(pending,ty)

def Suite.projection_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +one:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,1n)
  +two:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",univ)
  +head:F.Term.t = F.Term.Sec{one,[F.Term.Leg{Nil{},univ}]}
  do Result<&2,&2,F.Error.t,Unit>:
    width:Maybe<&2,F.Term.t> <- I.Inline.beta_type(one,F.Term.ALeg{0n},Some{F.Term.Sec{two,[F.Term.Leg{Nil{},univ}]}},0n)
    width_ok:Unit <- Suite.application_absent(width,"projection shape mismatch accepted")
    short:Maybe<&2,F.Term.t> <- I.Inline.beta_type(two,F.Term.ALeg{0n},Some{F.Term.Sec{two,[F.Term.Leg{Nil{},univ}]}},0n)
    short_ok:Unit <- Suite.application_absent(short,"short projection tuple accepted")
    long:Maybe<&2,F.Term.t> <- I.Inline.beta_type(one,F.Term.ALeg{0n},Some{F.Term.Sec{one,[F.Term.Leg{Nil{},univ},F.Term.Leg{Nil{},univ}]}},0n)
    long_ok:Unit <- Suite.application_absent(long,"long projection tuple accepted")
    shape:Maybe<&2,F.Term.t> <- I.Inline.beta_type(point,F.Term.ALeg{0n},Some{head},0n)
    shape_ok:Unit <- Suite.application_absent(shape,"point projection shape accepted")
    section:Maybe<&2,F.Term.t> <- I.Inline.beta_type(one,F.Term.ALeg{0n},Some{F.Term.Sec{point,[F.Term.Leg{Nil{},univ}]}},0n)
    section_ok:Unit <- Suite.application_absent(section,"point projection section accepted")
    index:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(2n,univ,univ)},context)
    index_ok:Unit <- Suite.application_absent(index,"out of range projection accepted")
    empty:Maybe<&2,F.Term.t> <- I.Inline.beta_type(F.Shape.make_collection(F.Term.t,0n),F.Term.ALeg{0n},Some{F.Term.Sec{F.Shape.make_collection(F.Term.t,0n),Nil{}}},0n)
    empty_ok:Unit <- Suite.application_absent(empty,"empty projection accepted")
    selected:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(0n,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),univ},univ)},context)
    selected_ok:Unit <- Suite.application_absent(selected,"free selected projection accepted")
    unused:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(0n,univ,F.Term.Var{0n})},context)
    unused_ok:Unit <- Suite.application_absent(unused,"free unused projection accepted")
    binder:Maybe<&2,F.Term.t> <- I.Inline.beta_type(one,F.Term.ALeg{0n},Some{F.Term.Sec{one,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"x"}],univ}]}},0n)
    binder_ok:Unit <- Suite.application_absent(binder,"bound selected projection accepted")
    other_binder:Maybe<&2,F.Term.t> <- I.Inline.beta_type(two,F.Term.ALeg{0n},Some{F.Term.Sec{two,[F.Term.Leg{Nil{},univ},F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"x"}],univ}]}},0n)
    other_binder_ok:Unit <- Suite.application_absent(other_binder,"bound unused projection accepted")
    address:Maybe<&2,F.Term.t> <- I.Inline.beta_type(one,F.Term.ACtor{"field"},Some{head},0n)
    address_ok:Unit <- Suite.application_absent(address,"constructor projection address accepted")
    stuck:Maybe<&2,F.Term.t> <- I.Inline.beta_type(one,F.Term.ALeg{0n},Some{univ},0n)
    Suite.application_absent(stuck,"nonsection projection head accepted")

def Suite.projection_chain(count: Nat, ty: F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n: Suite.projection_pair(1n,F.Term.Univ{F.Level.zero},Suite.projection_chain(n,ty))

def Suite.projection_head_chain(count: Nat, ty: F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
      F.Term.Out{shape,F.Term.ALeg{1n},Suite.projection_head_chain(n,F.Term.Sec{shape,[F.Term.Leg{Nil{},F.Term.Univ{F.Level.zero}},F.Term.Leg{Nil{},ty}]})}

def Suite.annotation_chain(count: Nat, body: F.Term.t) -> F.Term.t:
  match count:
    case 0n: body
    case 1n+rest: F.Term.Ann{Suite.annotation_chain(rest,body),F.Term.Univ{F.Level.one}}

def Suite.annotation_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.Ctx{F.Global.empty,Nil{},Nil{},2n,C.Budget.unlimited},Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Ann{ty,F.Term.Var{0n}}},context)
    syntax:Unit <- Suite.application_equal(actual,ty)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{F.Term.Ann{ty,univ}},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})

def Suite.annotation_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  do Result<&2,&2,F.Error.t,Unit>:
    annotation:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Ann{ty,F.Term.Var{0n}}},context)
    annotation_ok:Unit <- Suite.application_absent(annotation,"free source annotation accepted")
    body:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Ann{F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Global{"Nat"}},F.Term.Univ{F.Level.zero}}},context)
    Suite.application_absent(body,"free annotated body accepted")

def Suite.beta_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.Ctx{F.Global.empty,Nil{},Nil{},2n,C.Budget.unlimited},Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  value:F.Term.t = F.Term.Ann{F.Term.Var{1n},univ}
  body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Ann{F.Term.Var{3n},univ}}
  +ty:F.Term.t = Suite.beta_term(value,body)
  expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{ty},context)
    syntax:Unit <- Suite.application_equal(actual,expected)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{ty},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    applied_ok:Unit <- Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})
    headed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_head(F.Term.Global{"Nat"})},context)
    Suite.application_equal(headed,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Global{"Nat"}),univ})

def Suite.beta_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",F.Term.Univ{F.Level.one})
  +free_shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",F.Term.Var{0n})
  +arg:F.Term.addr = F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}}
  +leg:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],F.Term.Var{0n}}
  +head:Maybe<&2,F.Term.t> = Some{F.Term.Sec{shape,[leg]}}
  do Result<&2,&2,F.Error.t,Unit>:
    argument:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.beta_term(F.Term.Var{0n},F.Term.Univ{F.Level.one})},context)
    argument_ok:Unit <- Suite.application_absent(argument,"free unused beta argument accepted")
    body:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.beta_term(F.Term.Global{"Nat"},F.Term.Var{1n})},context)
    body_ok:Unit <- Suite.application_absent(body,"free beta body accepted")
    domain:Maybe<&2,F.Term.t> <- I.Inline.beta_type(free_shape,arg,head,0n)
    domain_ok:Unit <- Suite.application_absent(domain,"free beta application domain accepted")
    parameter:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,arg,Some{F.Term.Sec{free_shape,[leg]}},0n)
    parameter_ok:Unit <- Suite.application_absent(parameter,"free beta section domain accepted")
    nonpoint:Maybe<&2,F.Term.t> <- I.Inline.beta_type(F.Shape.make_collection(F.Term.t,1n),arg,head,0n)
    nonpoint_ok:Unit <- Suite.application_absent(nonpoint,"nonpoint beta application accepted")
    section:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,arg,Some{F.Term.Sec{F.Shape.make_collection(F.Term.t,1n),[leg]}},0n)
    section_ok:Unit <- Suite.application_absent(section,"nonpoint beta section accepted")
    projection:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,F.Term.ALeg{0n},head,0n)
    projection_ok:Unit <- Suite.application_absent(projection,"beta projection accepted")
    quantity:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,F.Term.APt{F.Quantity.Many{},F.Term.Global{"Nat"}},head,0n)
    quantity_ok:Unit <- Suite.application_absent(quantity,"beta application quantity ignored")
    binder:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,arg,Some{F.Term.Sec{shape,[F.Term.Leg{[F.Pair2{F.Quantity.Many{},"T"}],F.Term.Var{0n}}]}},0n)
    binder_ok:Unit <- Suite.application_absent(binder,"beta binder quantity ignored")
    arity:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,arg,Some{F.Term.Sec{shape,[F.Term.Leg{Nil{},F.Term.Global{"Nat"}}]}},0n)
    arity_ok:Unit <- Suite.application_absent(arity,"beta binder arity ignored")
    binders:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,arg,Some{F.Term.Sec{shape,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"},F.Pair2{F.Quantity.Zero{},"U"}],F.Term.Var{0n}}]}},0n)
    binders_ok:Unit <- Suite.application_absent(binders,"beta binder count ignored")
    legs:Maybe<&2,F.Term.t> <- I.Inline.beta_type(shape,arg,Some{F.Term.Sec{shape,[leg,leg]}},0n)
    Suite.application_absent(legs,"beta section arity ignored")

def Suite.beta_chain(count:Nat,ty:F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n: Suite.beta_term(F.Term.Global{"Nat"},Suite.beta_chain(n,ty))

def Suite.beta_head_chain(count:Nat,body:F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",F.Term.Univ{F.Level.one})
  head:F.Term.t = Suite.beta_chain(count,F.Term.Sec{shape,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],body}]})
  F.Term.Out{shape,F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}},head}

def Suite.projection_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_chain(64n,ty)},context)
    exact_ok:Unit <- Suite.application_equal(exact,ty)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_chain(65n,ty)},context)
    over_ok:Unit <- Suite.application_absent(over,"projection reduction bound exceeded")
    heads:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_head_chain(64n,ty)},context)
    heads_ok:Unit <- Suite.application_equal(heads,ty)
    heads_over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_head_chain(65n,ty)},context)
    heads_over_ok:Unit <- Suite.application_absent(heads_over,"projection head reduction bound exceeded")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(16n,Suite.annotation_chain(16n,Suite.beta_chain(16n,Suite.projection_chain(16n,ty))))},context)
    mixed_ok:Unit <- Suite.application_equal(mixed,ty)
    mixed_over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(16n,Suite.annotation_chain(16n,Suite.beta_chain(16n,Suite.projection_chain(17n,ty))))},context)
    Suite.application_absent(mixed_over,"projection mixed reduction bound exceeded")

def Suite.annotation_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.annotation_chain(64n,ty)},context)
    exact_ok:Unit <- Suite.application_equal(exact,ty)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.annotation_chain(65n,ty)},context)
    over_ok:Unit <- Suite.application_absent(over,"annotation reduction bound exceeded")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(21n,Suite.annotation_chain(22n,Suite.beta_chain(21n,ty)))},context)
    mixed_ok:Unit <- Suite.application_equal(mixed,ty)
    mixed_over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(21n,Suite.annotation_chain(23n,Suite.beta_chain(21n,ty)))},context)
    Suite.application_absent(mixed_over,"annotation mixed reduction bound exceeded")

def Suite.beta_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}),F.Term.Var{0n}}
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.beta_chain(64n,ty)},context)
    exact_ok:Unit <- Suite.application_equal(exact,ty)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.beta_chain(65n,ty)},context)
    over_ok:Unit <- Suite.application_absent(over,"beta reduction bound exceeded")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(32n,Suite.beta_chain(32n,ty))},context)
    mixed_ok:Unit <- Suite.application_equal(mixed,ty)
    mixed_over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(32n,Suite.beta_chain(33n,ty))},context)
    mixed_over_ok:Unit <- Suite.application_absent(mixed_over,"mixed reduction bound exceeded")
    head:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.beta_head_chain(31n,Suite.beta_chain(32n,ty))},context)
    head_ok:Unit <- Suite.application_equal(head,ty)
    head_over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.beta_head_chain(32n,Suite.beta_chain(32n,ty))},context)
    Suite.application_absent(head_over,"beta function budget was reset")

def Suite.beta_source_cycles() -> Result<&2,&2,F.Error.t,Unit>:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",F.Term.Univ{F.Level.one})
  cycle:F.Term.t = F.Term.Out{shape,F.Term.APt{F.Quantity.Zero{},F.Term.Global{"Nat"}},F.Term.Global{"Cycle"}}
  globals:F.Global.t = F.Global.add("Cycle",Suite.alias_entry(cycle),F.Global.add("Body",Suite.alias_entry(Suite.beta_term(F.Term.Global{"Nat"},F.Term.Global{"Body"})),F.Global.empty))
  +context:I.Inline.context = I.Inline.Context{C.Check.make(globals,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    head:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Global{"Cycle"}},context)
    head_ok:Unit <- Suite.application_absent(head,"beta function cycle accepted")
    body:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Global{"Body"}},context)
    Suite.application_absent(body,"beta result cycle accepted")

# Each let value doubles the previous one. Without a size cap, recovery does
# exponential work within the step budget.
def Suite.size_chain(count:Nat) -> F.Term.t:
  match count:
    case 0n: F.Term.Var{0n}
    case 1n+n: F.Term.Let{"T",F.Term.Univ{F.Level.one},F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Var{1n}},Suite.size_chain(n)}

def Suite.source_size_bound() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +nat:F.Term.t = F.Term.Global{"Nat"}
  do Result<&2,&2,F.Error.t,Unit>:
    small:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Let{"T",F.Term.Univ{F.Level.one},nat,Suite.size_chain(1n)}},context)
    small_ok:Unit <- Suite.application_equal(small,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",nat),nat})
    large:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Let{"T",F.Term.Univ{F.Level.one},nat,Suite.size_chain(14n)}},context)
    Suite.application_absent(large,"source size cap ignored")

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
      Suite.Case{"branch-parameter",unit => Suite.local_sealed(PF.Fixture.branch_parameter,PF.Fixture.branch_parameter_opaque,layout,1n)},
      Suite.Case{"branch-parameter-dependent",unit => Suite.local_sealed(PF.Fixture.branch_parameter_dependent,PF.Fixture.branch_parameter_dependent_opaque,layout,1n)},
      Suite.Case{"branch-parameter-function",unit => Suite.local_sealed(PF.Fixture.branch_parameter_function,PF.Fixture.branch_parameter_function_opaque,layout,1n)},
      Suite.Case{"branch-parameter-annotated",unit => Suite.local_sealed(PF.Fixture.branch_parameter_annotated,PF.Fixture.branch_parameter_annotated_opaque,layout,1n)},
      Suite.Case{"branch-parameter-let",unit => Suite.local_sealed(PF.Fixture.branch_parameter_let,PF.Fixture.branch_parameter_let_opaque,layout,1n)},
      Suite.Case{"branch-parameter-global",unit => Suite.local_sealed(PF.Fixture.branch_parameter_global,PF.Fixture.branch_parameter_global_opaque,layout,1n)},
      Suite.Case{"branch-parameter-ctor",unit => Suite.parameter_ctors(layout)},
      Suite.Case{"branch-parameter-universe",unit => Suite.sealed_syntax(PF.Fixture.branch_parameter_universe,PF.Fixture.branch_parameter_universe_opaque,layout)},
      Suite.Case{"branch-parameter-guards",unit => Suite.parameter_guards},
      Suite.Case{"alias-leg-scope",unit => Suite.stays_inline(X.Fixture.alias_leg_scope,"unknown binder was confused with an outer binder")},
      Suite.Case{"branch-metadata",unit => Suite.branch_guards},
      Suite.Case{"branch-fallback",unit => Suite.branch_fallback},
      Suite.Case{"motive-index",unit => Suite.local_sealed(MF.Fixture.motive_index,MF.Fixture.motive_index_opaque,None{},1n)},
      Suite.Case{"motive-self",unit => Suite.local_sealed(MF.Fixture.motive_self,MF.Fixture.motive_self_opaque,None{},1n)},
      Suite.Case{"motive-dependent",unit => Suite.local_sealed(MF.Fixture.motive_dependent,MF.Fixture.motive_dependent_opaque,None{},1n)},
      Suite.Case{"motive-parameter",unit => Suite.local_sealed(MF.Fixture.motive_parameter,MF.Fixture.motive_parameter_opaque,None{},1n)},
      Suite.Case{"motive-parameter-indices",unit => Suite.local_sealed(MF.Fixture.motive_parameter_indices,MF.Fixture.motive_parameter_indices_opaque,None{},1n)},
      Suite.Case{"motive-guards",unit => Suite.motive_guards},
      Suite.Case{"motive-quantities",unit => Suite.motive_quantities},
      Suite.Case{"motive-plain-local",unit => Suite.local_sealed(MF.Fixture.motive_plain_local,MF.Fixture.motive_plain_local_opaque,None{},1n)},
      Suite.Case{"motive-plain-annotated",unit => Suite.local_sealed(MF.Fixture.motive_plain_annotated,MF.Fixture.motive_plain_annotated_opaque,None{},1n)},
      Suite.Case{"motive-plain-global",unit => Suite.local_sealed(MF.Fixture.motive_plain_global,MF.Fixture.motive_plain_global_opaque,None{},1n)},
      Suite.Case{"motive-plain-let",unit => Suite.local_sealed(MF.Fixture.motive_plain_let,MF.Fixture.motive_plain_let_opaque,None{},1n)},
      Suite.Case{"motive-plain-dependent",unit => Suite.local_sealed(MF.Fixture.motive_plain_dependent,MF.Fixture.motive_plain_dependent_opaque,None{},1n)},
      Suite.Case{"motive-plain-guards",unit => Suite.plain_motive_guards},
      Suite.Case{"motive-plain-quantity",unit => Suite.plain_motive_quantity},
      Suite.Case{"motive-application-global",unit => Suite.local_sealed(MF.Fixture.motive_application_global,MF.Fixture.motive_application_global_opaque,None{},1n)},
      Suite.Case{"motive-application-dependent",unit => Suite.local_sealed(MF.Fixture.motive_application_dependent,MF.Fixture.motive_application_dependent_opaque,None{},1n)},
      Suite.Case{"motive-application-local",unit => Suite.local_sealed(MF.Fixture.motive_application_local,MF.Fixture.motive_application_local_opaque,None{},1n)},
      Suite.Case{"motive-application-curried",unit => Suite.local_sealed(MF.Fixture.motive_application_curried,MF.Fixture.motive_application_curried_opaque,None{},1n)},
      Suite.Case{"application-capture",unit => Suite.application_capture},
      Suite.Case{"application-guards",unit => Suite.application_guards},
      Suite.Case{"alias-global",unit => Suite.alias_global},
      Suite.Case{"alias-local",unit => Suite.alias_local},
      Suite.Case{"alias-local-global",unit => Suite.alias_local_global},
      Suite.Case{"alias-fuel",unit => Suite.alias_fuel},
      Suite.Case{"alias-guards",unit => Suite.alias_guards},
      Suite.Case{"motive-alias-global",unit => Suite.local_sealed(MF.Fixture.motive_alias_global,MF.Fixture.motive_alias_global_opaque,None{},1n)},
      Suite.Case{"motive-alias-dependent",unit => Suite.local_sealed(MF.Fixture.motive_alias_dependent,MF.Fixture.motive_alias_dependent_opaque,None{},1n)},
      Suite.Case{"motive-alias-local",unit => Suite.local_sealed(MF.Fixture.motive_alias_local,MF.Fixture.motive_alias_local_opaque,None{},1n)},
      Suite.Case{"motive-alias-curried",unit => Suite.local_sealed(MF.Fixture.motive_alias_curried,MF.Fixture.motive_alias_curried_opaque,None{},1n)},
      Suite.Case{"lambda-alias-global",unit => Suite.local_sealed(LF.Fixture.lambda_alias_global,LF.Fixture.lambda_alias_global_opaque,layout,1n)},
      Suite.Case{"lambda-alias-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_alias_dependent,LF.Fixture.lambda_alias_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-alias-local",unit => Suite.local_sealed(LF.Fixture.lambda_alias_local,LF.Fixture.lambda_alias_local_opaque,layout,1n)},
      Suite.Case{"lambda-alias-curried",unit => Suite.local_sealed(LF.Fixture.lambda_alias_curried,LF.Fixture.lambda_alias_curried_opaque,layout,1n)},
      Suite.Case{"lambda-alias-guards",unit => Suite.lambda_alias_guards},
      Suite.Case{"lambda-alias-scope",unit => Suite.lambda_alias_scope},
      Suite.Case{"lambda-let-global",unit => Suite.local_sealed(LF.Fixture.lambda_let_global,LF.Fixture.lambda_let_global_opaque,layout,1n)},
      Suite.Case{"lambda-let-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_let_dependent,LF.Fixture.lambda_let_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-let-local",unit => Suite.local_sealed(LF.Fixture.lambda_let_local,LF.Fixture.lambda_let_local_opaque,layout,1n)},
      Suite.Case{"lambda-let-curried",unit => Suite.local_sealed(LF.Fixture.lambda_let_curried,LF.Fixture.lambda_let_curried_opaque,layout,1n)},
      Suite.Case{"motive-let-dependent",unit => Suite.local_sealed(MF.Fixture.motive_let_dependent,MF.Fixture.motive_let_dependent_opaque,None{},1n)},
      Suite.Case{"motive-let-curried",unit => Suite.local_sealed(MF.Fixture.motive_let_curried,MF.Fixture.motive_let_curried_opaque,None{},1n)},
      Suite.Case{"let-source-syntax",unit => Suite.let_source_syntax},
      Suite.Case{"let-source-guards",unit => Suite.let_source_guards},
      Suite.Case{"let-source-fuel",unit => Suite.let_source_fuel},
      Suite.Case{"lambda-let-scope",unit => Suite.lambda_let_scope},
      Suite.Case{"lambda-annotation-global",unit => Suite.local_sealed(LF.Fixture.lambda_annotation_global,LF.Fixture.lambda_annotation_global_opaque,layout,1n)},
      Suite.Case{"lambda-projection-global",unit => Suite.local_sealed(LF.Fixture.lambda_projection_global,LF.Fixture.lambda_projection_global_opaque,layout,1n)},
      Suite.Case{"lambda-projection-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_projection_dependent,LF.Fixture.lambda_projection_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-projection-local",unit => Suite.local_sealed(LF.Fixture.lambda_projection_local,LF.Fixture.lambda_projection_local_opaque,layout,1n)},
      Suite.Case{"lambda-projection-curried",unit => Suite.local_sealed(LF.Fixture.lambda_projection_curried,LF.Fixture.lambda_projection_curried_opaque,layout,1n)},
      Suite.Case{"lambda-annotation-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_annotation_dependent,LF.Fixture.lambda_annotation_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-annotation-local",unit => Suite.local_sealed(LF.Fixture.lambda_annotation_local,LF.Fixture.lambda_annotation_local_opaque,layout,1n)},
      Suite.Case{"lambda-annotation-curried",unit => Suite.local_sealed(LF.Fixture.lambda_annotation_curried,LF.Fixture.lambda_annotation_curried_opaque,layout,1n)},
      Suite.Case{"motive-annotation-dependent",unit => Suite.local_sealed(MF.Fixture.motive_annotation_dependent,MF.Fixture.motive_annotation_dependent_opaque,None{},1n)},
      Suite.Case{"motive-annotation-curried",unit => Suite.local_sealed(MF.Fixture.motive_annotation_curried,MF.Fixture.motive_annotation_curried_opaque,None{},1n)},
      Suite.Case{"annotation-source-syntax",unit => Suite.annotation_source_syntax},
      Suite.Case{"projection-source-syntax",unit => Suite.projection_source_syntax},
      Suite.Case{"projection-source-guards",unit => Suite.projection_source_guards},
      Suite.Case{"projection-source-fuel",unit => Suite.projection_source_fuel},
      Suite.Case{"annotation-source-guards",unit => Suite.annotation_source_guards},
      Suite.Case{"annotation-source-fuel",unit => Suite.annotation_source_fuel},
      Suite.Case{"beta-source-syntax",unit => Suite.beta_source_syntax},
      Suite.Case{"lambda-beta-global",unit => Suite.local_sealed(LF.Fixture.lambda_beta_global,LF.Fixture.lambda_beta_global_opaque,layout,1n)},
      Suite.Case{"lambda-beta-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_beta_dependent,LF.Fixture.lambda_beta_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-beta-local",unit => Suite.local_sealed(LF.Fixture.lambda_beta_local,LF.Fixture.lambda_beta_local_opaque,layout,1n)},
      Suite.Case{"lambda-beta-curried",unit => Suite.local_sealed(LF.Fixture.lambda_beta_curried,LF.Fixture.lambda_beta_curried_opaque,layout,1n)},
      Suite.Case{"motive-beta-dependent",unit => Suite.local_sealed(MF.Fixture.motive_beta_dependent,MF.Fixture.motive_beta_dependent_opaque,None{},1n)},
      Suite.Case{"motive-beta-curried",unit => Suite.local_sealed(MF.Fixture.motive_beta_curried,MF.Fixture.motive_beta_curried_opaque,None{},1n)},
      Suite.Case{"beta-source-guards",unit => Suite.beta_source_guards},
      Suite.Case{"beta-source-fuel",unit => Suite.beta_source_fuel},
      Suite.Case{"beta-source-cycles",unit => Suite.beta_source_cycles},
      Suite.Case{"source-size-bound",unit => Suite.source_size_bound} ]

def main() -> IO(Unit):
  +layout:Maybe<&2,F.Pair2<Bool,String>> = Some{F.Pair2{False{},"Layout"}}
  do IO<Unit>:
    summary:F.Pair2<Nat,List<&2,String>> <- Suite.run(Suite.cases(layout),0n,Nil{})
    Suite.finish(Suite.length(Suite.cases(layout),0n),summary)
