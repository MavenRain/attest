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

def Suite.index_alias_in(term:F.Term.t,index:F.Term.t) -> Result<&2,&2,F.Error.t,F.Term.t>:
  match term:
    case F.Term.In{shape,address,args}:
      do Result<&2,&2,F.Error.t,F.Term.t>:
        unit:Unit <- T.Test.require(Suite.family_name(shape,"Choice"),"index alias variant lost its constructor family")
        Done{F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",[index]),address,args}}
    case other: Fail{F.Error.Mismatch{"index alias variant lost its constructor"}}

def Suite.index_alias_local(term:F.Term.t) -> Result<&2,&2,F.Error.t,F.Term.t>:
  match term:
    case F.Term.Let{name,ty,value,F.Term.Let{pick,pick_ty,pick_value,body}}:
      do Result<&2,&2,F.Error.t,F.Term.t>:
        revised:F.Term.t <- Suite.index_alias_in(pick_value,F.Term.Var{0n})
        Done{F.Term.Let{name,ty,value,F.Term.Let{pick,pick_ty,revised,body}}}
    case other: Fail{F.Error.Mismatch{"index alias variant lost its local aliases"}}

def Suite.index_alias_body(local:Bool,body:F.Term.t) -> Result<&2,&2,F.Error.t,F.Term.t>:
  match local:
    case False{}: Suite.index_alias_in(body,F.Term.Global{"Index"})
    case True{}: Suite.index_alias_local(body)

def Suite.index_alias_entry(same:Bool,entry:F.Global.entry,old:F.Global.entry) -> F.Global.entry:
  match same:
    case False{}: old
    case True{}: entry

def Suite.index_alias_name(local:Bool) -> String:
  match local:
    case False{}: "Pick"
    case True{}: "Layout"

def Suite.index_alias_rows(rows:E.Elab.rows,+name:String,+entry:F.Global.entry) -> E.Elab.rows:
  match rows:
    case Nil{}: Nil{}
    case F.Pair2{+found,old} <> rest:
      replacement:F.Global.entry = Suite.index_alias_entry(String.eq(found,name),entry,old)
      F.Pair2{found,replacement} <> Suite.index_alias_rows(rest,name,entry)

def Suite.index_alias_variant(checked:E.Elab.checked,+local:Bool) -> Result<&2,&2,F.Error.t,E.Elab.checked>:
  F.Pair2{+globals,rows} = checked
  +name:String = Suite.index_alias_name(local)
  do Result<&2,&2,F.Error.t,E.Elab.checked>:
    +definition:F.Global.def_entry <- T.Test.definition(name,globals)
    +body:F.Term.t <- Suite.index_alias_body(local,T.Test.def_body(definition))
    changed:Unit <- T.Test.require(Bool.not(I.Inline.term_equal(body,T.Test.def_body(definition))),"index alias variant did not change the index spelling")
    +entry:F.Global.entry = T.Test.replace_body(definition,body)
    +revised:F.Global.t = F.Global.add(name,entry,globals)
    +revised_rows:E.Elab.rows = Suite.index_alias_rows(rows,name,entry)
    consistent:Unit <- T.Test.require(Suite.consistent(revised_rows,revised),"index alias variant rows differ")
    typed:Unit <- Suite.recheck(revised,name)
    keep:Unit <- Suite.recheck(revised,"keep")
    Done{F.Pair2{revised,revised_rows}}

def Suite.index_alias_sealed(+source:String,+twin:String,+host:Maybe<&2,F.Pair2<Bool,String>>,+expected:Nat,local:Bool) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    source_checked:Unit <- Suite.local_sealed(source,twin,host,expected)
    original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    +variant:E.Elab.checked <- Suite.index_alias_variant(original,local)
    +prepared:E.Elab.checked <- T.Test.prepare(variant)
    typed:Unit <- Suite.local_prepared(prepared,host)
    sealed:Unit <- Suite.sealed_count(prepared,expected)
    opaque:E.Elab.checked <- E.Elab.check_in(G.Global.initial,twin)
    before:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(variant)
    after:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(opaque)
    T.Test.require(String.eq(R.Erase.print(Suite.runtime_rows(before)),R.Erase.print(Suite.runtime_rows(after))),"index alias variant runtime differs from its sealed twin")

def Suite.sum_index_branch(mode:Nat) -> Nat:
  match mode:
    case 4n: 0n
    case other: 1n

def Suite.index_reduction_expression(mode:Nat,+term:F.Term.t) -> F.Term.t:
  match mode:
    case 0n: F.Term.Let{"n",F.Term.Global{"Nat"},term,F.Term.Var{0n}}
    case 1n:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Many{},"n",F.Term.Global{"Nat"})
      F.Term.Out{shape,F.Term.APt{F.Quantity.Many{},term},F.Term.Ann{F.Term.Sec{shape,[F.Term.Leg{[F.Pair2{F.Quantity.Many{},"n"}],F.Term.Var{0n}}]},F.Term.Ran{shape,F.Term.Global{"Nat"}}}}
    case 2n: F.Term.Ann{term,F.Term.Global{"Nat"}}
    case 3n:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
      tuple:F.Term.t = F.Term.Ann{F.Term.Sec{shape,[F.Term.Leg{Nil{},term},F.Term.Leg{Nil{},term}]},F.Term.Ran{shape,G.Rules.diagram_of([F.Term.Global{"Nat"},F.Term.Global{"Nat"}])}}
      F.Term.Out{shape,F.Term.ALeg{0n},tuple}
    case 6n:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"IndexBox",Nil{})
      F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{"zero"},Nil{}},F.Quantity.Many{},Some{F.Term.Motive{Some{"IndexBox"},Nil{},"box",F.Term.Global{"Nat"}}},[F.Pair2{F.Term.ACtor{"zero"},F.Term.Leg{Nil{},term}},F.Pair2{F.Term.ACtor{"value"},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"n"}],F.Term.Var{0n}}}]}}
    case 7n:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"IndexBox",Nil{})
      F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{"value"},[term]},F.Quantity.Many{},Some{F.Term.Motive{Some{"IndexBox"},Nil{},"box",F.Term.Global{"Nat"}}},[F.Pair2{F.Term.ACtor{"zero"},F.Term.Leg{Nil{},term}},F.Pair2{F.Term.ACtor{"value"},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"n"}],F.Term.Var{0n}}}]}}
    case other:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
      +nat:F.Term.t = F.Term.Global{"Nat"}
      +index:Nat = Suite.sum_index_branch(mode)
      scrutinee:F.Term.t = F.Term.Ann{F.Term.In{shape,F.Term.ALeg{index},[term]},F.Term.Lan{shape,G.Rules.diagram_of([nat,nat])}}
      +leg:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Many{},"n"}],F.Term.Var{0n}}
      F.Term.Elim{F.Term.Elimination{shape,scrutinee,F.Quantity.Many{},Some{F.Term.Motive{None{},Nil{},"choice",nat}},[F.Pair2{F.Term.ALeg{0n},leg},F.Pair2{F.Term.ALeg{1n},leg}]}}

def Suite.index_reduction_variant(checked:E.Elab.checked,mode:Nat) -> Result<&2,&2,F.Error.t,E.Elab.checked>:
  F.Pair2{+globals,rows} = checked
  do Result<&2,&2,F.Error.t,E.Elab.checked>:
    +definition:F.Global.def_entry <- T.Test.definition("Pick",globals)
    +body:F.Term.t <- Suite.index_alias_in(T.Test.def_body(definition),Suite.index_reduction_expression(mode,F.Term.Global{"Index"}))
    changed:Unit <- T.Test.require(Bool.not(I.Inline.term_equal(body,T.Test.def_body(definition))),"index reduction variant did not change the index spelling")
    +entry:F.Global.entry = T.Test.replace_body(definition,body)
    +revised:F.Global.t = F.Global.add("Pick",entry,globals)
    +revised_rows:E.Elab.rows = Suite.index_alias_rows(rows,"Pick",entry)
    consistent:Unit <- T.Test.require(Suite.consistent(revised_rows,revised),"index reduction variant rows differ")
    typed:Unit <- Suite.recheck(revised,"Pick")
    keep:Unit <- Suite.recheck(revised,"keep")
    Done{F.Pair2{revised,revised_rows}}

def Suite.index_reduction_sealed(+source:String,+twin:String,+host:Maybe<&2,F.Pair2<Bool,String>>,mode:Nat) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    source_checked:Unit <- Suite.local_sealed(source,twin,host,1n)
    original:E.Elab.checked <- E.Elab.check_in(G.Global.initial,source)
    +variant:E.Elab.checked <- Suite.index_reduction_variant(original,mode)
    +prepared:E.Elab.checked <- T.Test.prepare(variant)
    typed:Unit <- Suite.local_prepared(prepared,host)
    sealed:Unit <- Suite.sealed_count(prepared,1n)
    opaque:E.Elab.checked <- E.Elab.check_in(G.Global.initial,twin)
    before:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(variant)
    after:List<&2,F.Pair2<String,R.Erase.entry>> <- Suite.erase(opaque)
    T.Test.require(String.eq(R.Erase.print(Suite.runtime_rows(before)),R.Erase.print(Suite.runtime_rows(after))),"index reduction variant runtime differs from its sealed twin")

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

def Suite.case_pair(index: Nat, argument: F.Term.t, first: F.Term.t, second: F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +binder:F.Pair2<F.Quantity.t,String> = F.Pair2{F.Quantity.Many{},"payload"}
  F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ALeg{index},[argument]},F.Quantity.Many{},None{},[
    F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[binder],first}},
    F.Pair2{F.Term.ALeg{1n},F.Term.Leg{[binder],second}}]}}

def Suite.case_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.Ctx{F.Global.empty,Nil{},Nil{},2n,C.Budget.unlimited},Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{F.Term.Var{0n},univ}),F.Term.Ann{F.Term.Var{3n},univ}}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = [F.Pair2{F.Term.ALeg{1n},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"payload"}],body}},F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"payload"}],univ}}]
  do Result<&2,&2,F.Error.t,Unit>:
    first:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.case_pair(0n,F.Term.Var{1n},univ,body)},context)
    first_ok:Unit <- Suite.application_equal(first,univ)
    second:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.case_pair(1n,F.Term.Var{1n},univ,body)},context)
    second_ok:Unit <- Suite.application_equal(second,ty)
    reversed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ALeg{1n},[F.Term.Var{1n}]},F.Quantity.Many{},None{},branches}}},context)
    reversed_ok:Unit <- Suite.application_equal(reversed,ty)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{Suite.case_pair(1n,F.Term.Var{1n},univ,body)},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})

def Suite.case_refused(term:F.Term.t,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{term},context)
    Suite.application_absent(actual,message)

def Suite.case_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +one:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,1n)
  +two:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +binder:F.Pair2<F.Quantity.t,String> = F.Pair2{F.Quantity.Many{},"payload"}
  +leg:F.Term.leg = F.Term.Leg{[binder],univ}
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = [F.Pair2{F.Term.ALeg{0n},leg},F.Pair2{F.Term.ALeg{1n},leg}]
  +scrut:F.Term.t = F.Term.In{two,F.Term.ALeg{1n},[univ]}
  do Result<&2,&2,F.Error.t,Unit>:
    shape:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.In{one,F.Term.ALeg{1n},[univ]},F.Quantity.Many{},None{},branches}},"case shape mismatch accepted")
    short:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{1n},leg}] }},"short case branches accepted")
    duplicate:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{1n},leg},F.Pair2{F.Term.ALeg{1n},leg}]}},"duplicate case branch accepted")
    outside:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{2n},leg},F.Pair2{F.Term.ALeg{1n},leg}]}},"out-of-range case branch accepted")
    missing:Unit <- Suite.case_refused(Suite.case_pair(2n,univ,univ,univ),"missing case branch accepted")
    empty:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.In{two,F.Term.ALeg{1n},Nil{}},F.Quantity.Many{},None{},branches}},"empty case payload accepted")
    extra:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.In{two,F.Term.ALeg{1n},[univ,univ]},F.Quantity.Many{},None{},branches}},"extra case payload accepted")
    binder_count:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},F.Term.Leg{Nil{},univ}},F.Pair2{F.Term.ALeg{1n},leg}]}},"empty unused case binder accepted")
    extra_binder:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},leg},F.Pair2{F.Term.ALeg{1n},F.Term.Leg{[binder,binder],univ}}]}},"extra selected case binder accepted")
    extra_unused_binder:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[binder,binder],univ}},F.Pair2{F.Term.ALeg{1n},leg}]}},"extra unused case binder accepted")
    named:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"ctor"},leg},F.Pair2{F.Term.ALeg{1n},leg}]}},"named case branch accepted")
    named_motive:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{Some{"Named"},Nil{},"self",univ}},branches}},"named case motive accepted")
    indexed_motive:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{None{},["index"],"self",univ}},branches}},"indexed case motive accepted")
    Suite.case_refused(F.Term.Elim{F.Term.Elimination{F.Shape.make_point(F.Term.t,F.Quantity.Many{},"x",univ),scrut,F.Quantity.Many{},None{},branches}},"point case shape accepted")

def Suite.case_source_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +two:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +leg:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Many{},"payload"}],univ}
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = [F.Pair2{F.Term.ALeg{0n},leg},F.Pair2{F.Term.ALeg{1n},leg}]
  +scrut:F.Term.t = F.Term.In{two,F.Term.ALeg{1n},[univ]}
  do Result<&2,&2,F.Error.t,Unit>:
    unused:Unit <- Suite.case_refused(Suite.case_pair(1n,univ,F.Term.Var{1n},univ),"free unused case branch accepted")
    selected:Unit <- Suite.case_refused(Suite.case_pair(1n,univ,univ,F.Term.Var{1n}),"free selected case branch accepted")
    payload:Unit <- Suite.case_refused(Suite.case_pair(1n,F.Term.Var{0n},univ,univ),"free case payload accepted")
    annotation:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.Ann{scrut,F.Term.Var{0n}},F.Quantity.Many{},None{},branches}},"free case scrutinee annotation accepted")
    motive:Unit <- Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{None{},Nil{},"self",F.Term.Var{1n}}},branches}},"free case motive accepted")
    Suite.case_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.Global{"unknown"},F.Quantity.Many{},None{},branches}},"neutral case scrutinee accepted")

def Suite.case_chain(count:Nat,ty:F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n: Suite.case_pair(1n,Suite.case_chain(n,ty),F.Term.Univ{F.Level.zero},F.Term.Var{0n})

def Suite.case_result_chain(count:Nat,ty:F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n: Suite.case_pair(1n,F.Term.Univ{F.Level.zero},F.Term.Univ{F.Level.zero},Suite.case_result_chain(n,ty))

def Suite.case_head_chain(count:Nat,ty:F.Term.t) -> F.Term.t:
  match count:
    case 0n: ty
    case 1n+n:
      +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,1n)
      injection:F.Term.t = F.Term.In{shape,F.Term.ALeg{0n},[ty]}
      F.Term.Elim{F.Term.Elimination{shape,Suite.case_head_chain(n,injection),F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"payload"}],F.Term.Var{0n}}}]}}

def Suite.case_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +ty:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.case_chain(64n,ty)},context)
    exact_ok:Unit <- Suite.application_equal(exact,ty)
    over:Unit <- Suite.case_refused(Suite.case_chain(65n,ty),"case reduction bound exceeded")
    results:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.case_result_chain(64n,ty)},context)
    results_ok:Unit <- Suite.application_equal(results,ty)
    results_over:Unit <- Suite.case_refused(Suite.case_result_chain(65n,ty),"case result reduction bound exceeded")
    heads:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.case_head_chain(64n,ty)},context)
    heads_ok:Unit <- Suite.application_equal(heads,ty)
    heads_over:Unit <- Suite.case_refused(Suite.case_head_chain(65n,ty),"case head reduction bound exceeded")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(16n,Suite.beta_chain(16n,Suite.projection_chain(16n,Suite.case_chain(16n,ty))))},context)
    mixed_ok:Unit <- Suite.application_equal(mixed,ty)
    Suite.case_refused(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.projection_chain(16n,Suite.case_chain(17n,ty)))),"mixed case reduction bound exceeded")

def Suite.case_source_pending() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = I.Inline.Context{C.Check.make(F.Global.empty,C.Budget.unlimited),Nil{}}
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",univ)
  +identity:F.Term.t = F.Term.Sec{point,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],F.Term.Var{0n}}]}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  scrut:F.Term.t = F.Term.In{shape,F.Term.ALeg{1n},[univ]}
  do Result<&2,&2,F.Error.t,Unit>:
    application:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Out{point,F.Term.APt{F.Quantity.Zero{},univ},Suite.case_pair(1n,identity,univ,F.Term.Var{0n})}},context)
    application_ok:Unit <- Suite.application_equal(application,univ)
    projection:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(1n,univ,Suite.case_pair(1n,univ,univ,F.Term.Var{0n}))},context)
    projection_ok:Unit <- Suite.application_equal(projection,univ)
    recovered:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Elim{F.Term.Elimination{shape,Suite.projection_pair(1n,univ,F.Term.Out{point,F.Term.APt{F.Quantity.Zero{},scrut},identity}),F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"x"}],univ}},F.Pair2{F.Term.ALeg{1n},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"x"}],F.Term.Var{0n}}}]}}},context)
    Suite.application_equal(recovered,univ)

def Suite.constructor_family() -> F.Positivity.family:
  F.Positivity.Family{"Choice",Nil{},Nil{},F.Level.one,F.Positivity.Complete{["empty","pair"]},[
    F.Positivity.Ctor{"empty",Nil{},Nil{},0n,False{}},
    F.Positivity.Ctor{"pair",[F.Triple3{F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}},F.Triple3{F.Quantity.Zero{},"x",F.Term.Var{0n}}],Nil{},2n,False{}}],True{}}

def Suite.constructor_context(depth:Nat) -> I.Inline.context:
  globals:F.Global.t = F.Global.add_family("Choice",Suite.constructor_family,F.Global.empty)
  I.Inline.Context{C.Check.Ctx{globals,Nil{},Nil{},depth,C.Budget.unlimited},Nil{}}

def Suite.constructor_branches(empty:F.Term.t,body:F.Term.t) -> List<&2,F.Pair2<F.Term.addr,F.Term.leg>>:
  [F.Pair2{F.Term.ACtor{"empty"},F.Term.Leg{Nil{},empty}},F.Pair2{F.Term.ACtor{"pair"},F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"A"},F.Pair2{F.Quantity.Zero{},"x"}],body}}]

def Suite.constructor_term(name:String,args:List<&2,F.Term.t>,empty:F.Term.t,body:F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{name},args},F.Quantity.Many{},None{},Suite.constructor_branches(empty,body)}}

def Suite.constructor_absent(term:F.Term.t,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{term},Suite.constructor_context(0n))
    Suite.application_absent(actual,message)

def Suite.constructor_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = Suite.constructor_context(2n)
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +args:List<&2,F.Term.t> = [F.Term.Var{1n},F.Term.Var{0n}]
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{4n},univ}}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  do Result<&2,&2,F.Error.t,Unit>:
    first:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("pair",args,univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Var{1n}),univ})},context)
    first_ok:Unit <- Suite.application_equal(first,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Var{1n}),univ})
    second:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("pair",args,univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Var{0n}),univ})},context)
    second_ok:Unit <- Suite.application_equal(second,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Var{0n}),univ})
    empty:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("empty",Nil{},univ,F.Term.Var{0n})},context)
    empty_ok:Unit <- Suite.application_equal(empty,univ)
    syntax:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("pair",args,univ,body)},context)
    syntax_ok:Unit <- Suite.application_equal(syntax,ty)
    reversed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{"pair"},args},F.Quantity.Many{},Some{F.Term.Motive{Some{"Choice"},Nil{},"self",univ}},I.Inline.reverse(F.Pair2<F.Term.addr,F.Term.leg>,Suite.constructor_branches(univ,body),Nil{})}}},context)
    reversed_ok:Unit <- Suite.application_equal(reversed,ty)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{Suite.constructor_term("pair",args,univ,body)},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})

def Suite.constructor_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  +scrut:F.Term.t = F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]}
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = Suite.constructor_branches(univ,univ)
  +pair:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"A"},F.Pair2{F.Quantity.Zero{},"x"}],univ}
  +empty:F.Term.leg = F.Term.Leg{Nil{},univ}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.constructor_absent(Suite.constructor_term("missing",[univ,univ],univ,univ),"unknown constructor accepted")
    short:Unit <- Suite.constructor_absent(Suite.constructor_term("pair",[univ],univ,univ),"short constructor accepted")
    long:Unit <- Suite.constructor_absent(Suite.constructor_term("pair",[univ,univ,univ],univ,univ),"long constructor accepted")
    shape_ok:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{F.Shape.make_inductive(F.Term.t,"Other",Nil{}),F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},None{},branches}},"constructor shape mismatch accepted")
    index:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",[univ]),F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},None{},branches}},"constructor index accepted")
    duplicate:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"pair"},pair},F.Pair2{F.Term.ACtor{"pair"},pair}]}},"duplicate constructor branch accepted")
    coverage:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"pair"},pair}]}},"missing constructor branch accepted")
    unknown:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"unknown"},empty},F.Pair2{F.Term.ACtor{"pair"},pair}]}},"unknown branch accepted")
    address:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},empty},F.Pair2{F.Term.ACtor{"pair"},pair}]}},"numeric constructor branch accepted")
    arity:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"empty"},empty},F.Pair2{F.Term.ACtor{"pair"},empty}]}},"constructor branch arity accepted")
    quantity:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"empty"},empty},F.Pair2{F.Term.ACtor{"pair"},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"A"},F.Pair2{F.Quantity.Zero{},"x"}],univ}}]}},"constructor binder quantity accepted")
    motive:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},Some{F.Term.Motive{Some{"Other"},Nil{},"self",univ}},branches}},"constructor motive family accepted")
    motive_index:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},Some{F.Term.Motive{None{},["index"],"self",univ}},branches}},"constructor motive index accepted")
    shape_index:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{F.Shape.make_inductive(F.Term.t,"Choice",[univ]),scrut,F.Quantity.Many{},None{},branches}},"constructor elimination index accepted")
    named_motive_index:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},Some{F.Term.Motive{Some{"Choice"},["index"],"self",univ}},branches}},"constructor named motive index accepted")
    Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,F.Term.Global{"neutral"},F.Quantity.Many{},None{},branches}},"neutral constructor scrutinee accepted")

def Suite.constructor_metadata_absent(family:Maybe<&2,F.Positivity.family>,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.constructor_family(family,"Choice","pair",[univ,univ],Suite.constructor_branches(univ,univ),None{},0n,True{},0n)
    Suite.application_absent(actual,message)

def Suite.constructor_source_metadata(family:F.Positivity.family,+recursive:Bool) ->Result<&2,&2,F.Error.t,Unit>:
  F.Positivity.Family{name,params,indices,level,+status,+ctors,positive} = family
  +field:F.Triple3<F.Quantity.t,String,F.Term.t> = F.Triple3{F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}}
  +binders:List<&2,F.Pair2<F.Quantity.t,String>> = [F.Pair2{F.Quantity.Zero{},"A"}]
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.constructor_metadata_absent(None{},"missing constructor family accepted")
    name:Unit <- Suite.constructor_metadata_absent(Some{F.Positivity.Family{"Other",Nil{},Nil{},F.Level.one,status,ctors,True{}}},"wrong constructor family accepted")
    params:Unit <- Suite.constructor_metadata_absent(Some{F.Positivity.Family{"Choice",[field],Nil{},F.Level.one,status,ctors,True{}}},"constructor full arity omits parameters")
    indices:Unit <- Suite.constructor_metadata_absent(Some{F.Positivity.Family{"Choice",Nil{},[field],F.Level.one,status,ctors,True{}}},"indexed metadata mismatch accepted")
    positive:Unit <- Suite.constructor_metadata_absent(Some{F.Positivity.Family{"Choice",Nil{},Nil{},F.Level.one,status,ctors,False{}}},"nonpositive constructor family accepted")
    provisional:Unit <- Suite.constructor_metadata_absent(Some{F.Positivity.Family{"Choice",Nil{},Nil{},F.Level.one,F.Positivity.Provisional{},ctors,True{}}},"provisional constructor family accepted")
    builtin:Unit <- Suite.constructor_metadata_absent(Some{F.Positivity.Family{"Choice",Nil{},Nil{},F.Level.one,F.Positivity.Builtin{},ctors,True{}}},"builtin constructor family accepted")
    wellformed:Unit <- T.Test.require(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",[field],Nil{},1n,recursive}},binders,0n,0n),"well-formed constructor refused")
    arity:Unit <- T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",[field],Nil{},2n,recursive}},binders,0n,0n)),"constructor metadata arity accepted")
    indices:Unit <- T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",[field],[F.Term.Univ{F.Level.zero}],1n,recursive}},binders,0n,0n)),"constructor result index accepted")
    T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",[F.Triple3{F.Quantity.Zero{},"A",F.Term.Var{0n}}],Nil{},1n,recursive}},binders,0n,0n)),"open constructor field accepted")

def Suite.constructor_tree(count:Nat,leaf:F.Term.t) -> F.Term.t:
  match count:
    case 0n: leaf
    case 1n+n:
      +child:F.Term.t = Suite.constructor_tree(n,leaf)
      F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",child),child}

def Suite.constructor_source_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  do Result<&2,&2,F.Error.t,Unit>:
    unused:Unit <- Suite.constructor_absent(Suite.constructor_term("pair",[univ,univ],F.Term.Var{0n},univ),"open unused constructor branch accepted")
    body:Unit <- Suite.constructor_absent(Suite.constructor_term("pair",[univ,univ],univ,F.Term.Var{2n}),"open constructor body accepted")
    argument:Unit <- Suite.constructor_absent(Suite.constructor_term("pair",[univ,F.Term.Var{0n}],univ,univ),"open constructor argument accepted")
    motive:Unit <- Suite.constructor_absent(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},Some{F.Term.Motive{None{},Nil{},"self",F.Term.Var{1n}}},Suite.constructor_branches(univ,univ)}},"open constructor motive accepted")
    Suite.constructor_absent(Suite.constructor_term("pair",[Suite.constructor_tree(11n,univ),univ],univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{1n}),F.Term.Var{2n}}),"constructor size cap ignored")

def Suite.constructor_chain(count:Nat,body:F.Term.t) -> F.Term.t:
  match count:
    case 0n: body
    case 1n+n: Suite.constructor_term("pair",[F.Term.Univ{F.Level.zero},Suite.constructor_chain(n,body)],F.Term.Univ{F.Level.zero},F.Term.Var{0n})

def Suite.constructor_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.constructor_context(0n)
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_chain(64n,univ)},context)
    exact_ok:Unit <- Suite.application_equal(exact,univ)
    over:Unit <- Suite.constructor_absent(Suite.constructor_chain(65n,univ),"constructor reduction bound exceeded")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_chain(16n,Suite.constructor_chain(16n,univ))))},context)
    mixed_ok:Unit <- Suite.application_equal(mixed,univ)
    Suite.constructor_absent(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_chain(16n,Suite.constructor_chain(17n,univ)))),"mixed constructor reduction bound exceeded")

def Suite.constructor_source_pending() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.constructor_context(0n)
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",univ)
  +identity:F.Term.t = F.Term.Sec{point,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],F.Term.Var{0n}}]}
  do Result<&2,&2,F.Error.t,Unit>:
    head:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(32n,F.Term.Elim{F.Term.Elimination{shape,Suite.beta_chain(31n,F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]}),F.Quantity.Many{},None{},Suite.constructor_branches(univ,F.Term.Var{0n})}})},context)
    head_ok:Unit <- Suite.application_equal(head,univ)
    head_over:Unit <- Suite.constructor_absent(Suite.let_chain(32n,F.Term.Elim{F.Term.Elimination{shape,Suite.beta_chain(32n,F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]}),F.Quantity.Many{},None{},Suite.constructor_branches(univ,F.Term.Var{0n})}}),"constructor head budget reset")
    application:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{F.Term.Out{point,F.Term.APt{F.Quantity.Zero{},univ},Suite.constructor_term("pair",[univ,identity],univ,F.Term.Var{0n})}},context)
    application_ok:Unit <- Suite.application_equal(application,univ)
    projection:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.projection_pair(1n,univ,Suite.constructor_term("pair",[univ,univ],univ,F.Term.Var{0n}))},context)
    Suite.application_equal(projection,univ)

def Suite.constructor_parameter_ctors(ctors:List<&2,F.Positivity.ctor>) -> List<&2,F.Positivity.ctor>:
  match ctors:
    case Nil{}: Nil{}
    case F.Positivity.Ctor{name,fields,indices,arity,recursive} <> rest:
      F.Positivity.Ctor{name,fields,indices,(arity + 2n : Nat),recursive} <> Suite.constructor_parameter_ctors(rest)

def Suite.parameter_family(family:F.Positivity.family) -> F.Positivity.family:
  F.Positivity.Family{name,params,indices,level,status,ctors,positive} = family
  parameters:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"A",F.Term.Univ{F.Level.zero}},F.Triple3{F.Quantity.Zero{},"a",F.Term.Var{0n}}]
  F.Positivity.Family{name,parameters,indices,level,status,Suite.constructor_parameter_ctors(ctors),positive}

def Suite.parameter_context(depth:Nat) -> I.Inline.context:
  globals:F.Global.t = F.Global.add_family("Choice",Suite.parameter_family(Suite.constructor_family),F.Global.empty)
  I.Inline.Context{C.Check.Ctx{globals,Nil{},Nil{},depth,C.Budget.unlimited},Nil{}}

def Suite.parameter_term(parameters:List<&2,F.Term.t>,injected:List<&2,F.Term.t>,name:String,args:List<&2,F.Term.t>,empty:F.Term.t,body:F.Term.t) -> F.Term.t:
  shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",parameters)
  injection:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",injected)
  F.Term.Elim{F.Term.Elimination{shape,F.Term.In{injection,F.Term.ACtor{name},args},F.Quantity.Many{},Some{F.Term.Motive{Some{"Choice"},Nil{},"self",F.Term.Univ{F.Level.one}}},Suite.constructor_branches(empty,body)}}

def Suite.parameter_absent(term:F.Term.t,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{term},Suite.parameter_context(0n))
    Suite.application_absent(actual,message)

def Suite.parameter_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = Suite.parameter_context(2n)
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +args:List<&2,F.Term.t> = [F.Term.Var{0n},F.Term.Var{1n}]
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{4n},univ}}
  +expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{0n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.parameter_term(Nil{},Nil{},"pair",args,univ,body)},context)
    actual_ok:Unit <- Suite.application_equal(actual,expected)
    empty:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.parameter_term(Nil{},Nil{},"empty",Nil{},univ,body)},context)
    empty_ok:Unit <- Suite.application_equal(empty,univ)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{Suite.parameter_term(Nil{},Nil{},"pair",args,univ,body)},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})

def Suite.parameter_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +upper:F.Term.t = F.Term.Univ{F.Level.one}
  +parameters:List<&2,F.Term.t> = [univ,upper]
  +args:List<&2,F.Term.t> = [univ,univ]
  do Result<&2,&2,F.Error.t,Unit>:
    marker:Unit <- Suite.parameter_absent(Suite.parameter_term(parameters,Nil{},"pair",args,univ,univ),"constructor elimination payload accepted")
    injection:Unit <- Suite.parameter_absent(Suite.parameter_term(Nil{},parameters,"pair",args,univ,univ),"constructor injection indices accepted")
    Suite.parameter_absent(Suite.parameter_term(Nil{},Nil{},"pair",[univ],univ,univ),"parameter counted as constructor field")

def Suite.parameter_source_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    body:Unit <- Suite.parameter_absent(Suite.parameter_term(Nil{},Nil{},"pair",[univ,univ],univ,F.Term.Var{2n}),"parameters counted as branch binders")
    unused:Unit <- Suite.parameter_absent(Suite.parameter_term(Nil{},Nil{},"pair",[univ,univ],F.Term.Var{0n},univ),"open parameterized unused branch accepted")
    argument:Unit <- Suite.parameter_absent(Suite.parameter_term(Nil{},Nil{},"pair",[univ,F.Term.Var{0n}],univ,univ),"open parameterized field accepted")
    Suite.parameter_absent(Suite.parameter_term(Nil{},Nil{},"pair",[Suite.constructor_tree(11n,univ),univ],univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{1n}),F.Term.Var{2n}}),"parameterized constructor size cap ignored")

def Suite.parameter_chain(count:Nat,body:F.Term.t) -> F.Term.t:
  match count:
    case 0n: body
    case 1n+n:
      +univ:F.Term.t = F.Term.Univ{F.Level.zero}
      Suite.parameter_term(Nil{},Nil{},"pair",[univ,Suite.parameter_chain(n,body)],univ,F.Term.Var{0n})

def Suite.parameter_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.parameter_context(0n)
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.parameter_chain(64n,univ)},context)
    exact_ok:Unit <- Suite.application_equal(exact,univ)
    over:Unit <- Suite.parameter_absent(Suite.parameter_chain(65n,univ),"parameterized constructor reduction bound exceeded")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_chain(16n,Suite.parameter_chain(16n,univ))))},context)
    mixed_ok:Unit <- Suite.application_equal(mixed,univ)
    Suite.parameter_absent(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_chain(16n,Suite.parameter_chain(17n,univ)))),"mixed parameterized reduction bound exceeded")

def Suite.parameter_metadata_absent(family:F.Positivity.family,parameters:F.Positivity.telescope,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  F.Positivity.Family{name,params,indices,level,status,ctors,positive} = family
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.constructor_family(Some{F.Positivity.Family{name,parameters,indices,level,status,ctors,positive}},"Choice","pair",[univ,univ],Suite.constructor_branches(univ,univ),None{},0n,True{},2n)
    Suite.application_absent(actual,message)

def Suite.parameter_source_metadata() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    first:Unit <- Suite.parameter_metadata_absent(Suite.parameter_family(Suite.constructor_family),[F.Triple3{F.Quantity.Zero{},"A",F.Term.Var{0n}},F.Triple3{F.Quantity.Zero{},"a",F.Term.Var{0n}}],"open first constructor parameter type accepted")
    later:Unit <- Suite.parameter_metadata_absent(Suite.parameter_family(Suite.constructor_family),[F.Triple3{F.Quantity.Zero{},"A",univ},F.Triple3{F.Quantity.Zero{},"a",F.Term.Var{1n}}],"open later constructor parameter type accepted")
    field:Unit <- T.Test.require(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",[F.Triple3{F.Quantity.Zero{},"x",F.Term.Var{1n}}],Nil{},3n,False{}}},[F.Pair2{F.Quantity.Zero{},"x"}],2n,0n),"parameter-typed constructor field refused")
    T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",[F.Triple3{F.Quantity.Zero{},"x",F.Term.Var{2n}}],Nil{},3n,False{}}},[F.Pair2{F.Quantity.Zero{},"x"}],2n,0n)),"open parameterized constructor field accepted")

def Suite.parameter_introductions() -> Result<&2,&2,F.Error.t,Unit>:
  +prefix:String = "mu Packet (0 A : Type 0) (0 a : A) : Type 0 with\n| vacant : Packet A a\n| packet : (b : A) -> Packet A a\nmu Other (0 A : Type 0) : Type 0 with\n| other : Other A\nmu Witness (0 A : Type 0) : (0 x : A) -> Prop with\n| witness : (0 x : A) -> Witness A x\n"
  do Result<&2,&2,F.Error.t,Unit>:
    accepted:E.Elab.checked <- E.Elab.check_in(G.Global.initial,prefix ++ "def empty : Packet Nat 0 := vacant\ndef direct : Packet Nat 0 := packet 1\ndef consume : (p : Packet Nat 0) -> Nat := fun (p : Packet Nat 0) => 0\ndef argument : Nat := consume (packet 1)\ndef dependent : (0 A : Type 0) -> (0 a : A) -> (b : A) -> Packet A a := fun (0 A : Type 0) (0 a : A) (b : A) => packet b\ndef indexed : Witness Nat 0 := witness 0\n")
    family:Unit <- T.Test.fails_with(E.Elab.checked,E.Elab.check_in(G.Global.initial,prefix ++ "def bad : Other Nat := packet 1\n"),"constructor expected family differs","wrong constructor expected family accepted")
    arity:Unit <- T.Test.fails(E.Elab.checked,E.Elab.check_in(G.Global.initial,prefix ++ "def bad : Packet Nat 0 := packet\n"),"parameterized constructor arity ignored")
    field:Unit <- T.Test.fails(E.Elab.checked,E.Elab.check_in(G.Global.initial,prefix ++ "def bad : Packet Nat 0 := packet Nat\n"),"parameterized constructor field type ignored")
    expected:Unit <- T.Test.fails_with(E.Elab.checked,E.Elab.check_in(G.Global.initial,prefix ++ "def bad : Nat := packet 1\n"),"constructor expected an inductive family","nonfamily constructor expected type accepted")
    index:Unit <- T.Test.fails(E.Elab.checked,E.Elab.check_in(G.Global.initial,prefix ++ "def bad : Witness Nat 1 := witness 0\n"),"parameterized constructor result index ignored")
    T.Test.fails(E.Elab.checked,E.Elab.check_in(G.Global.initial,prefix ++ "def bad : Nat := case packet 1 as value in Packet return Nat with | vacant => 0 | packet b => b\n"),"parameterized constructor inferred without expected type")

def Suite.index_family() -> F.Positivity.family:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  params:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"P",univ},F.Triple3{F.Quantity.Zero{},"p",F.Term.Var{0n}}]
  F.Positivity.Family{"Choice",params,[F.Triple3{F.Quantity.Zero{},"A",univ},F.Triple3{F.Quantity.Zero{},"a",F.Term.Var{0n}}],F.Level.one,F.Positivity.Complete{["empty","pair"]},[
    F.Positivity.Ctor{"empty",Nil{},[F.Term.Var{1n},F.Term.Var{0n}],2n,False{}},
    F.Positivity.Ctor{"pair",[F.Triple3{F.Quantity.Zero{},"A",univ},F.Triple3{F.Quantity.Zero{},"x",F.Term.Var{0n}}],[F.Term.Var{1n},F.Term.Var{0n}],4n,False{}}],True{}}

def Suite.index_context(depth:Nat) -> I.Inline.context:
  globals:F.Global.t = F.Global.add_family("Choice",Suite.index_family,F.Global.empty)
  I.Inline.Context{C.Check.Ctx{globals,Nil{},Nil{},depth,C.Budget.unlimited},Nil{}}

def Suite.index_motive(names:List<&2,String>) -> Maybe<&2,F.Term.motive>:
  Some{F.Term.Motive{Some{"Choice"},names,"self",F.Term.Univ{F.Level.one}}}

def Suite.index_term(name:String,args:List<&2,F.Term.t>,empty:F.Term.t,body:F.Term.t,motive:Maybe<&2,F.Term.motive>) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",[F.Term.Univ{F.Level.zero},F.Term.Univ{F.Level.zero}])
  F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{name},args},F.Quantity.Many{},motive,Suite.constructor_branches(empty,body)}}

def Suite.index_absent(term:F.Term.t,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{term},Suite.index_context(0n))
    Suite.application_absent(actual,message)

def Suite.index_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +context:I.Inline.context = Suite.index_context(2n)
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +motive:Maybe<&2,F.Term.motive> = Suite.index_motive(["A","a"])
  +args:List<&2,F.Term.t> = [F.Term.Var{0n},F.Term.Var{1n}]
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{4n},univ}}
  +expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{0n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_term("pair",args,univ,body,motive)},context)
    actual_ok:Unit <- Suite.application_equal(actual,expected)
    empty:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_term("empty",Nil{},univ,body,motive)},context)
    empty_ok:Unit <- Suite.application_equal(empty,univ)
    applied:Maybe<&2,F.Term.t> <- I.Inline.application_source_type(Some{Suite.index_term("pair",args,univ,body,motive)},F.Term.APt{F.Quantity.Zero{},F.Term.Var{0n}},context)
    Suite.application_equal(applied,F.Term.Ann{F.Term.Var{1n},univ})

def Suite.index_source_motive() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +args:List<&2,F.Term.t> = [univ,univ]
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.index_absent(Suite.index_term("pair",args,univ,univ,None{}),"indexed missing motive accepted")
    short:Unit <- Suite.index_absent(Suite.index_term("pair",args,univ,univ,Suite.index_motive(["a"])),"indexed short motive accepted")
    extra:Unit <- Suite.index_absent(Suite.index_term("pair",args,univ,univ,Suite.index_motive(["A","a","b"])),"indexed extra motive accepted")
    unnamed:Unit <- Suite.index_absent(Suite.index_term("pair",args,univ,univ,Some{F.Term.Motive{None{},["A","a"],"self",univ}}),"indexed unnamed motive accepted")
    bare:Unit <- Suite.index_absent(Suite.index_term("pair",args,univ,univ,Some{F.Term.Motive{None{},Nil{},"self",univ}}),"indexed unnamed bare motive accepted")
    Suite.index_absent(Suite.index_term("pair",args,univ,univ,Some{F.Term.Motive{Some{"Other"},["A","a"],"self",univ}}),"indexed wrong motive family accepted")

def Suite.index_metadata_absent(family:F.Positivity.family,indices:F.Positivity.telescope,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  F.Positivity.Family{name,params,old,level,status,ctors,positive} = family
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.constructor_family(Some{F.Positivity.Family{name,params,indices,level,status,ctors,positive}},"Choice","pair",[univ,univ],Suite.constructor_branches(univ,univ),Suite.index_motive(["A","a"]),2n,True{},2n)
    Suite.application_absent(actual,message)

def Suite.index_source_metadata() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +binders:List<&2,F.Pair2<F.Quantity.t,String>> = [F.Pair2{F.Quantity.Zero{},"x"}]
  +fields:F.Positivity.telescope = [F.Triple3{F.Quantity.Zero{},"x",F.Term.Var{1n}}]
  do Result<&2,&2,F.Error.t,Unit>:
    first:Unit <- Suite.index_metadata_absent(Suite.index_family,[F.Triple3{F.Quantity.Zero{},"A",F.Term.Var{2n}},F.Triple3{F.Quantity.Zero{},"a",F.Term.Var{0n}}],"open first index accepted")
    later:Unit <- Suite.index_metadata_absent(Suite.index_family,[F.Triple3{F.Quantity.Zero{},"A",univ},F.Triple3{F.Quantity.Zero{},"a",F.Term.Var{3n}}],"open later index accepted")
    valid:Unit <- T.Test.require(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",fields,[F.Term.Var{2n},F.Term.Var{0n}],3n,False{}}},binders,2n,2n),"scoped result indices refused")
    missing:Unit <- T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",fields,[univ],3n,False{}}},binders,2n,2n)),"short result indices accepted")
    extra:Unit <- T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",fields,[univ,univ,univ],3n,False{}}},binders,2n,2n)),"extra result indices accepted")
    open:Unit <- T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",fields,[F.Term.Var{3n},univ],3n,False{}}},binders,2n,2n)),"open result index accepted")
    last:Unit <- T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",fields,[univ,F.Term.Var{3n}],3n,False{}}},binders,2n,2n)),"open later result index accepted")
    T.Test.require(Bool.not(I.Inline.constructor_fields(Some{F.Positivity.Ctor{"pair",fields,[univ,univ],5n,False{}}},binders,2n,2n)),"indices counted in constructor arity")

def Suite.index_shape_absent(indices:List<&2,F.Term.t>,values:List<&2,F.Term.t>,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",indices)
  injected:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",values)
  Suite.index_absent(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{injected,F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},Suite.index_motive(["A","a"]),Suite.constructor_branches(univ,univ)}},message)

def Suite.index_source_shapes() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +upper:F.Term.t = F.Term.Univ{F.Level.one}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.index_shape_absent(Nil{},Nil{},"indexed shape arity ignored")
    short:Unit <- Suite.index_shape_absent([univ],[univ],"indexed short shapes accepted")
    extra:Unit <- Suite.index_shape_absent([univ,univ,univ],[univ,univ,univ],"indexed extra shapes accepted")
    injection:Unit <- Suite.index_shape_absent([univ,univ],[univ],"indexed short injection shape accepted")
    prefix:Unit <- Suite.index_shape_absent([univ],[univ,univ],"indexed unequal shape arities accepted")
    unequal:Unit <- Suite.index_shape_absent([univ,univ],[upper,univ],"indexed shape values differ")
    tail:Unit <- Suite.index_shape_absent([univ,univ],[univ,upper],"indexed later shape values differ")
    definitional:Unit <- Suite.index_shape_absent([F.Term.Ann{upper,univ},univ],[univ,univ],"indexed unequal annotated shape values accepted")
    Suite.index_shape_absent([univ,F.Term.Var{0n}],[univ,F.Term.Var{0n}],"indexed open shape value accepted")

def Suite.index_source_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +motive:Maybe<&2,F.Term.motive> = Suite.index_motive(["A","a"])
  do Result<&2,&2,F.Error.t,Unit>:
    body:Unit <- Suite.index_absent(Suite.index_term("pair",[univ,univ],univ,F.Term.Var{2n},motive),"open indexed constructor body accepted")
    binders:Unit <- Suite.index_absent(F.Term.Elim{F.Term.Elimination{F.Shape.make_inductive(F.Term.t,"Choice",[univ,univ]),F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",[univ,univ]),F.Term.ACtor{"pair"},[univ,univ,univ,univ]},F.Quantity.Many{},motive,[F.Pair2{F.Term.ACtor{"empty"},F.Term.Leg{Nil{},univ}},F.Pair2{F.Term.ACtor{"pair"},F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"A"},F.Pair2{F.Quantity.Zero{},"x"},F.Pair2{F.Quantity.Zero{},"i"},F.Pair2{F.Quantity.Zero{},"j"}],F.Term.Var{3n}}}]}},"indices counted as branch binders")
    unused:Unit <- Suite.index_absent(Suite.index_term("pair",[univ,univ],F.Term.Var{0n},univ,motive),"open indexed unused branch accepted")
    short:Unit <- Suite.index_absent(Suite.index_term("pair",[univ],univ,univ,motive),"indexed short constructor accepted")
    argument:Unit <- Suite.index_absent(Suite.index_term("pair",[univ,F.Term.Var{0n}],univ,univ,motive),"open indexed field accepted")
    Suite.index_absent(Suite.index_term("pair",[Suite.constructor_tree(11n,univ),univ],univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{1n}),F.Term.Var{2n}},motive),"indexed constructor size cap ignored")

def Suite.index_chain(count:Nat,body:F.Term.t) -> F.Term.t:
  match count:
    case 0n: body
    case 1n+n:
      +univ:F.Term.t = F.Term.Univ{F.Level.zero}
      Suite.index_term("pair",[univ,Suite.index_chain(n,body)],univ,F.Term.Var{0n},Suite.index_motive(["A","a"]))

def Suite.index_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_context(0n)
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_chain(64n,univ)},context)
    exact_ok:Unit <- Suite.application_equal(exact,univ)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_chain(65n,univ)},context)
    Suite.application_absent(over,"indexed shared fuel exceeded")

def Suite.recursive_ctors(ctors:List<&2,F.Positivity.ctor>) -> List<&2,F.Positivity.ctor>:
  match ctors:
    case Nil{}: Nil{}
    case F.Positivity.Ctor{+name,fields,indices,arity,recursive} <> rest:
      F.Positivity.Ctor{name,fields,indices,arity,String.eq(name,"pair")} <> Suite.recursive_ctors(rest)

def Suite.recursive_family(family:F.Positivity.family) -> F.Positivity.family:
  F.Positivity.Family{name,params,indices,level,status,ctors,positive} = family
  F.Positivity.Family{name,params,indices,level,status,Suite.recursive_ctors(ctors),positive}

def Suite.recursive_context(family:F.Positivity.family,depth:Nat) -> I.Inline.context:
  globals:F.Global.t = F.Global.add_family("Choice",Suite.recursive_family(family),F.Global.empty)
  I.Inline.Context{C.Check.Ctx{globals,Nil{},Nil{},depth,C.Budget.unlimited},Nil{}}

def Suite.recursive_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.recursive_context(Suite.constructor_family,2n)
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{4n},univ}}
  +ty:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    selected:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("pair",[F.Term.Var{1n},F.Term.Var{0n}],univ,body)},context)
    selected_ok:Unit <- Suite.application_equal(selected,ty)
    unused:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("empty",Nil{},univ,body)},context)
    unused_ok:Unit <- Suite.application_equal(unused,univ)
    indexed:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_term("pair",[F.Term.Var{1n},F.Term.Var{0n}],univ,body,Suite.index_motive(["A","a"]))},Suite.recursive_context(Suite.index_family,2n))
    Suite.application_equal(indexed,ty)

def Suite.recursive_source_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.recursive_context(Suite.constructor_family,0n)
  do Result<&2,&2,F.Error.t,Unit>:
    unused:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("pair",[univ,univ],F.Term.Var{0n},univ)},context)
    unused_ok:Unit <- Suite.application_absent(unused,"open recursive unused branch accepted")
    selected:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.constructor_term("pair",[univ,univ],univ,F.Term.Var{2n})},context)
    Suite.application_absent(selected,"open recursive selected branch accepted")

def Suite.recursive_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.recursive_context(Suite.index_family,0n)
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_chain(64n,univ)},context)
    exact_ok:Unit <- Suite.application_equal(exact,univ)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_chain(65n,univ)},context)
    over_ok:Unit <- Suite.application_absent(over,"recursive shared fuel exceeded")
    ignored:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_term("pair",[univ,Suite.index_chain(64n,univ)],univ,univ,Suite.index_motive(["A","a"]))},context)
    Suite.application_equal(ignored,univ)

def Suite.index_alias_context(entry:F.Global.entry,locals:List<&2,I.Inline.local>,depth:Nat) -> I.Inline.context:
  globals:F.Global.t = F.Global.add("Index",entry,F.Global.add_family("Choice",Suite.index_family,F.Global.empty))
  I.Inline.Context{C.Check.Ctx{globals,Nil{},Nil{},depth,C.Budget.unlimited},locals}

def Suite.index_alias_term(indices:List<&2,F.Term.t>,values:List<&2,F.Term.t>,body:F.Term.t) -> F.Term.t:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  F.Term.Elim{F.Term.Elimination{F.Shape.make_inductive(F.Term.t,"Choice",indices),F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",values),F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},Suite.index_motive(["A","a"]),Suite.constructor_branches(univ,body)}}

def Suite.index_alias_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +neutral:F.Term.t = F.Term.Global{"Neutral"}
  +entry:F.Global.entry = F.Global.Def{F.Global.DefEntry{univ,neutral,True{},None{},False{}}}
  +context:I.Inline.context = Suite.index_alias_context(entry,Nil{},0n)
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{univ,F.Term.Univ{F.Level.one}}),F.Term.Univ{F.Level.zero}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[neutral,univ],body)},context)
    syntax:Unit <- Suite.application_equal(actual,body)
    reverse:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([neutral,univ],[F.Term.Global{"Index"},univ],body)},context)
    reverse_ok:Unit <- Suite.application_equal(reverse,body)
    tail:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([univ,F.Term.Global{"Index"}],[univ,neutral],body)},context)
    tail_ok:Unit <- Suite.application_equal(tail,body)
    unequal:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[neutral,F.Term.Univ{F.Level.one}],body)},context)
    unequal_ok:Unit <- Suite.application_absent(unequal,"later alias index differs")
    neutral_globals:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[F.Term.Global{"Other"},univ],body)},context)
    neutral_globals_ok:Unit <- Suite.application_absent(neutral_globals,"distinct neutral index globals accepted")
    short:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[neutral],body)},context)
    Suite.application_absent(short,"alias index widths differ")

def Suite.index_alias_source_local() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +entry:F.Global.entry = F.Global.Def{F.Global.DefEntry{univ,univ,True{},None{},False{}}}
  +locals:List<&2,I.Inline.local> = [I.Inline.Local{"alias",univ,F.Term.Var{0n}},I.Inline.Param{"outer",univ},I.Inline.Param{"older",univ}]
  +context:I.Inline.context = Suite.index_alias_context(entry,locals,3n)
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{3n}),F.Term.Var{5n}}
  +expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{1n}),F.Term.Var{3n}}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Var{0n},univ],[F.Term.Var{1n},univ],body)},context)
    shifted:Unit <- Suite.application_equal(actual,expected)
    parameter:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Var{1n},univ],[univ,univ],univ)},context)
    parameter_ok:Unit <- Suite.application_absent(parameter,"neutral index parameter unfolded")
    neutral_params:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Var{0n},univ],[F.Term.Var{2n},univ],univ)},context)
    neutral_params_ok:Unit <- Suite.application_absent(neutral_params,"distinct neutral index parameters accepted")
    open_context:I.Inline.context = Suite.index_alias_context(entry,[I.Inline.Local{"a",univ,F.Term.Var{1n}},I.Inline.Local{"b",univ,F.Term.Var{0n}}],2n)
    open:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Var{0n},univ],[F.Term.Var{1n},univ],univ)},open_context)
    Suite.application_absent(open,"open local index alias unfolded")

def Suite.index_alias_refused(entry:F.Global.entry,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[univ,univ],univ)},Suite.index_alias_context(entry,Nil{},0n))
    Suite.application_absent(actual,message)

def Suite.index_alias_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    opaque:Unit <- Suite.index_alias_refused(F.Global.Def{F.Global.DefEntry{univ,univ,False{},None{},False{}}},"opaque index alias unfolded")
    recursive:Unit <- Suite.index_alias_refused(F.Global.Def{F.Global.DefEntry{univ,univ,True{},Some{0n},False{}}},"recursive index alias unfolded")
    partial:Unit <- Suite.index_alias_refused(F.Global.Def{F.Global.DefEntry{univ,univ,True{},None{},True{}}},"partial index alias unfolded")
    open_global:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[F.Term.Var{0n},univ],univ)},Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,F.Term.Var{0n},True{},None{},False{}}},[I.Inline.Param{"p",univ}],1n))
    open:Unit <- Suite.application_absent(open_global,"open global index alias unfolded")
    cycle_context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,F.Term.Global{"Index"},True{},None{},False{}}},[I.Inline.Local{"u",univ,univ}],1n)
    cycle_term:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},F.Term.Var{0n}],[F.Term.Global{"Index"},univ],univ)},cycle_context)
    cycle:Unit <- Suite.application_absent(cycle_term,"cyclic index alias unfolded")
    unequal:Unit <- Suite.index_alias_refused(F.Global.Def{F.Global.DefEntry{univ,F.Term.Univ{F.Level.one},True{},None{},False{}}},"unequal index alias accepted")
    wrapped:Unit <- Suite.index_alias_refused(F.Global.Def{F.Global.DefEntry{univ,F.Term.Ann{F.Term.Univ{F.Level.one},univ},True{},None{},False{}}},"reduced unequal index alias accepted")
    +context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,univ,True{},None{},False{}}},Nil{},0n)
    term:F.Term.t = Suite.index_alias_term([F.Term.Global{"Index"},univ],[univ,univ],F.Term.Var{2n})
    free:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{term},context)
    Suite.application_absent(free,"open aliased constructor result accepted")

def Suite.index_alias_chain(count:Nat,body:F.Term.t) -> F.Term.t:
  match count:
    case 0n: body
    case 1n+n:
      +univ:F.Term.t = F.Term.Univ{F.Level.zero}
      F.Term.Elim{F.Term.Elimination{F.Shape.make_inductive(F.Term.t,"Choice",[F.Term.Global{"Index"},univ]),F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",[univ,univ]),F.Term.ACtor{"pair"},[univ,Suite.index_alias_chain(n,body)]},F.Quantity.Many{},Suite.index_motive(["A","a"]),Suite.constructor_branches(univ,F.Term.Var{0n})}}

def Suite.index_alias_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,univ,True{},None{},False{}}},Nil{},0n)
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_chain(64n,univ)},context)
    exact_ok:Unit <- Suite.application_equal(exact,univ)
    over:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_chain(65n,univ)},context)
    Suite.application_absent(over,"aliased index shared fuel exceeded")

def Suite.index_reduction_context() -> I.Inline.context:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,univ,True{},None{},False{}}},Nil{},0n)

def Suite.index_reduction_compare(+index:F.Term.t,+value:F.Term.t,+context:I.Inline.context,+expected:F.Term.t) -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  do Result<&2,&2,F.Error.t,Unit>:
    left:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([index,univ],[value,univ],expected)},context)
    left_ok:Unit <- Suite.application_equal(left,expected)
    right:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([value,univ],[index,univ],expected)},context)
    Suite.application_equal(right,expected)

def Suite.index_reduction_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +neutral:F.Term.t = F.Term.Global{"Neutral"}
  +context:I.Inline.context = Suite.index_reduction_context
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{univ,F.Term.Univ{F.Level.one}}),univ}
  do Result<&2,&2,F.Error.t,Unit>:
    let_ok:Unit <- Suite.index_reduction_compare(F.Term.Let{"T",univ,neutral,F.Term.Var{0n}},neutral,context,body)
    beta_ok:Unit <- Suite.index_reduction_compare(Suite.beta_term(neutral,F.Term.Var{0n}),neutral,context,body)
    annotation_ok:Unit <- Suite.index_reduction_compare(F.Term.Ann{neutral,univ},neutral,context,body)
    projection_ok:Unit <- Suite.index_reduction_compare(Suite.projection_pair(1n,univ,neutral),neutral,context,body)
    mixed:Unit <- Suite.index_reduction_compare(F.Term.Ann{Suite.beta_term(F.Term.Global{"Index"},F.Term.Let{"T",univ,F.Term.Var{0n},F.Term.Var{0n}}),univ},univ,context,body)
    later:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Ann{univ,univ},univ],[univ,F.Term.Univ{F.Level.one}],body)},context)
    Suite.application_absent(later,"later reduced index differs")

def Suite.index_reduction_source_local() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,univ,True{},None{},False{}}},[I.Inline.Local{"a",univ,F.Term.Ann{F.Term.Var{0n},univ}},I.Inline.Param{"outer",univ},I.Inline.Param{"older",univ}],3n)
  do Result<&2,&2,F.Error.t,Unit>:
    shifted:Unit <- Suite.index_reduction_compare(F.Term.Ann{F.Term.Var{0n},univ},F.Term.Var{1n},context,univ)
    capture:Unit <- Suite.index_reduction_compare(Suite.beta_term(F.Term.Var{2n},F.Term.Let{"T",univ,univ,F.Term.Var{1n}}),F.Term.Var{2n},context,univ)
    distinct:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Ann{F.Term.Var{0n},univ},univ],[F.Term.Var{2n},univ],univ)},context)
    Suite.application_absent(distinct,"reduced local index captured a parameter")

def Suite.index_reduction_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_reduction_context
  +application:F.Term.t = F.Term.Out{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",univ),F.Term.APt{F.Quantity.Zero{},univ},F.Term.Global{"Neutral"}}
  do Result<&2,&2,F.Error.t,Unit>:
    open_annotation:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(F.Term.Ann{univ,F.Term.Var{0n}},context)
    annotation_ok:Unit <- Suite.application_absent(open_annotation,"open annotated index payload accepted")
    open_let:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(F.Term.Let{"T",F.Term.Var{0n},univ,F.Term.Var{0n}},context)
    let_ok:Unit <- Suite.application_absent(open_let,"open let index payload accepted")
    unused:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.projection_pair(0n,univ,F.Term.Var{0n}),context)
    unused_ok:Unit <- Suite.application_absent(unused,"open projection index payload accepted")
    neutral:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(application,context)
    neutral_ok:Unit <- Suite.application_absent(neutral,"neutral index application reduced")
    kept:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([application,F.Term.Global{"Index"}],[application,univ],univ)},context)
    kept_ok:Unit <- Suite.application_equal(kept,univ)
    aliased_context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,application,True{},None{},False{}}},Nil{},0n)
    aliased:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([F.Term.Global{"Index"},univ],[application,univ],univ)},aliased_context)
    aliased_ok:Unit <- Suite.application_equal(aliased,univ)
    case_term:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(F.Term.Elim{F.Term.Elimination{F.Shape.make_collection(F.Term.t,2n),univ,F.Quantity.Many{},None{},Nil{}}},context)
    case_ok:Unit <- Suite.application_absent(case_term,"index case reduced")
    cycle_context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,F.Term.Ann{F.Term.Global{"Index"},univ},True{},None{},False{}}},Nil{},0n)
    cycle:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(F.Term.Global{"Index"},cycle_context)
    Suite.application_absent(cycle,"index reduction alias cycle accepted")

def Suite.index_reduction_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_reduction_context
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(64n,univ),context)
    exact_ok:Unit <- Suite.application_equal(exact,univ)
    over:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(65n,univ),context)
    over_ok:Unit <- Suite.application_absent(over,"index let fuel exceeded")
    beta:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.beta_chain(64n,univ),context)
    beta_ok:Unit <- Suite.application_equal(beta,univ)
    beta_over:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.beta_chain(65n,univ),context)
    beta_over_ok:Unit <- Suite.application_absent(beta_over,"index beta fuel exceeded")
    shared:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(32n,Suite.beta_chain(32n,univ)),context)
    shared_ok:Unit <- Suite.application_equal(shared,univ)
    shared_over:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(32n,Suite.beta_chain(33n,univ)),context)
    shared_over_ok:Unit <- Suite.application_absent(shared_over,"index let and beta fuel not shared")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(F.Term.Ann{Suite.let_chain(64n,univ),univ},context)
    Suite.application_absent(mixed,"index annotation and let fuel not shared")

def Suite.constructor_index_family(family:F.Positivity.family) -> F.Positivity.family:
  F.Positivity.Family{name,params,indices,level,status,ctors,positive} = family
  F.Positivity.Family{"Inner",params,indices,level,status,ctors,positive}

def Suite.constructor_index_term(name:String,args:List<&2,F.Term.t>,empty:F.Term.t,body:F.Term.t) -> F.Term.t:
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Inner",Nil{})
  F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{name},args},F.Quantity.Many{},None{},Suite.constructor_branches(empty,body)}}

def Suite.constructor_index_context(context:I.Inline.context) -> I.Inline.context:
  I.Inline.Context{checker,domains} = context
  globals:F.Global.t = F.Global.add_family("Inner",Suite.constructor_index_family(Suite.constructor_family),C.Check.global(checker))
  I.Inline.Context{C.Check.Ctx{globals,Nil{},Nil{},0n,C.Budget.unlimited},domains}

def Suite.constructor_index_equal(term:F.Term.t,context:I.Inline.context,expected:F.Term.t) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(term,context)
    Suite.application_equal(actual,expected)

def Suite.constructor_index_refused(term:F.Term.t,context:I.Inline.context,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(term,context)
    Suite.application_absent(actual,message)

def Suite.constructor_index_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.constructor_index_context(Suite.index_reduction_context)
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{univ,F.Term.Univ{F.Level.one}}),univ}
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Inner",Nil{})
  +point:F.Shape.t<F.Term.t> = F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"T",univ)
  +identity:F.Term.t = F.Term.Sec{point,[F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"T"}],F.Term.Var{0n}}]}
  do Result<&2,&2,F.Error.t,Unit>:
    empty:Unit <- Suite.index_reduction_compare(Suite.constructor_index_term("empty",Nil{},univ,univ),univ,context,body)
    pair:Unit <- Suite.index_reduction_compare(Suite.constructor_index_term("pair",[univ,univ],univ,F.Term.Var{0n}),univ,context,body)
    alias:Unit <- Suite.index_reduction_compare(Suite.constructor_index_term("pair",[univ,F.Term.Global{"Index"}],univ,F.Term.Var{0n}),univ,context,body)
    reordered:Unit <- Suite.constructor_index_equal(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},Some{F.Term.Motive{Some{"Inner"},Nil{},"self",univ}},I.Inline.reverse(F.Pair2<F.Term.addr,F.Term.leg>,Suite.constructor_branches(univ,F.Term.Var{0n}),Nil{})}},context,univ)
    mixed:Unit <- Suite.index_reduction_compare(Suite.case_pair(1n,Suite.projection_pair(1n,univ,Suite.beta_term(univ,Suite.constructor_index_term("pair",[univ,F.Term.Var{0n}],univ,F.Term.Var{0n}))),univ,F.Term.Var{0n}),univ,context,body)
    application:Unit <- Suite.constructor_index_equal(F.Term.Out{point,F.Term.APt{F.Quantity.Zero{},univ},Suite.constructor_index_term("pair",[univ,identity],univ,F.Term.Var{0n})},context,univ)
    later:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([Suite.constructor_index_term("empty",Nil{},univ,univ),univ],[univ,F.Term.Univ{F.Level.one}],body)},context)
    Suite.application_absent(later,"later constructor index differs")

def Suite.constructor_index_source_scope() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.constructor_context(2n)
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{4n},univ}}
  +expected:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"y",F.Term.Ann{F.Term.Var{1n},univ}),F.Term.Ann{F.Term.Var{2n},univ}}
  do Result<&2,&2,F.Error.t,Unit>:
    scoped:Unit <- Suite.constructor_index_equal(Suite.constructor_term("pair",[F.Term.Var{1n},F.Term.Var{0n}],univ,body),context,expected)
    unused:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ],F.Term.Var{0n},univ),Suite.constructor_context(0n),"open unused constructor index branch accepted")
    selected:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ],univ,F.Term.Var{2n}),Suite.constructor_context(0n),"open selected constructor index branch accepted")
    payload:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,F.Term.Var{0n}],univ,univ),Suite.constructor_context(0n),"open constructor index payload accepted")
    large:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,Suite.constructor_tree(11n,univ)],univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Var{1n}}),Suite.constructor_context(0n),"constructor index size cap ignored")
    Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ],univ,Suite.size_chain(14n)),Suite.constructor_context(0n),"constructor index let size cap ignored")

def Suite.constructor_index_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.constructor_context(0n)
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  +scrut:F.Term.t = F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]}
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = Suite.constructor_branches(univ,univ)
  +pair:F.Term.leg = F.Term.Leg{[F.Pair2{F.Quantity.Zero{},"A"},F.Pair2{F.Quantity.Zero{},"x"}],univ}
  +empty:F.Term.leg = F.Term.Leg{Nil{},univ}
  do Result<&2,&2,F.Error.t,Unit>:
    missing:Unit <- Suite.constructor_index_refused(Suite.constructor_term("missing",[univ,univ],univ,univ),context,"unknown constructor index constructor accepted")
    short:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ],univ,univ),context,"short constructor index payload accepted")
    long:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ,univ],univ,univ),context,"long constructor index payload accepted")
    shape_ok:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{F.Shape.make_inductive(F.Term.t,"Other",Nil{}),F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},None{},branches}},context,"constructor index shape mismatch accepted")
    absent:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ],univ,univ),I.Inline.Context{C.Check.Ctx{F.Global.empty,Nil{},Nil{},0n,C.Budget.unlimited},Nil{}},"missing constructor index family accepted")
    duplicate:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"pair"},pair},F.Pair2{F.Term.ACtor{"pair"},pair}]}},context,"duplicate constructor index branch accepted")
    coverage:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"pair"},pair}]}},context,"missing constructor index branch accepted")
    quantity:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ACtor{"empty"},empty},F.Pair2{F.Term.ACtor{"pair"},F.Term.Leg{[F.Pair2{F.Quantity.Many{},"A"},F.Pair2{F.Quantity.Zero{},"x"}],univ}}]}},context,"constructor index quantity mismatch accepted")
    motive:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},Some{F.Term.Motive{Some{"Other"},Nil{},"self",univ}},branches}},context,"constructor index motive mismatch accepted")
    open_motive:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,scrut,F.Quantity.Many{},Some{F.Term.Motive{Some{"Choice"},Nil{},"self",F.Term.Var{1n}}},branches}},context,"open constructor index motive accepted")
    Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,F.Term.Global{"neutral"},F.Quantity.Many{},None{},branches}},context,"neutral constructor index scrutinee accepted")

def Suite.constructor_index_source_metadata(family:F.Positivity.family) -> Result<&2,&2,F.Error.t,Unit>:
  F.Positivity.Family{+name,+params,+indices,+level,status,+ctors,positive} = family
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_context(0n)
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",[univ,univ])
  +term:F.Term.t = Suite.index_term("pair",[univ,univ],univ,F.Term.Var{0n},Suite.index_motive(["A","a"]))
  +invalid:F.Global.t = F.Global.add_family("Choice",F.Positivity.Family{name,params,indices,level,status,ctors,False{}},F.Global.empty)
  +bad_context:I.Inline.context = I.Inline.Context{C.Check.Ctx{invalid,Nil{},Nil{},0n,C.Budget.unlimited},Nil{}}
  do Result<&2,&2,F.Error.t,Unit>:
    indexed:Unit <- Suite.constructor_index_equal(term,context,univ)
    motive:Unit <- Suite.constructor_index_refused(Suite.index_term("pair",[univ,univ],univ,univ,None{}),context,"constructor index indexed motive missing")
    different:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",[F.Term.Univ{F.Level.one},univ]),F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},Suite.index_motive(["A","a"]),Suite.constructor_branches(univ,univ)}},context,"constructor index unequal shape payload accepted")
    reentry:Unit <- Suite.constructor_index_refused(F.Term.Elim{F.Term.Elimination{shape,F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",[F.Term.Ann{univ,univ},univ]),F.Term.ACtor{"pair"},[univ,univ]},F.Quantity.Many{},Suite.index_motive(["A","a"]),Suite.constructor_branches(univ,univ)}},context,"constructor index shape recovery reentered")
    nonpositive:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ],univ,univ),bad_context,"nonpositive constructor index family accepted")
    provisional:F.Global.t = F.Global.add_family("Choice",F.Positivity.Family{name,params,indices,level,F.Positivity.Provisional{},ctors,positive},F.Global.empty)
    provisional_ok:Unit <- Suite.constructor_index_refused(Suite.constructor_term("pair",[univ,univ],univ,univ),I.Inline.Context{C.Check.Ctx{provisional,Nil{},Nil{},0n,C.Budget.unlimited},Nil{}},"provisional constructor index family accepted")
    recursive:F.Global.t = F.Global.add_family("Choice",Suite.recursive_family(Suite.constructor_family),F.Global.empty)
    Suite.constructor_index_equal(Suite.constructor_term("pair",[univ,F.Term.In{F.Shape.make_inductive(F.Term.t,"Choice",Nil{}),F.Term.ACtor{"empty"},Nil{}}],univ,F.Term.Var{1n}),I.Inline.Context{C.Check.Ctx{recursive,Nil{},Nil{},0n,C.Budget.unlimited},Nil{}},univ)

def Suite.constructor_index_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.constructor_context(0n)
  +shape:F.Shape.t<F.Term.t> = F.Shape.make_inductive(F.Term.t,"Choice",Nil{})
  +scrut:F.Term.t = F.Term.In{shape,F.Term.ACtor{"pair"},[univ,univ]}
  do Result<&2,&2,F.Error.t,Unit>:
    exact:Unit <- Suite.constructor_index_equal(Suite.constructor_chain(64n,univ),context,univ)
    over:Unit <- Suite.constructor_index_refused(Suite.let_chain(32n,Suite.constructor_chain(33n,univ)),context,"constructor index result fuel exceeded")
    head:Unit <- Suite.constructor_index_equal(Suite.let_chain(32n,F.Term.Elim{F.Term.Elimination{shape,Suite.beta_chain(31n,scrut),F.Quantity.Many{},None{},Suite.constructor_branches(univ,F.Term.Var{0n})}}),context,univ)
    head_over:Unit <- Suite.constructor_index_refused(Suite.let_chain(32n,F.Term.Elim{F.Term.Elimination{shape,Suite.beta_chain(32n,scrut),F.Quantity.Many{},None{},Suite.constructor_branches(univ,F.Term.Var{0n})}}),context,"constructor index head fuel exceeded")
    shared:Unit <- Suite.constructor_index_equal(Suite.let_chain(32n,F.Term.Elim{F.Term.Elimination{shape,Suite.beta_chain(15n,scrut),F.Quantity.Many{},None{},Suite.constructor_branches(univ,Suite.constructor_chain(16n,univ))}}),context,univ)
    shared_over:Unit <- Suite.constructor_index_refused(Suite.let_chain(32n,F.Term.Elim{F.Term.Elimination{shape,Suite.beta_chain(15n,scrut),F.Quantity.Many{},None{},Suite.constructor_branches(univ,Suite.constructor_chain(17n,univ))}}),context,"constructor index head and result fuel not shared")
    mixed:Unit <- Suite.constructor_index_equal(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_chain(16n,Suite.constructor_chain(16n,univ)))),context,univ)
    Suite.constructor_index_refused(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_chain(16n,Suite.constructor_chain(17n,univ)))),context,"constructor index mixed fuel not shared")

def Suite.sum_index_source_syntax() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +neutral:F.Term.t = F.Term.Global{"Neutral"}
  +context:I.Inline.context = Suite.index_reduction_context
  +body:F.Term.t = F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Ann{univ,F.Term.Univ{F.Level.one}}),univ}
  +two:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +binder:F.Pair2<F.Quantity.t,String> = F.Pair2{F.Quantity.Many{},"payload"}
  +scrut:F.Term.t = F.Term.In{two,F.Term.ALeg{1n},[neutral]}
  do Result<&2,&2,F.Error.t,Unit>:
    first:Unit <- Suite.index_reduction_compare(Suite.case_pair(0n,neutral,F.Term.Var{0n},univ),neutral,context,body)
    second:Unit <- Suite.index_reduction_compare(Suite.case_pair(1n,neutral,univ,F.Term.Var{0n}),neutral,context,body)
    reversed:Unit <- Suite.index_reduction_compare(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{None{},Nil{},"self",univ}},[F.Pair2{F.Term.ALeg{1n},F.Term.Leg{[binder],F.Term.Var{0n}}},F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[binder],univ}}]}},neutral,context,body)
    head:Unit <- Suite.index_reduction_compare(Suite.case_head_chain(2n,neutral),neutral,context,body)
    mixed:Unit <- Suite.index_reduction_compare(F.Term.Ann{Suite.beta_term(univ,Suite.case_pair(1n,F.Term.Var{0n},univ,Suite.projection_pair(1n,univ,F.Term.Var{0n}))),univ},univ,context,body)
    applied:Unit <- Suite.index_reduction_compare(Suite.beta_term(univ,Suite.case_pair(1n,F.Term.Var{0n},univ,F.Term.Var{0n})),univ,context,body)
    later:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([Suite.case_pair(1n,univ,univ,F.Term.Var{0n}),univ],[univ,F.Term.Univ{F.Level.one}],body)},context)
    Suite.application_absent(later,"later sum index differs")

def Suite.sum_index_source_local() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +two:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +binder:F.Pair2<F.Quantity.t,String> = F.Pair2{F.Quantity.Many{},"payload"}
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = [F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[binder],univ}},F.Pair2{F.Term.ALeg{1n},F.Term.Leg{[binder],F.Term.Var{0n}}}]
  +context:I.Inline.context = Suite.index_alias_context(F.Global.Def{F.Global.DefEntry{univ,F.Term.Ann{F.Term.In{two,F.Term.ALeg{1n},[univ]},univ},True{},None{},False{}}},[I.Inline.Local{"sum",univ,F.Term.In{two,F.Term.ALeg{1n},[F.Term.Var{0n}]}},I.Inline.Param{"outer",univ},I.Inline.Param{"older",univ}],3n)
  do Result<&2,&2,F.Error.t,Unit>:
    global:Unit <- Suite.index_reduction_compare(F.Term.Elim{F.Term.Elimination{two,F.Term.Global{"Index"},F.Quantity.Many{},None{},branches}},univ,context,univ)
    local:Unit <- Suite.index_reduction_compare(F.Term.Elim{F.Term.Elimination{two,F.Term.Var{0n},F.Quantity.Many{},None{},branches}},F.Term.Var{1n},context,univ)
    capture:Unit <- Suite.index_reduction_compare(Suite.case_pair(1n,F.Term.Var{2n},univ,F.Term.Let{"T",univ,univ,F.Term.Var{1n}}),F.Term.Var{2n},context,univ)
    distinct:Maybe<&2,F.Term.t> <- I.Inline.source_alias_type(Some{Suite.index_alias_term([Suite.case_pair(1n,F.Term.Var{1n},univ,F.Term.Var{0n}),univ],[F.Term.Var{2n},univ],univ)},context)
    Suite.application_absent(distinct,"sum index captured a parameter")

def Suite.sum_index_refused(term:F.Term.t,message:String) -> Result<&2,&2,F.Error.t,Unit>:
  do Result<&2,&2,F.Error.t,Unit>:
    actual:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(term,Suite.index_reduction_context)
    Suite.application_absent(actual,message)

def Suite.sum_index_source_guards() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +one:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,1n)
  +two:F.Shape.t<F.Term.t> = F.Shape.make_collection(F.Term.t,2n)
  +binder:F.Pair2<F.Quantity.t,String> = F.Pair2{F.Quantity.Many{},"payload"}
  +leg:F.Term.leg = F.Term.Leg{[binder],univ}
  +branches:List<&2,F.Pair2<F.Term.addr,F.Term.leg>> = [F.Pair2{F.Term.ALeg{0n},leg},F.Pair2{F.Term.ALeg{1n},leg}]
  +scrut:F.Term.t = F.Term.In{two,F.Term.ALeg{1n},[univ]}
  do Result<&2,&2,F.Error.t,Unit>:
    shape:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.In{one,F.Term.ALeg{1n},[univ]},F.Quantity.Many{},None{},branches}},"sum index shape mismatch accepted")
    short:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{1n},leg}]}},"short sum index branches accepted")
    duplicate:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{1n},leg},F.Pair2{F.Term.ALeg{1n},leg}]}},"duplicate sum index branch accepted")
    outside:Unit <- Suite.sum_index_refused(Suite.case_pair(2n,univ,univ,univ),"missing sum index branch accepted")
    empty:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.In{two,F.Term.ALeg{1n},Nil{}},F.Quantity.Many{},None{},branches}},"empty sum index payload accepted")
    extra:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.In{two,F.Term.ALeg{1n},[univ,univ]},F.Quantity.Many{},None{},branches}},"extra sum index payload accepted")
    arity:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},None{},[F.Pair2{F.Term.ALeg{0n},F.Term.Leg{[binder,binder],univ}},F.Pair2{F.Term.ALeg{1n},leg}]}},"extra unused sum index binder accepted")
    motive:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{Some{"Named"},Nil{},"self",univ}},branches}},"named sum index motive accepted")
    indexed:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{None{},["index"],"self",univ}},branches}},"indexed sum index motive accepted")
    unused:Unit <- Suite.sum_index_refused(Suite.case_pair(1n,univ,F.Term.Var{1n},univ),"open unused sum index branch accepted")
    selected:Unit <- Suite.sum_index_refused(Suite.case_pair(1n,univ,univ,F.Term.Var{1n}),"open selected sum index branch accepted")
    payload:Unit <- Suite.sum_index_refused(Suite.case_pair(1n,F.Term.Var{0n},univ,univ),"open sum index payload accepted")
    annotation:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.Ann{scrut,F.Term.Var{0n}},F.Quantity.Many{},None{},branches}},"open sum index annotation accepted")
    open_motive:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,scrut,F.Quantity.Many{},Some{F.Term.Motive{None{},Nil{},"self",F.Term.Var{1n}}},branches}},"open sum index motive accepted")
    neutral:Unit <- Suite.sum_index_refused(F.Term.Elim{F.Term.Elimination{two,F.Term.Global{"Neutral"},F.Quantity.Many{},None{},branches}},"neutral sum index scrutinee accepted")
    large_let:Unit <- Suite.sum_index_refused(Suite.case_pair(1n,univ,univ,Suite.size_chain(14n)),"sum index let size cap ignored")
    large:Unit <- Suite.sum_index_refused(Suite.case_pair(1n,Suite.constructor_tree(11n,univ),univ,F.Term.Ran{F.Shape.make_point(F.Term.t,F.Quantity.Zero{},"x",F.Term.Var{0n}),F.Term.Var{1n}}),"sum index size cap ignored")
    Suite.constructor_index_equal(Suite.index_alias_term([univ,univ],[univ,univ],univ),Suite.index_reduction_context,univ)

def Suite.sum_index_source_fuel() -> Result<&2,&2,F.Error.t,Unit>:
  +univ:F.Term.t = F.Term.Univ{F.Level.zero}
  +context:I.Inline.context = Suite.index_reduction_context
  do Result<&2,&2,F.Error.t,Unit>:
    head:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.case_head_chain(64n,univ),context)
    head_ok:Unit <- Suite.application_equal(head,univ)
    head_steps:Unit <- Suite.sum_index_refused(Suite.case_head_chain(65n,univ),"sum index head transitions exceeded")
    head_fuel:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(32n,Suite.case_head_chain(32n,univ)),context)
    head_fuel_ok:Unit <- Suite.application_equal(head_fuel,univ)
    head_over:Unit <- Suite.sum_index_refused(Suite.let_chain(33n,Suite.case_head_chain(32n,univ)),"sum index head fuel exceeded")
    result:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.case_result_chain(64n,univ),context)
    result_ok:Unit <- Suite.application_equal(result,univ)
    result_steps:Unit <- Suite.sum_index_refused(Suite.case_result_chain(65n,univ),"sum index result transitions exceeded")
    result_fuel:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(32n,Suite.case_result_chain(32n,univ)),context)
    result_fuel_ok:Unit <- Suite.application_equal(result_fuel,univ)
    result_over:Unit <- Suite.sum_index_refused(Suite.let_chain(33n,Suite.case_result_chain(32n,univ)),"sum index result fuel exceeded")
    shared:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.case_head_chain(32n,Suite.case_result_chain(32n,univ)),context)
    shared_ok:Unit <- Suite.application_equal(shared,univ)
    shared_steps:Unit <- Suite.sum_index_refused(Suite.case_head_chain(32n,Suite.case_result_chain(33n,univ)),"sum index head and result transitions exceeded")
    shared_fuel:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(32n,Suite.case_head_chain(16n,Suite.case_result_chain(16n,univ))),context)
    shared_fuel_ok:Unit <- Suite.application_equal(shared_fuel,univ)
    shared_over:Unit <- Suite.sum_index_refused(Suite.let_chain(32n,Suite.case_head_chain(16n,Suite.case_result_chain(17n,univ))),"sum index head and result fuel not shared")
    mixed:Maybe<&2,F.Term.t> <- I.Inline.index_source_head(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_result_chain(32n,univ))),context)
    mixed_ok:Unit <- Suite.application_equal(mixed,univ)
    Suite.sum_index_refused(Suite.let_chain(16n,Suite.beta_chain(16n,Suite.case_result_chain(33n,univ))),"sum index let and beta fuel not shared")

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
      Suite.Case{"lambda-case-global",unit => Suite.local_sealed(LF.Fixture.lambda_case_global,LF.Fixture.lambda_case_global_opaque,layout,1n)},
      Suite.Case{"lambda-constructor-global",unit => Suite.local_sealed(LF.Fixture.lambda_constructor_global,LF.Fixture.lambda_constructor_global_opaque,layout,1n)},
      Suite.Case{"lambda-constructor-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_constructor_dependent,LF.Fixture.lambda_constructor_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-constructor-local",unit => Suite.local_sealed(LF.Fixture.lambda_constructor_local,LF.Fixture.lambda_constructor_local_opaque,layout,1n)},
      Suite.Case{"lambda-constructor-curried",unit => Suite.local_sealed(LF.Fixture.lambda_constructor_curried,LF.Fixture.lambda_constructor_curried_opaque,layout,1n)},
      Suite.Case{"constructor-source-syntax",unit => Suite.constructor_source_syntax},
      Suite.Case{"lambda-index-global",unit => Suite.local_sealed(LF.Fixture.lambda_index_global,LF.Fixture.lambda_index_global_opaque,layout,1n)},
      Suite.Case{"lambda-index-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_index_dependent,LF.Fixture.lambda_index_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-index-local",unit => Suite.local_sealed(LF.Fixture.lambda_index_local,LF.Fixture.lambda_index_local_opaque,layout,1n)},
      Suite.Case{"lambda-index-curried",unit => Suite.local_sealed(LF.Fixture.lambda_index_curried,LF.Fixture.lambda_index_curried_opaque,layout,1n)},
      Suite.Case{"index-source-syntax",unit => Suite.index_source_syntax},
      Suite.Case{"index-source-motive",unit => Suite.index_source_motive},
      Suite.Case{"index-source-metadata",unit => Suite.index_source_metadata},
      Suite.Case{"index-source-shapes",unit => Suite.index_source_shapes},
      Suite.Case{"index-source-scope",unit => Suite.index_source_scope},
      Suite.Case{"index-source-fuel",unit => Suite.index_source_fuel},
      Suite.Case{"lambda-recursive-global",unit => Suite.local_sealed(LF.Fixture.lambda_recursive_global,LF.Fixture.lambda_recursive_global_opaque,layout,1n)},
      Suite.Case{"lambda-recursive-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_recursive_dependent,LF.Fixture.lambda_recursive_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-recursive-local",unit => Suite.local_sealed(LF.Fixture.lambda_recursive_local,LF.Fixture.lambda_recursive_local_opaque,layout,1n)},
      Suite.Case{"lambda-recursive-indexed",unit => Suite.local_sealed(LF.Fixture.lambda_recursive_indexed,LF.Fixture.lambda_recursive_indexed_opaque,layout,1n)},
      Suite.Case{"recursive-source-syntax",unit => Suite.recursive_source_syntax},
      Suite.Case{"recursive-source-metadata",unit => Suite.constructor_source_metadata(Suite.recursive_family(Suite.constructor_family),True{})},
      Suite.Case{"recursive-source-scope",unit => Suite.recursive_source_scope},
      Suite.Case{"recursive-source-fuel",unit => Suite.recursive_source_fuel},
      Suite.Case{"index-alias-source-syntax",unit => Suite.index_alias_source_syntax},
      Suite.Case{"index-alias-source-local",unit => Suite.index_alias_source_local},
      Suite.Case{"index-alias-source-guards",unit => Suite.index_alias_source_guards},
      Suite.Case{"index-alias-source-fuel",unit => Suite.index_alias_source_fuel},
      Suite.Case{"index-reduction-source-syntax",unit => Suite.index_reduction_source_syntax},
      Suite.Case{"index-reduction-source-local",unit => Suite.index_reduction_source_local},
      Suite.Case{"index-reduction-source-guards",unit => Suite.index_reduction_source_guards},
      Suite.Case{"index-reduction-source-fuel",unit => Suite.index_reduction_source_fuel},
      Suite.Case{"sum-index-source-syntax",unit => Suite.sum_index_source_syntax},
      Suite.Case{"constructor-index-source-syntax",unit => Suite.constructor_index_source_syntax},
      Suite.Case{"constructor-index-source-scope",unit => Suite.constructor_index_source_scope},
      Suite.Case{"constructor-index-source-guards",unit => Suite.constructor_index_source_guards},
      Suite.Case{"constructor-index-source-metadata",unit => Suite.constructor_index_source_metadata(Suite.constructor_family)},
      Suite.Case{"constructor-index-source-fuel",unit => Suite.constructor_index_source_fuel},
      Suite.Case{"lambda-constructor-index-empty",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_constructor_index_empty,LF.Fixture.lambda_constructor_index_empty_opaque,layout,6n)},
      Suite.Case{"lambda-constructor-index-value",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_constructor_index_value,LF.Fixture.lambda_constructor_index_value_opaque,layout,7n)},
      Suite.Case{"sum-index-source-local",unit => Suite.sum_index_source_local},
      Suite.Case{"sum-index-source-guards",unit => Suite.sum_index_source_guards},
      Suite.Case{"sum-index-source-fuel",unit => Suite.sum_index_source_fuel},
      Suite.Case{"lambda-sum-index-left",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_sum_index_left,LF.Fixture.lambda_sum_index_left_opaque,layout,4n)},
      Suite.Case{"lambda-sum-index-right",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_sum_index_right,LF.Fixture.lambda_sum_index_right_opaque,layout,5n)},
      Suite.Case{"lambda-index-reduction-let",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_index_reduction_let,LF.Fixture.lambda_index_reduction_let_opaque,layout,0n)},
      Suite.Case{"lambda-index-reduction-beta",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_index_reduction_beta,LF.Fixture.lambda_index_reduction_beta_opaque,layout,1n)},
      Suite.Case{"lambda-index-reduction-annotation",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_index_reduction_annotation,LF.Fixture.lambda_index_reduction_annotation_opaque,layout,2n)},
      Suite.Case{"lambda-index-reduction-projection",unit => Suite.index_reduction_sealed(LF.Fixture.lambda_index_reduction_projection,LF.Fixture.lambda_index_reduction_projection_opaque,layout,3n)},
      Suite.Case{"lambda-index-alias-global",unit => Suite.index_alias_sealed(LF.Fixture.lambda_index_alias_global,LF.Fixture.lambda_index_alias_global_opaque,layout,1n,False{})},
      Suite.Case{"lambda-index-alias-local",unit => Suite.index_alias_sealed(LF.Fixture.lambda_index_alias_local,LF.Fixture.lambda_index_alias_local_opaque,layout,1n,True{})},
      Suite.Case{"lambda-parameter-global",unit => Suite.local_sealed(LF.Fixture.lambda_parameter_global,LF.Fixture.lambda_parameter_global_opaque,layout,1n)},
      Suite.Case{"lambda-parameter-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_parameter_dependent,LF.Fixture.lambda_parameter_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-parameter-local",unit => Suite.local_sealed(LF.Fixture.lambda_parameter_local,LF.Fixture.lambda_parameter_local_opaque,layout,1n)},
      Suite.Case{"lambda-parameter-curried",unit => Suite.local_sealed(LF.Fixture.lambda_parameter_curried,LF.Fixture.lambda_parameter_curried_opaque,layout,1n)},
      Suite.Case{"parameter-source-syntax",unit => Suite.parameter_source_syntax},
      Suite.Case{"parameter-source-guards",unit => Suite.parameter_source_guards},
      Suite.Case{"parameter-source-scope",unit => Suite.parameter_source_scope},
      Suite.Case{"parameter-source-metadata",unit => Suite.parameter_source_metadata},
      Suite.Case{"parameter-introductions",unit => Suite.parameter_introductions},
      Suite.Case{"parameter-source-fuel",unit => Suite.parameter_source_fuel},
      Suite.Case{"constructor-source-guards",unit => Suite.constructor_source_guards},
      Suite.Case{"constructor-source-metadata",unit => Suite.constructor_source_metadata(Suite.constructor_family,False{})},
      Suite.Case{"constructor-source-scope",unit => Suite.constructor_source_scope},
      Suite.Case{"constructor-source-fuel",unit => Suite.constructor_source_fuel},
      Suite.Case{"constructor-source-pending",unit => Suite.constructor_source_pending},
      Suite.Case{"lambda-case-dependent",unit => Suite.local_sealed(LF.Fixture.lambda_case_dependent,LF.Fixture.lambda_case_dependent_opaque,layout,1n)},
      Suite.Case{"lambda-case-local",unit => Suite.local_sealed(LF.Fixture.lambda_case_local,LF.Fixture.lambda_case_local_opaque,layout,1n)},
      Suite.Case{"lambda-case-curried",unit => Suite.local_sealed(LF.Fixture.lambda_case_curried,LF.Fixture.lambda_case_curried_opaque,layout,1n)},
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
      Suite.Case{"case-source-syntax",unit => Suite.case_source_syntax},
      Suite.Case{"case-source-guards",unit => Suite.case_source_guards},
      Suite.Case{"case-source-scope",unit => Suite.case_source_scope},
      Suite.Case{"case-source-fuel",unit => Suite.case_source_fuel},
      Suite.Case{"case-source-pending",unit => Suite.case_source_pending},
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
