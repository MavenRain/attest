import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_mu.bend as M
import ../lib/kernel_eval.bend as E
import ../lib/kernel_primitives.bend as P
import ../lib/erasure.bend as R
import ../lib/kernel_source.bend as S

def Inline.append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}: ys
    case h <> t: h <> Inline.append(A, t, ys)

def Inline.length(-A: Data, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}: 0n
    case h <> t: 1n+Inline.length(A, t)

def Inline.here(xs: List<&2, F.Term.t>) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match xs:
    case Nil{}: Nil{}
    case h <> t: F.Pair2{0n, h} <> Inline.here(t)

def Inline.shape_children(s: F.Shape.t<F.Term.t>) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  Inline.here(F.Shape.payload(F.Term.t, s))

def Inline.option_count(-A: Data, value: Maybe<&2, A>) -> Nat:
  match value:
    case None{}: 0n
    case Some{x}: 1n

def Inline.former_binders(s: F.Shape.t<F.Term.t>) -> Nat:
  Inline.option_count(F.Term.t, F.Shape.point_dom(F.Term.t, s))

def Inline.address_children(a: F.Term.addr) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match a:
    case F.Term.APt{q, t}: [F.Pair2{0n, t}]
    case F.Term.ALeg{k}: Nil{}
    case F.Term.ACtor{name}: Nil{}

def Inline.leg_child(leg: F.Term.leg) -> F.Pair2<Nat, F.Term.t>:
  F.Term.Leg{binders, body} = leg
  F.Pair2{Inline.length(F.Pair2<F.Quantity.t, String>, binders), body}

def Inline.leg_children(legs: List<&2, F.Term.leg>) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match legs:
    case Nil{}: Nil{}
    case h <> t: Inline.leg_child(h) <> Inline.leg_children(t)

def Inline.motive_children(m: Maybe<&2, F.Term.motive>) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match m:
    case None{}: Nil{}
    case Some{F.Term.Motive{ind, idx, self, body}}:
      [F.Pair2{1n+Inline.length(String, idx), body}]

def Inline.branch_children(bs: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match bs:
    case Nil{}: Nil{}
    case F.Pair2{address, leg} <> rest:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.address_children(address), Inline.leg_child(leg) <> Inline.branch_children(rest))

def Inline.children(term: F.Term.t) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match term:
    case F.Term.Var{ix}: Nil{}
    case F.Term.Global{name}: Nil{}
    case F.Term.Univ{level}: Nil{}
    case F.Term.Lit{literal}: Nil{}
    case F.Term.Auto{}: Nil{}
    case F.Term.Lan{+shape, diagram}:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shape_children(shape), [F.Pair2{Inline.former_binders(shape), diagram}])
    case F.Term.Ran{+shape, diagram}:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shape_children(shape), [F.Pair2{Inline.former_binders(shape), diagram}])
    case F.Term.In{shape, address, args}:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shape_children(shape), Inline.append(F.Pair2<Nat, F.Term.t>, Inline.address_children(address), Inline.here(args)))
    case F.Term.Out{shape, address, head}:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shape_children(shape), Inline.append(F.Pair2<Nat, F.Term.t>, Inline.address_children(address), [F.Pair2{0n, head}]))
    case F.Term.Sec{shape, legs}:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shape_children(shape), Inline.leg_children(legs))
    case F.Term.Elim{F.Term.Elimination{shape, scrut, quantity, motive, branches}}:
      Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shape_children(shape), F.Pair2{0n, scrut} <> Inline.append(F.Pair2<Nat, F.Term.t>, Inline.motive_children(motive), Inline.branch_children(branches)))
    case F.Term.Let{name, ty, value, body}: [F.Pair2{0n, ty}, F.Pair2{0n, value}, F.Pair2{1n, body}]
    case F.Term.Ann{value, ty}: [F.Pair2{0n, value}, F.Pair2{0n, ty}]

def Inline.shift_children(xs: List<&2, F.Pair2<Nat, F.Term.t>>, +depth: Nat) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match xs:
    case Nil{}: Nil{}
    case F.Pair2{shift, child} <> rest:
      F.Pair2{(depth + shift : Nat), child} <> Inline.shift_children(rest, depth)

type Inline.scan_mode is Data:
  Inline.Closed{}
  Inline.Occurs{}

def Inline.scan_empty(mode: Inline.scan_mode) -> Bool:
  match mode:
    case Inline.Closed{}: True{}
    case Inline.Occurs{}: False{}

def Inline.scan_var(mode: Inline.scan_mode, ix: Nat, depth: Nat, rest: Bool) -> Bool:
  match mode:
    case Inline.Closed{}: Bool.and(Nat.is_lt(ix, depth), rest)
    case Inline.Occurs{}: Bool.or(Nat.is_eq(ix, depth), rest)

# The work list replaces mutual recursion through syntax lists. Every task
# expands only into strict syntax children and there is no depth cutoff.
@unsafe
def Inline.scan(tasks: List<&2, F.Pair2<Nat, F.Term.t>>, +mode: Inline.scan_mode) -> Bool:
  match tasks:
    case Nil{}: Inline.scan_empty(mode)
    case F.Pair2{depth, term} <> rest:
      match term:
        case F.Term.Var{ix}: Inline.scan_var(mode, ix, depth, Inline.scan(rest, mode))
        case other:
          Inline.scan(Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shift_children(Inline.children(other), depth), rest), mode)

def Inline.closed(depth: Nat, term: F.Term.t) -> Bool:
  Inline.scan([F.Pair2{depth, term}], Inline.Closed{})

def Inline.occurs(target: Nat, term: F.Term.t) -> Bool:
  Inline.scan([F.Pair2{target, term}], Inline.Occurs{})

def Inline.occurs_children(children: List<&2, F.Pair2<Nat, F.Term.t>>, depth: Nat) -> Bool:
  Inline.scan(Inline.shift_children(children, depth), Inline.Occurs{})

def Inline.typed_here(term: F.Term.t, +target: Nat) -> Bool:
  match term:
    case F.Term.Var{ix}: False{}
    case F.Term.Global{name}: False{}
    case F.Term.Univ{level}: False{}
    case F.Term.Lit{literal}: False{}
    case F.Term.Auto{}: False{}
    case F.Term.Lan{s, d}: Inline.occurs(target, F.Term.Lan{s, d})
    case F.Term.Ran{s, d}: Inline.occurs(target, F.Term.Ran{s, d})
    case F.Term.In{s, a, args}: Inline.occurs_children(Inline.shape_children(s), target)
    case F.Term.Out{s, a, head}: Inline.occurs_children(Inline.shape_children(s), target)
    case F.Term.Sec{s, legs}: Inline.occurs_children(Inline.shape_children(s), target)
    case F.Term.Elim{F.Term.Elimination{shape, scrut, quantity, motive, branches}}:
      Bool.or(Inline.occurs_children(Inline.shape_children(shape), target), Inline.occurs_children(Inline.motive_children(motive), target))
    case F.Term.Let{name, ty, value, body}: Bool.or(Inline.occurs(target, ty), Inline.occurs(target, value))
    case F.Term.Ann{value, ty}: Inline.occurs(target, ty)

@unsafe
def Inline.typed_tasks(tasks: List<&2, F.Pair2<Nat, F.Term.t>>) -> Bool:
  match tasks:
    case Nil{}: False{}
    case F.Pair2{+target, +term} <> rest:
      Bool.or(Inline.typed_here(term, target), Inline.typed_tasks(Inline.append(F.Pair2<Nat, F.Term.t>, Inline.shift_children(Inline.children(term), target), rest)))

def Inline.typed(target: Nat, term: F.Term.t) -> Bool:
  Inline.typed_tasks([F.Pair2{target, term}])

type Inline.state is Data:
  Inline.State{globals: F.Global.t, next: Nat}

type Inline.local is Data:
  Inline.Param{name: String, domain: F.Term.t}
  Inline.Local{name: String, domain: F.Term.t, value: F.Term.t}

type Inline.context is Data:
  Inline.Context{checker: C.Check.ctx, domains: List<&2, Inline.local>}

def Inline.Semantics() -> Type:
  R.Erase.Semantics

def Inline.call_univ_state(ops: Inline.Semantics, checker: C.Check.ctx, term: F.Term.t) -> R.Erase.State<F.Level.t>:
  R.Erase.semantic_univ_state(ops, checker, term)

def Inline.call_infer_state(ops: Inline.Semantics, checker: C.Check.ctx, quantity: F.Quantity.t, term: F.Term.t) -> R.Erase.State<F.Value.t>:
  R.Erase.semantic_infer_state(ops, checker, quantity, term)

def Inline.call_quote_state(ops: Inline.Semantics, globals: F.Global.t, size: Nat, value: F.Value.t) -> R.Erase.State<F.Term.t>:
  R.Erase.semantic_quote_state(ops, globals, size, value)

def Inline.bind_state(-A: Data, -B: Data, r: R.Erase.State<A>, next: A -> R.Erase.State<B>) -> R.Erase.State<B>:
  R.Erase.State.bind(A, B, r, next)

def Inline.root(context: Inline.context) -> Inline.context:
  Inline.Context{+checker, domains} = context
  Inline.Context{C.Check.make(C.Check.global(checker), C.Check.budget(checker)), Nil{}}

def Inline.keep_expected(closed: Bool, ty: F.Term.t) -> Maybe<&2, F.Term.t>:
  match closed:
    case True{}: Some{ty}
    case False{}: None{}

def Inline.source_expected(expected: Maybe<&2, F.Term.t>, +depth: Nat) -> Maybe<&2, F.Term.t>:
  match expected:
    case None{}: None{}
    case Some{+ty}:
      Inline.keep_expected(Inline.closed(depth, ty), ty)

def Inline.proof_error_state(reason: F.Error.t) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match reason:
    case F.Error.Cannot_infer{message}: R.Erase.Return{None{}}
    case other: R.Erase.Raise{other}

def Inline.inferred_type_value(~ops: Inline.Semantics, inferred: Result<&2,&2,F.Error.t,F.Value.t>, +checker: C.Check.ctx) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match inferred:
    case Fail{reason}: Inline.proof_error_state(reason)
    case Done{value}:
      Inline.bind_state(F.Term.t, Maybe<&2, F.Term.t>, Inline.call_quote_state(ops, C.Check.global(checker), C.Check.size(checker), value), ty => R.Erase.Return{Some{ty}})

def Inline.inferred_type_state(~ops: Inline.Semantics, inferred: R.Erase.State<F.Value.t>, +checker: C.Check.ctx) -> R.Erase.State<Maybe<&2,F.Term.t>>:
  R.Erase.State.attempt(F.Value.t,Maybe<&2,F.Term.t>,inferred,result => Inline.inferred_type_value(~ops,result,checker))

def Inline.infer_closed_state(~ops: Inline.Semantics, closed: Bool, +checker: C.Check.ctx, term: F.Term.t) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match closed:
    case False{}: R.Erase.Return{None{}}
    case True{}: Inline.inferred_type_state(~ops, Inline.call_infer_state(ops, checker, F.Quantity.Zero{}, term), checker)

def Inline.infer_source_state(~ops: Inline.Semantics, term: F.Term.t, checker: C.Check.ctx) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match term:
    case F.Term.Ann{value, ty}: R.Erase.Return{Some{ty}}
    case F.Term.Var{i}: R.Erase.Return{None{}}
    case F.Term.Global{name}: R.Erase.Return{None{}}
    case F.Term.Univ{level}: R.Erase.Return{None{}}
    case F.Term.Lit{literal}: R.Erase.Return{None{}}
    case F.Term.Auto{}: R.Erase.Return{None{}}
    case F.Term.Lan{shape, diagram}: R.Erase.Return{None{}}
    case F.Term.Ran{shape, diagram}: R.Erase.Return{None{}}
    case +other: Inline.infer_closed_state(~ops, Inline.closed(0n, other), checker, other)

def Inline.choose_type_state(~ops: Inline.Semantics, expected: Maybe<&2, F.Term.t>, checker: C.Check.ctx, term: F.Term.t) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match expected:
    case Some{ty}: R.Erase.Return{Some{ty}}
    case None{}: Inline.infer_source_state(~ops, term, checker)

def Inline.proof_level_state(proof: Bool, ty: F.Term.t) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match proof:
    case True{}: R.Erase.Return{Some{ty}}
    case False{}: R.Erase.Return{None{}}

def Inline.classify_type_state(~ops: Inline.Semantics, ty: Maybe<&2, F.Term.t>, checker: C.Check.ctx) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match ty:
    case None{}: R.Erase.Return{None{}}
    case Some{+term}:
      Inline.bind_state(F.Level.t, Maybe<&2, F.Term.t>, Inline.call_univ_state(ops, checker, term), level =>
        Inline.proof_level_state(F.Level.equal(level, F.Level.zero), term))

def Inline.proof_closed_state(~ops: Inline.Semantics, closed: Bool, +checker: C.Check.ctx, expected: Maybe<&2, F.Term.t>, term: F.Term.t) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  match closed:
    case False{}: R.Erase.Return{None{}}
    case True{}:
      Inline.bind_state(Maybe<&2, F.Term.t>, Maybe<&2, F.Term.t>, Inline.choose_type_state(~ops, Inline.source_expected(expected, C.Check.size(checker)), checker, term), ty =>
        Inline.classify_type_state(~ops, ty, checker))

def Inline.proof_type_state(~ops: Inline.Semantics, +checker: C.Check.ctx, expected: Maybe<&2, F.Term.t>, +term: F.Term.t) -> R.Erase.State<Maybe<&2, F.Term.t>>:
  Inline.proof_closed_state(~ops, Inline.closed(C.Check.size(checker), term), checker, expected, term)

def Inline.abstract_local(local: Inline.local, body: F.Term.t) -> F.Term.t:
  match local:
    case Inline.Param{name, domain}: P.Rules.arrow(F.Quantity.Zero{}, name, domain, body)
    case Inline.Local{name, domain, value}: F.Term.Let{name, domain, value, body}

def Inline.abstract(domains: List<&2, Inline.local>, ty: F.Term.t) -> F.Term.t:
  match domains:
    case Nil{}: ty
    case local <> rest: Inline.abstract(rest, Inline.abstract_local(local, ty))

def Inline.bind_closed_state(closed: Bool, context: Inline.context, +name: String, quantity: F.Quantity.t, +domain: F.Term.t) -> R.Erase.State<Inline.context>:
  match closed:
    case False{}: R.Erase.Return{Inline.root(context)}
    case True{}:
      Inline.Context{+checker, domains} = context
      Inline.bind_state(F.Value.t, Inline.context, R.Erase.State.lift(F.Value.t, E.Eval.eval(C.Check.global(checker), C.Check.environment(checker), domain)), value =>
        R.Erase.Return{Inline.Context{C.Check.bind(name, quantity, value, checker), Inline.Param{name, domain} <> domains}})

def Inline.bind_domain_state(+context: Inline.context, name: String, quantity: F.Quantity.t, +domain: F.Term.t) -> R.Erase.State<Inline.context>:
  Inline.Context{checker, domains} = context
  Inline.bind_closed_state(Inline.closed(C.Check.size(checker), domain), context, name, quantity, domain)

def Inline.proposition_state(~ops: Inline.Semantics, checker: C.Check.ctx, domain: F.Term.t) -> R.Erase.State<Bool>:
  Inline.bind_state(F.Level.t, Bool, Inline.call_univ_state(ops, checker, domain), level => R.Erase.Return{F.Level.equal(level, F.Level.zero)})

def Inline.define_closed_state(closed: Bool, context: Inline.context, +name: String, +domain: F.Term.t, +value: F.Term.t) -> R.Erase.State<Inline.context>:
  match closed:
    case False{}: R.Erase.Return{Inline.root(context)}
    case True{}:
      Inline.Context{+checker, domains} = context
      Inline.bind_state(F.Value.t, Inline.context, R.Erase.State.lift(F.Value.t, E.Eval.eval(C.Check.global(checker), C.Check.environment(checker), domain)), ty =>
        Inline.bind_state(F.Value.t, Inline.context, R.Erase.State.lift(F.Value.t, E.Eval.eval(C.Check.global(checker), C.Check.environment(checker), value)), definition =>
          R.Erase.Return{Inline.Context{C.Check.define(name, F.Quantity.Zero{}, ty, definition, checker), Inline.Local{name, domain, value} <> domains}}))

def Inline.define_let_state(+context: Inline.context, name: String, +domain: F.Term.t, +value: F.Term.t) -> R.Erase.State<Inline.context>:
  Inline.Context{checker, domains} = context
  +depth = C.Check.size(checker)
  Inline.define_closed_state(Bool.and(Inline.closed(depth, domain), Inline.closed(depth, value)), context, name, domain, value)

def Inline.bind_proof_state(proof: Bool, context: Inline.context, name: String, domain: F.Term.t, value: F.Term.t) -> R.Erase.State<Inline.context>:
  match proof:
    case True{}: Inline.bind_domain_state(context, name, F.Quantity.Zero{}, domain)
    case False{}: Inline.define_let_state(context, name, domain, value)

def Inline.bind_let_closed_state(~ops: Inline.Semantics, closed: Bool, +context: Inline.context, name: String, +domain: F.Term.t, value: F.Term.t) -> R.Erase.State<Inline.context>:
  match closed:
    case False{}: R.Erase.Return{Inline.root(context)}
    case True{}:
      Inline.Context{checker, domains} = context
      Inline.bind_state(Bool, Inline.context, Inline.proposition_state(~ops, checker, domain), proof => Inline.bind_proof_state(proof, context, name, domain, value))

def Inline.bind_let_state(~ops: Inline.Semantics, +context: Inline.context, name: String, +domain: F.Term.t, +value: F.Term.t) -> R.Erase.State<Inline.context>:
  Inline.Context{checker, domains} = context
  +depth = C.Check.size(checker)
  Inline.bind_let_closed_state(~ops, Bool.and(Inline.closed(depth, domain), Inline.closed(depth, value)), context, name, domain, value)

def Inline.needed_closed_state(~ops: Inline.Semantics, needed: Bool, checker: C.Check.ctx, domain: F.Term.t) -> R.Erase.State<Bool>:
  match needed:
    case False{}: R.Erase.Return{False{}}
    case True{}: Inline.proposition_state(~ops, checker, domain)

def Inline.needed_proof_state(~ops: Inline.Semantics, context: Inline.context, +domain: F.Term.t, body: F.Term.t) -> R.Erase.State<Bool>:
  Inline.Context{+checker, domains} = context
  Inline.needed_closed_state(~ops, Bool.and(Inline.closed(C.Check.size(checker), domain), Inline.typed(0n, body)), checker, domain)

def Inline.diagram_point_state(point: Maybe<&2, F.Triple3<F.Quantity.t, String, F.Term.t>>, context: Inline.context) -> R.Erase.State<Inline.context>:
  match point:
    case Some{F.Triple3{q, name, domain}}: Inline.bind_domain_state(context, name, q, domain)
    case None{}: R.Erase.Return{context}

def Inline.diagram_context_state(context: Inline.context, s: F.Shape.t<F.Term.t>) -> R.Erase.State<Inline.context>:
  Inline.diagram_point_state(P.Rules.as_vpi(F.Term.t, s), context)

def Inline.present(-A: Data, value: Maybe<&2, A>) -> Bool:
  match value:
    case None{}: False{}
    case Some{x}: True{}

def Inline.reserved(+globals: F.Global.t, +name: String) -> Bool:
  Bool.or(Inline.present(F.Global.entry, F.Global.find(name, globals)), Inline.present(F.Positivity.family, F.Global.find_family(name, globals)))

@unsafe
def Inline.fresh_step(reserved: Bool, +globals: F.Global.t, +next: Nat, name: String) -> F.Pair2<String, Inline.state>:
  match reserved:
    case False{}: F.Pair2{name, Inline.State{globals, next}}
    case True{}:
      +candidate = "__attest_inline_proof_" ++ Nat.show(next)
      Inline.fresh_step(Inline.reserved(globals, candidate), globals, 1n+next, candidate)

def Inline.fresh(state: Inline.state) -> F.Pair2<String, Inline.state>:
  Inline.State{+globals, +next} = state
  +name = "__attest_inline_proof_" ++ Nat.show(next)
  Inline.fresh_step(Inline.reserved(globals, name), globals, 1n+next, name)

def Inline.reverse(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}: acc
    case h <> t: Inline.reverse(A, t, h <> acc)

def Inline.quote_payload_state(~ops: Inline.Semantics, xs: List<&2, F.Value.t>, +globals: F.Global.t, +size: Nat) -> R.Erase.State<List<&2, F.Term.t>>:
  match xs:
    case Nil{}: R.Erase.Return{Nil{}}
    case h <> t:
      do R.Erase.State<List<&2, F.Term.t>>:
        first: F.Term.t <- Inline.call_quote_state(ops, globals, size, h)
        rest: List<&2, F.Term.t> <- Inline.quote_payload_state(~ops, t, globals, size)
        R.Erase.Return{first <> rest}

def Inline.instantiate_ran_state(~ops: Inline.Semantics, ran: Maybe<&2, F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>>, +globals: F.Global.t, +size: Nat, +ix: Nat, head: F.Term.t) -> R.Erase.State<F.Pair2<F.Term.t, F.Value.t>>:
  match ran:
    case None{}: R.Erase.Raise{F.Error.Mismatch{"proof postulate lost its telescope"}}
    case Some{F.Triple3{+shape, codomain, universe}}:
      do R.Erase.State<F.Pair2<F.Term.t, F.Value.t>>:
        payload: List<&2, F.Term.t> <- Inline.quote_payload_state(~ops, F.Shape.payload(F.Value.t, shape), globals, size)
        s: F.Shape.t<F.Term.t> <- R.Erase.State.lift(F.Shape.t<F.Term.t>, F.Shape.with_payload(F.Value.t, F.Term.t, shape, payload))
        cod: F.Value.t <- R.Erase.State.lift(F.Value.t, E.Eval.open_closure(globals, codomain, [F.Value.var((size - (1n+ix : Nat) : Nat))]))
        R.Erase.Return{F.Pair2{F.Term.Out{s, F.Term.APt{F.Quantity.Zero{}, F.Term.Var{ix}}, head}, cod}}

def Inline.instantiate_local_state(~ops: Inline.Semantics, local: Inline.local, +globals: F.Global.t, size: Nat, ix: Nat, value: F.Pair2<F.Term.t, F.Value.t>) -> R.Erase.State<F.Pair2<F.Term.t, F.Value.t>>:
  match local:
    case Inline.Local{name, domain, definition}: R.Erase.Return{value}
    case Inline.Param{name, domain}:
      F.Pair2{head, ty} = value
      Inline.bind_state(F.Value.t, F.Pair2<F.Term.t, F.Value.t>, R.Erase.State.lift(F.Value.t, E.Eval.whnf(globals, ty)), normal =>
        Inline.instantiate_ran_state(~ops, F.Value.as_ran(normal), globals, size, ix, head))

def Inline.instantiate_loop_state(~ops: Inline.Semantics, locals: List<&2, Inline.local>, +ix: Nat, +globals: F.Global.t, +size: Nat, value: F.Pair2<F.Term.t, F.Value.t>) -> R.Erase.State<F.Pair2<F.Term.t, F.Value.t>>:
  match locals:
    case Nil{}: R.Erase.Return{value}
    case local <> rest:
      Inline.bind_state(F.Pair2<F.Term.t, F.Value.t>, F.Pair2<F.Term.t, F.Value.t>, Inline.instantiate_loop_state(~ops, rest, 1n+ix, globals, size, value), next =>
        Inline.instantiate_local_state(~ops, local, globals, size, ix, next))

def Inline.instantiated_head(value: F.Pair2<F.Term.t, F.Value.t>) -> F.Term.t:
  F.Pair2{head, ty} = value
  head

def Inline.instantiate_size_state(~ops: Inline.Semantics, size: Nat, locals: List<&2, Inline.local>, +globals: F.Global.t, name: String, ty: F.Term.t) -> R.Erase.State<F.Term.t>:
  match size:
    case 0n: R.Erase.Return{F.Term.Global{name}}
    case 1n+p:
      do R.Erase.State<F.Term.t>:
        value: F.Value.t <- R.Erase.State.lift(F.Value.t, E.Eval.eval(globals, Nil{}, ty))
        result: F.Pair2<F.Term.t, F.Value.t> <- Inline.instantiate_loop_state(~ops, locals, 0n, globals, 1n+p, F.Pair2{F.Term.Global{name}, value})
        R.Erase.Return{Inline.instantiated_head(result)}

def Inline.instantiate_state(~ops: Inline.Semantics, context: Inline.context, globals: F.Global.t, name: String, ty: F.Term.t) -> R.Erase.State<F.Term.t>:
  Inline.Context{checker, domains} = context
  Inline.instantiate_size_state(~ops, C.Check.size(checker), domains, globals, name, ty)

def Inline.strings_equal(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}: True{}
        case other: False{}
    case h <> t:
      match b:
        case Nil{}: False{}
        case h2 <> t2: Bool.and(String.eq(h, h2), Inline.strings_equal(t, t2))

def Inline.optional_string_equal(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match a:
    case None{}:
      match b:
        case None{}: True{}
        case Some{x}: False{}
    case Some{x}:
      match b:
        case None{}: False{}
        case Some{y}: String.eq(x, y)

def Inline.binders_equal(a: List<&2, F.Pair2<F.Quantity.t, String>>, b: List<&2, F.Pair2<F.Quantity.t, String>>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}: True{}
        case other: False{}
    case F.Pair2{q, name} <> t:
      match b:
        case Nil{}: False{}
        case F.Pair2{q2, name2} <> t2:
          Bool.and(F.Quantity.equal(q, q2), Bool.and(String.eq(name, name2), Inline.binders_equal(t, t2)))

def Inline.address_shell_equal(a: F.Term.addr, b: F.Term.addr) -> Bool:
  match a:
    case F.Term.APt{q, term}:
      match b:
        case F.Term.APt{q2, term2}: F.Quantity.equal(q, q2)
        case other: False{}
    case F.Term.ALeg{k}:
      match b:
        case F.Term.ALeg{j}: Nat.is_eq(k, j)
        case other: False{}
    case F.Term.ACtor{name}:
      match b:
        case F.Term.ACtor{name2}: String.eq(name, name2)
        case other: False{}

def Inline.motive_shell_equal(a: Maybe<&2, F.Term.motive>, b: Maybe<&2, F.Term.motive>) -> Bool:
  match a:
    case None{}:
      match b:
        case None{}: True{}
        case Some{x}: False{}
    case Some{F.Term.Motive{ind, idx, self, body}}:
      match b:
        case None{}: False{}
        case Some{F.Term.Motive{ind2, idx2, self2, body2}}:
          Bool.and(Inline.optional_string_equal(ind, ind2), Bool.and(Inline.strings_equal(idx, idx2), String.eq(self, self2)))

def Inline.legs_shell_equal(a: List<&2, F.Term.leg>, b: List<&2, F.Term.leg>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}: True{}
        case other: False{}
    case F.Term.Leg{binders, body} <> rest:
      match b:
        case Nil{}: False{}
        case F.Term.Leg{binders2, body2} <> rest2: Bool.and(Inline.binders_equal(binders, binders2), Inline.legs_shell_equal(rest, rest2))

def Inline.branches_shell_equal(a: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, b: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}: True{}
        case other: False{}
    case F.Pair2{addr, F.Term.Leg{binders, body}} <> rest:
      match b:
        case Nil{}: False{}
        case F.Pair2{addr2, F.Term.Leg{binders2, body2}} <> rest2:
          Bool.and(Inline.address_shell_equal(addr, addr2), Bool.and(Inline.binders_equal(binders, binders2), Inline.branches_shell_equal(rest, rest2)))

def Inline.term_shell_equal(a: F.Term.t, b: F.Term.t) -> Bool:
  match a:
    case F.Term.Var{i}:
      match b:
        case F.Term.Var{j}: Nat.is_eq(i, j)
        case other: False{}
    case F.Term.Univ{level}:
      match b:
        case F.Term.Univ{level2}: F.Level.equal(level, level2)
        case other: False{}
    case F.Term.Global{name}:
      match b:
        case F.Term.Global{name2}: String.eq(name, name2)
        case other: False{}
    case F.Term.Lit{literal}:
      match b:
        case F.Term.Lit{literal2}: F.Literal.equal(literal, literal2)
        case other: False{}
    case F.Term.Auto{}:
      match b:
        case F.Term.Auto{}: True{}
        case other: False{}
    case F.Term.Lan{s, diagram}:
      match b:
        case F.Term.Lan{s2, diagram2}: R.Erase.shape_shell_equal(F.Term.t, F.Term.t, s, s2)
        case other: False{}
    case F.Term.Ran{s, diagram}:
      match b:
        case F.Term.Ran{s2, diagram2}: R.Erase.shape_shell_equal(F.Term.t, F.Term.t, s, s2)
        case other: False{}
    case F.Term.In{s, addr, args}:
      match b:
        case F.Term.In{s2, addr2, args2}: Bool.and(R.Erase.shape_shell_equal(F.Term.t, F.Term.t, s, s2), Inline.address_shell_equal(addr, addr2))
        case other: False{}
    case F.Term.Out{s, addr, head}:
      match b:
        case F.Term.Out{s2, addr2, head2}: Bool.and(R.Erase.shape_shell_equal(F.Term.t, F.Term.t, s, s2), Inline.address_shell_equal(addr, addr2))
        case other: False{}
    case F.Term.Sec{s, legs}:
      match b:
        case F.Term.Sec{s2, legs2}: Bool.and(R.Erase.shape_shell_equal(F.Term.t, F.Term.t, s, s2), Inline.legs_shell_equal(legs, legs2))
        case other: False{}
    case F.Term.Let{name, ty, value, body}:
      match b:
        case F.Term.Let{name2, ty2, value2, body2}: String.eq(name, name2)
        case other: False{}
    case F.Term.Ann{value, ty}:
      match b:
        case F.Term.Ann{value2, ty2}: True{}
        case other: False{}
    case F.Term.Elim{F.Term.Elimination{s, scrut, quantity, motive, branches}}:
      match b:
        case F.Term.Elim{F.Term.Elimination{s2, scrut2, quantity2, motive2, branches2}}:
          Bool.and(R.Erase.shape_shell_equal(F.Term.t, F.Term.t, s, s2), Bool.and(F.Quantity.equal(quantity, quantity2), Bool.and(Inline.motive_shell_equal(motive, motive2), Inline.branches_shell_equal(branches, branches2))))
        case other: False{}

type Inline.EqualTask is Data:
  Inline.EqualTerms{left: F.Term.t, right: F.Term.t}
  Inline.EqualChildren{left: List<&2, F.Pair2<Nat, F.Term.t>>, right: List<&2, F.Pair2<Nat, F.Term.t>>}

@unsafe
def Inline.equal_task(task: Inline.EqualTask) -> Bool:
  match task:
    case Inline.EqualTerms{+a, +b}:
      Bool.and(Inline.term_shell_equal(a, b), Inline.equal_task(Inline.EqualChildren{Inline.children(a), Inline.children(b)}))
    case Inline.EqualChildren{a, b}:
      match a:
        case Nil{}:
          match b:
            case Nil{}: True{}
            case other: False{}
        case F.Pair2{shift, child} <> rest:
          match b:
            case Nil{}: False{}
            case F.Pair2{shift2, child2} <> rest2:
              Bool.and(Nat.is_eq(shift, shift2), Bool.and(Inline.equal_task(Inline.EqualTerms{child, child2}), Inline.equal_task(Inline.EqualChildren{rest, rest2})))

def Inline.term_equal(a: F.Term.t, b: F.Term.t) -> Bool:
  Inline.equal_task(Inline.EqualTerms{a, b})

def Inline.optional_nat_equal(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a:
    case None{}:
      match b:
        case None{}: True{}
        case Some{x}: False{}
    case Some{x}:
      match b:
        case None{}: False{}
        case Some{y}: Nat.is_eq(x, y)

def Inline.prim_tag(prim: F.Prim.t) -> Nat:
  match prim:
    case F.Prim.Nat_add{}: 0n
    case F.Prim.Nat_sub{}: 1n
    case F.Prim.Nat_mul{}: 2n
    case F.Prim.Nat_eq{}: 3n
    case F.Prim.Nat_lt{}: 4n

def Inline.entry_equal(a: F.Global.entry, b: F.Global.entry) -> Bool:
  match a:
    case F.Global.Axiom{F.Global.AxiomEntry{ty}}:
      match b:
        case F.Global.Axiom{F.Global.AxiomEntry{ty2}}: Inline.term_equal(ty, ty2)
        case other: False{}
    case F.Global.Prim{F.Global.PrimEntry{ty, prim}}:
      match b:
        case F.Global.Prim{F.Global.PrimEntry{ty2, prim2}}: Bool.and(Inline.term_equal(ty, ty2), Nat.is_eq(Inline.prim_tag(prim), Inline.prim_tag(prim2)))
        case other: False{}
    case F.Global.Def{F.Global.DefEntry{ty, body, red, rec_arg, partial}}:
      match b:
        case F.Global.Def{F.Global.DefEntry{ty2, body2, red2, rec_arg2, partial2}}:
          Bool.and(Inline.term_equal(ty, ty2), Bool.and(Inline.term_equal(body, body2), Bool.and(Bool.not(Bool.xor(red, red2)), Bool.and(Inline.optional_nat_equal(rec_arg, rec_arg2), Bool.not(Bool.xor(partial, partial2))))))
        case other: False{}

def Inline.lambda_bind_state(closed: Bool, context: Inline.context, name: String, quantity: F.Quantity.t, domain: F.Term.t, codomain: F.Term.t) -> R.Erase.State<Maybe<&2, F.Pair2<Inline.context, F.Term.t>>>:
  match closed:
    case False{}: R.Erase.Return{None{}}
    case True{}:
      Inline.bind_state(Inline.context, Maybe<&2, F.Pair2<Inline.context, F.Term.t>>, Inline.bind_domain_state(context, name, quantity, domain), next => R.Erase.Return{Some{F.Pair2{next, codomain}}})

def Inline.lambda_point_state(point: Maybe<&2, F.Triple3<F.Quantity.t, String, F.Term.t>>, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +context: Inline.context, codomain: F.Term.t) -> R.Erase.State<Maybe<&2, F.Pair2<Inline.context, F.Term.t>>>:
  match point:
    case None{}: R.Erase.Return{None{}}
    case Some{F.Triple3{quantity, ignored, +domain}}:
      match binders:
        case F.Pair2{binder_quantity, name} <> Nil{}:
          Inline.Context{checker, domains} = context
          Inline.lambda_bind_state(Inline.closed(C.Check.size(checker), domain), context, name, quantity, domain, codomain)
        case other: R.Erase.Return{None{}}

def Inline.lambda_type_state(expected: Maybe<&2, F.Term.t>, leg: F.Term.leg, context: Inline.context) -> R.Erase.State<Maybe<&2, F.Pair2<Inline.context, F.Term.t>>>:
  match expected:
    case None{}: R.Erase.Return{None{}}
    case Some{ty}:
      match ty:
        case F.Term.Ran{shape, codomain}:
          F.Term.Leg{binders, body} = leg
          Inline.lambda_point_state(P.Rules.as_vpi(F.Term.t, shape), binders, context, codomain)
        case other: R.Erase.Return{None{}}

def Inline.scope_closed(closed: Bool, context: Inline.context) -> Inline.context:
  match closed:
    case True{}: Inline.root(context)
    case False{}: context

def Inline.leg_scope(binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> Inline.context:
  match binders:
    case Nil{}: context
    case other: Inline.root(context)

# Constructor types are closed over earlier fields. Keep their source syntax
# when extending an outer scope so universe distinctions survive sealing.
def Inline.branch_fields_valid(fields: F.Positivity.telescope, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +depth: Nat) -> Bool:
  match fields binders:
    case Nil{} Nil{}: True{}
    case Con{F.Triple3{quantity, ignored, domain}, rest} Con{F.Pair2{binder_quantity, name}, more}:
      Bool.and(Bool.and(F.Quantity.equal(quantity, binder_quantity), Inline.closed(depth, domain)), Inline.branch_fields_valid(rest, more, (depth + 1n : Nat)))
    case Nil{} Con{binder, more}: False{}
    case Con{field, rest} Nil{}: False{}

def Inline.branch_fields_state(fields: F.Positivity.telescope, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match fields binders:
    case Nil{} Nil{}: R.Erase.Return{Some{context}}
    case Con{F.Triple3{quantity, ignored, domain}, rest} Con{F.Pair2{binder_quantity, name}, more}:
      Inline.bind_state(Inline.context, Maybe<&2, Inline.context>, Inline.bind_domain_state(context, name, quantity, domain), scope =>
        Inline.branch_fields_state(rest, more, scope))
    case Nil{} Con{binder, more}: R.Erase.Return{None{}}
    case Con{field, rest} Nil{}: R.Erase.Return{None{}}

def Inline.branch_valid_state(valid: Bool, fields: F.Positivity.telescope, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match valid:
    case False{}: R.Erase.Return{None{}}
    case True{}: Inline.branch_fields_state(fields, binders, context)

def Inline.branch_ctor_state(ctor: Maybe<&2, F.Positivity.ctor>, +binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match ctor:
    case None{}: R.Erase.Return{None{}}
    case Some{F.Positivity.Ctor{name, +fields, indices, arity, recursive}}:
      Inline.branch_valid_state(Inline.branch_fields_valid(fields, binders, 0n), fields, binders, context)

def Inline.branch_family_state(family: Maybe<&2, F.Positivity.family>, name: String, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match family:
    case None{}: R.Erase.Return{None{}}
    case Some{+value}:
      F.Positivity.Family{family_name, params, indices, level, status, ctors, positive} = value
      match params:
        case Nil{}: Inline.branch_ctor_state(M.Mu.ctor_of(name, value), binders, context)
        case Con{param, rest}: R.Erase.Return{None{}}

def Inline.branch_view_state(view: Maybe<&2, F.Pair2<String, List<&2, F.Term.t>>>, address: F.Term.addr, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match view address:
    case Some{F.Pair2{family, indices}} F.Term.ACtor{name}:
      Inline.Context{checker, domains} = context
      Inline.branch_family_state(F.Global.find_family(family, C.Check.global(checker)), name, binders, context)
    case other address: R.Erase.Return{None{}}

def Inline.branch_context_state(shape: F.Shape.t<F.Term.t>, address: F.Term.addr, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  Inline.branch_view_state(F.Shape.inductive(F.Term.t, shape), address, binders, context)

# Recover declared types without quoting evaluated universes or proof bodies.
def Inline.local_domain(local: Inline.local) -> F.Term.t:
  match local:
    case Inline.Param{name, ty}: ty
    case Inline.Local{name, ty, value}: ty

def Inline.local_type(locals: List<&2, Inline.local>, index: Nat, skipped: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match locals index:
    case Nil{} index: Done{None{}}
    case local <> rest 0n:
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        ty: F.Term.t <- S.Source.term(S.Source.Shift{(skipped + 1n : Nat)}, 0n, Inline.local_domain(local))
        Done{Some{ty}}
    case local <> rest 1n+n: Inline.local_type(rest, n, (skipped + 1n : Nat))

def Inline.global_type(entry: Maybe<&2, F.Global.entry>) -> Maybe<&2, F.Term.t>:
  match entry:
    case None{}: None{}
    case Some{value}: Some{F.Global.entry_ty(value)}

# Alias bodies are checked in their declaration scope before entering this one.
def Inline.global_alias(entry: Maybe<&2, F.Global.entry>) -> Maybe<&2, F.Term.t>:
  match entry:
    case Some{F.Global.Def{F.Global.DefEntry{ty, body, True{}, None{}, False{}}}}:
      Inline.source_expected(Some{body}, 0n)
    case other: None{}

def Inline.shift_alias(valid: Bool, value: F.Term.t, skipped: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match valid:
    case False{}: Done{None{}}
    case True{}:
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        shifted: F.Term.t <- S.Source.term(S.Source.Shift{(skipped + 1n : Nat)}, 0n, value)
        Done{Some{shifted}}

def Inline.local_alias(locals: List<&2, Inline.local>, index: Nat, skipped: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match locals index:
    case Nil{} index: Done{None{}}
    case Inline.Param{name, ty} <> rest 0n: Done{None{}}
    case Inline.Local{name, ty, +value} <> +rest 0n:
      Inline.shift_alias(Inline.closed(Inline.length(Inline.local, rest), value), value, skipped)
    case local <> rest 1n+n: Inline.local_alias(rest, n, (skipped + 1n : Nat))

# Each alias hop consumes one declaration; cycles exhaust the finite context.
def Inline.alias_type(fuel: Nat, ty: Maybe<&2, F.Term.t>, +context: Inline.context) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match fuel ty:
    case 0n ty: Done{None{}}
    case 1n+remaining None{}: Done{None{}}
    case 1n+remaining Some{F.Term.Global{name}}:
      Inline.Context{checker, domains} = context
      Inline.alias_type(remaining, Inline.global_alias(F.Global.find(name, C.Check.global(checker))), context)
    case 1n+remaining Some{F.Term.Var{index}}:
      Inline.Context{checker, domains} = context
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        body: Maybe<&2, F.Term.t> <- Inline.local_alias(domains, index, 0n)
        Inline.alias_type(remaining, body, context)
    case 1n+remaining Some{other}: Done{Some{other}}

def Inline.source_variables(count: Nat, +index: Nat) -> List<&2, F.Term.t>:
  match count:
    case 0n: Nil{}
    case 1n+n: F.Term.Var{index} <> Inline.source_variables(n, (index + 1n : Nat))

def Inline.source_alias_head(ty: Maybe<&2, F.Term.t>, +context: Inline.context) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  Inline.Context{checker, domains} = context
  aliases = (Inline.length(F.Pair2<String, F.Global.entry>, F.Global.entries(C.Check.global(checker))) + Inline.length(Inline.local, domains) : Nat)
  Inline.alias_type((aliases + 1n : Nat), ty, context)

def Inline.let_closed(valid: Bool, value: F.Term.t, body: F.Term.t, depth: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match valid:
    case True{}:
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        reduced: F.Term.t <- S.Source.term(S.Source.Parameters{value <> Inline.source_variables(depth, 0n)}, 0n, body)
        Done{Some{reduced}}
    case False{}: Done{None{}}

def Inline.let_type(ty: Maybe<&2, F.Term.t>, context: Inline.context, next: Maybe<&2, F.Term.t> -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match ty:
    case Some{F.Term.Let{name, +annotation, +value, +body}}:
      Inline.Context{checker, domains} = context
      +depth = C.Check.size(checker)
      valid = Bool.and(Inline.closed(depth, annotation), Bool.and(Inline.closed(depth, value), Inline.closed((depth + 1n : Nat), body)))
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        reduced: Maybe<&2, F.Term.t> <- Inline.let_closed(valid, value, body, depth)
        next(reduced)
    case other: Done{other}

def Inline.let_exhausted(ty: Maybe<&2, F.Term.t>) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match ty:
    case Some{F.Term.Let{name, annotation, value, body}}: Done{None{}}
    case other: Done{other}

# Alias chains keep their declaration bound between let reductions.
# A separate bound prevents cycles that pass through a let from restarting forever.
def Inline.source_let_type(fuel: Nat, ty: Maybe<&2, F.Term.t>, +context: Inline.context) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match fuel:
    case 0n:
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        expanded: Maybe<&2, F.Term.t> <- Inline.source_alias_head(ty, context)
        Inline.let_exhausted(expanded)
    case 1n+remaining:
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        expanded: Maybe<&2, F.Term.t> <- Inline.source_alias_head(ty, context)
        Inline.let_type(expanded, context, reduced => Inline.source_let_type(remaining, reduced, context))

def Inline.source_alias_type(ty: Maybe<&2, F.Term.t>, context: Inline.context) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  Inline.source_let_type(64n, ty, context)

def Inline.lambda_context_state(expected: Maybe<&2, F.Term.t>, leg: F.Term.leg, +context: Inline.context) -> R.Erase.State<Maybe<&2, F.Pair2<Inline.context, F.Term.t>>>:
  Inline.bind_state(Maybe<&2, F.Term.t>, Maybe<&2, F.Pair2<Inline.context, F.Term.t>>, R.Erase.State.lift(Maybe<&2, F.Term.t>, Inline.source_alias_type(expected, context)), expanded =>
    Inline.lambda_type_state(expanded, leg, context))

# Substitution removes the function binder and preserves every outer variable.
# Keep source syntax: semantic readback can erase dependent proof arguments.
def Inline.application_closed(valid: Bool, codomain: F.Term.t, argument: F.Term.t, depth: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match valid:
    case False{}: Done{None{}}
    case True{}:
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        ty: F.Term.t <- S.Source.term(S.Source.Parameters{argument <> Inline.source_variables(depth, 0n)}, 0n, codomain)
        Done{Some{ty}}

def Inline.application_point(point: Maybe<&2, F.Triple3<F.Quantity.t, String, F.Term.t>>, +codomain: F.Term.t, +argument: F.Term.t, +depth: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match point:
    case None{}: Done{None{}}
    case Some{F.Triple3{q, name, domain}}:
      Inline.application_closed(Bool.and(Inline.closed((depth + 1n : Nat), codomain), Inline.closed(depth, argument)), codomain, argument, depth)

def Inline.application_type(ty: Maybe<&2, F.Term.t>, address: F.Term.addr, depth: Nat) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match ty address:
    case Some{F.Term.Ran{shape, codomain}} F.Term.APt{quantity, argument}:
      Inline.application_point(P.Rules.as_vpi(F.Term.t, shape), codomain, argument, depth)
    case other address: Done{None{}}

def Inline.application_source_type(ty: Maybe<&2, F.Term.t>, address: F.Term.addr, +context: Inline.context) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  Inline.Context{checker, domains} = context
  do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
    expanded: Maybe<&2, F.Term.t> <- Inline.source_alias_type(ty, context)
    Inline.application_type(expanded, address, C.Check.size(checker))

def Inline.scrutinee_type(term: F.Term.t, +context: Inline.context) -> Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
  match term:
    case F.Term.Ann{value, ty}: Done{Some{ty}}
    case F.Term.Var{index}:
      Inline.Context{checker, domains} = context
      Inline.local_type(domains, index, 0n)
    case F.Term.Global{name}:
      Inline.Context{checker, domains} = context
      Done{Inline.global_type(F.Global.find(name, C.Check.global(checker)))}
    case F.Term.Out{shape, address, head}:
      Inline.Context{checker, domains} = context
      do Result<&2,&2,F.Error.t,Maybe<&2, F.Term.t>>:
        ty: Maybe<&2, F.Term.t> <- Inline.scrutinee_type(head, context)
        Inline.application_source_type(ty, address, context)
    case other: Done{None{}}

def Inline.parameter_legs(legs: List<&2, F.Term.leg>, reversed: List<&2, F.Term.t>) -> Maybe<&2, List<&2, F.Term.t>>:
  match legs:
    case Nil{}: Some{reversed}
    case F.Term.Leg{Nil{}, body} <> rest: Inline.parameter_legs(rest, body <> reversed)
    case other: None{}

def Inline.parameter_width_valid(valid: Bool, legs: List<&2, F.Term.leg>) -> Maybe<&2, List<&2, F.Term.t>>:
  match valid:
    case True{}: Inline.parameter_legs(legs, Nil{})
    case False{}: None{}

def Inline.parameter_width(width: Maybe<&2, Nat>, +legs: List<&2, F.Term.leg>) -> Maybe<&2, List<&2, F.Term.t>>:
  match width:
    case Some{count}: Inline.parameter_width_valid(Nat.is_eq(count, Inline.length(F.Term.leg, legs)), legs)
    case None{}: None{}

def Inline.parameter_diagram(diagram: F.Term.t) -> Maybe<&2, List<&2, F.Term.t>>:
  match diagram:
    case F.Term.Sec{shape, legs}: Inline.parameter_width(F.Shape.collection(F.Term.t, shape), legs)
    case other: None{}

def Inline.branch_arguments_equal(equal: Bool, diagram: F.Term.t) -> Maybe<&2, List<&2, F.Term.t>>:
  match equal:
    case True{}: Inline.parameter_diagram(diagram)
    case False{}: None{}

def Inline.branch_arguments(ty: Maybe<&2, F.Term.t>, shape: F.Shape.t<F.Term.t>) -> Maybe<&2, List<&2, F.Term.t>>:
  match ty:
    case Some{F.Term.Lan{source_shape, +diagram}}:
      Inline.branch_arguments_equal(Inline.term_equal(F.Term.Lan{shape, diagram}, F.Term.Lan{source_shape, diagram}), diagram)
    case other: None{}

def Inline.arguments_closed(arguments: List<&2, F.Term.t>, +depth: Nat) -> Bool:
  match arguments:
    case Nil{}: True{}
    case first <> rest: Bool.and(Inline.closed(depth, first), Inline.arguments_closed(rest, depth))

def Inline.specialize_fields(fields: F.Positivity.telescope, +arguments: List<&2, F.Term.t>, +depth: Nat) -> Result<&2,&2,F.Error.t,F.Positivity.telescope>:
  match fields:
    case Nil{}: Done{Nil{}}
    case F.Triple3{quantity, name, domain} <> rest:
      do Result<&2,&2,F.Error.t,F.Positivity.telescope>:
        ty: F.Term.t <- S.Source.term(S.Source.Parameters{arguments}, depth, domain)
        more: F.Positivity.telescope <- Inline.specialize_fields(rest, arguments, (depth + 1n : Nat))
        Done{F.Triple3{quantity, name, ty} <> more}

def Inline.specialized_branch_state(valid: Bool, fields: F.Positivity.telescope, arguments: List<&2, F.Term.t>, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match valid:
    case False{}: R.Erase.Return{None{}}
    case True{}:
      Inline.bind_state(F.Positivity.telescope, Maybe<&2, Inline.context>, R.Erase.State.lift(F.Positivity.telescope, Inline.specialize_fields(fields, arguments, 0n)), specialized =>
        Inline.branch_fields_state(specialized, binders, context))

def Inline.parameterized_ctor_state(ctor: Maybe<&2, F.Positivity.ctor>, params: F.Positivity.telescope, arguments: Maybe<&2, List<&2, F.Term.t>>, +binders: List<&2, F.Pair2<F.Quantity.t, String>>, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match ctor arguments:
    case Some{F.Positivity.Ctor{name, +fields, indices, arity, recursive}} Some{+args}:
      Inline.Context{checker, domains} = context
      +count = Inline.length(F.Triple3<F.Quantity.t, String, F.Term.t>, params)
      valid = Bool.and(Nat.is_eq(count, Inline.length(F.Term.t, args)), Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.branch_fields_valid(fields, binders, count)))
      Inline.specialized_branch_state(valid, fields, args, binders, context)
    case other arguments: R.Erase.Return{None{}}

def Inline.branch_source_family_state(family: Maybe<&2, F.Positivity.family>, name: String, shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match family:
    case None{}: Inline.branch_family_state(None{}, name, binders, context)
    case Some{+value}:
      F.Positivity.Family{family_name, +params, indices, level, status, ctors, positive} = value
      match params:
        case Nil{}: Inline.branch_family_state(Some{value}, name, binders, context)
        case Con{param, rest}:
          Inline.bind_state(Maybe<&2, F.Term.t>, Maybe<&2, Inline.context>, R.Erase.State.lift(Maybe<&2, F.Term.t>, Inline.scrutinee_type(scrut, context)), ty =>
            Inline.parameterized_ctor_state(M.Mu.ctor_of(name, value), params, Inline.branch_arguments(ty, shape), binders, context))

def Inline.branch_scrutinee_view_state(view: Maybe<&2, F.Pair2<String, List<&2, F.Term.t>>>, shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, address: F.Term.addr, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match view address:
    case Some{F.Pair2{family, indices}} F.Term.ACtor{name}:
      Inline.Context{checker, domains} = context
      Inline.branch_source_family_state(F.Global.find_family(family, C.Check.global(checker)), name, shape, scrut, binders, context)
    case other address: R.Erase.Return{None{}}

def Inline.branch_scrutinee_state(+shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, address: F.Term.addr, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  Inline.branch_scrutinee_view_state(F.Shape.inductive(F.Term.t, shape), shape, scrut, address, binders, context)

# Motive indices and self are erased binders, even when family indices are not.
def Inline.motive_variables(count: Nat) -> List<&2, F.Term.t>:
  match count:
    case 0n: Nil{}
    case 1n+n:
      +index = n
      F.Term.Var{index} <> Inline.motive_variables(index)

def Inline.motive_fields_valid(fields: F.Positivity.telescope, names: List<&2, String>, +depth: Nat) -> Bool:
  match fields names:
    case Nil{} Nil{}: True{}
    case F.Triple3{quantity, old_name, domain} <> rest name <> more:
      Bool.and(Inline.closed(depth, domain), Inline.motive_fields_valid(rest, more, (depth + 1n : Nat)))
    case Nil{} name <> more: False{}
    case field <> rest Nil{}: False{}

def Inline.motive_fields_state(fields: F.Positivity.telescope, names: List<&2, String>, self: String, self_ty: F.Term.t, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match fields names:
    case Nil{} Nil{}:
      Inline.bind_state(Inline.context, Maybe<&2, Inline.context>, Inline.bind_domain_state(context, self, F.Quantity.Zero{}, self_ty), scope => R.Erase.Return{Some{scope}})
    case F.Triple3{quantity, old_name, domain} <> rest name <> more:
      Inline.bind_state(Inline.context, Maybe<&2, Inline.context>, Inline.bind_domain_state(context, name, F.Quantity.Zero{}, domain), scope =>
        Inline.motive_fields_state(rest, more, self, self_ty, scope))
    case Nil{} name <> more: R.Erase.Return{None{}}
    case field <> rest Nil{}: R.Erase.Return{None{}}

def Inline.motive_valid_state(valid: Bool, ind: String, fields: F.Positivity.telescope, +names: List<&2, String>, self: String, +arguments: List<&2, F.Term.t>, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match valid:
    case False{}: R.Erase.Return{None{}}
    case True{}:
      +count = Inline.length(String, names)
      do R.Erase.State<Maybe<&2, Inline.context>>:
        specialized: F.Positivity.telescope <- R.Erase.State.lift(F.Positivity.telescope, Inline.specialize_fields(fields, arguments, 0n))
        diagram: F.Term.t <- R.Erase.State.lift(F.Term.t, S.Source.term(S.Source.Shift{count}, 0n, P.Rules.diagram_of(Inline.reverse(F.Term.t, arguments, Nil{}))))
        Inline.motive_fields_state(specialized, names, self, F.Term.Lan{F.Shape.make_inductive(F.Term.t, ind, Inline.motive_variables(count)), diagram}, context)

def Inline.motive_arguments_state(ind: String, params: F.Positivity.telescope, +fields: F.Positivity.telescope, +names: List<&2, String>, self: String, arguments: Maybe<&2, List<&2, F.Term.t>>, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match arguments:
    case None{}: R.Erase.Return{None{}}
    case Some{+args}:
      Inline.Context{checker, domains} = context
      +count = Inline.length(F.Triple3<F.Quantity.t, String, F.Term.t>, params)
      valid = Bool.and(Nat.is_eq(count, Inline.length(F.Term.t, args)), Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.motive_fields_valid(fields, names, count)))
      Inline.motive_valid_state(valid, ind, fields, names, self, args, context)

def Inline.motive_family_state(family: Maybe<&2, F.Positivity.family>, ind: String, names: List<&2, String>, self: String, shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match family:
    case None{}: R.Erase.Return{None{}}
    case Some{F.Positivity.Family{family_name, +params, indices, level, status, ctors, positive}}:
      match params:
        case Nil{}: Inline.motive_arguments_state(ind, Nil{}, indices, names, self, Some{Nil{}}, context)
        case param <> rest:
          Inline.bind_state(Maybe<&2, F.Term.t>, Maybe<&2, Inline.context>, R.Erase.State.lift(Maybe<&2, F.Term.t>, Inline.scrutinee_type(scrut, context)), ty =>
            Inline.motive_arguments_state(ind, params, indices, names, self, Inline.branch_arguments(ty, shape), context))

def Inline.motive_selected_state(valid: Bool, shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, +ind: String, names: List<&2, String>, self: String, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match valid:
    case False{}: R.Erase.Return{None{}}
    case True{}:
      Inline.Context{checker, domains} = context
      Inline.motive_family_state(F.Global.find_family(ind, C.Check.global(checker)), ind, names, self, shape, scrut, context)

def Inline.motive_view_state(view: Maybe<&2, F.Pair2<String, List<&2, F.Term.t>>>, shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, +ind: String, +names: List<&2, String>, self: String, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match view:
    case None{}: R.Erase.Return{None{}}
    case Some{F.Pair2{family, indices}}:
      Inline.motive_selected_state(Bool.and(String.eq(ind, family), Nat.is_eq(Inline.length(F.Term.t, indices), Inline.length(String, names))), shape, scrut, ind, names, self, context)

# Plain motives bind only an erased self with the original scrutinee type.
def Inline.motive_plain_type_state(ty: Maybe<&2, F.Term.t>, self: String, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match ty:
    case None{}: R.Erase.Return{None{}}
    case Some{domain}:
      Inline.bind_state(Inline.context, Maybe<&2, Inline.context>, Inline.bind_domain_state(context, self, F.Quantity.Zero{}, domain), scope =>
        R.Erase.Return{Some{scope}})

def Inline.motive_plain_names_state(names: List<&2, String>, scrut: F.Term.t, self: String, +context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match names:
    case head <> tail: R.Erase.Return{None{}}
    case Nil{}:
      Inline.Context{checker, domains} = context
      Inline.bind_state(Maybe<&2, F.Term.t>, Maybe<&2, Inline.context>, R.Erase.State.lift(Maybe<&2, F.Term.t>, Inline.scrutinee_type(scrut, context)), ty =>
        Inline.motive_plain_type_state(Inline.source_expected(ty, C.Check.size(checker)), self, context))

def Inline.motive_plain_view_state(view: Maybe<&2, F.Pair2<String, List<&2, F.Term.t>>>, scrut: F.Term.t, names: List<&2, String>, self: String, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match view:
    case Some{family}: R.Erase.Return{None{}}
    case None{}: Inline.motive_plain_names_state(names, scrut, self, context)

def Inline.motive_context_state(+shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, ind: Maybe<&2, String>, names: List<&2, String>, self: String, context: Inline.context) -> R.Erase.State<Maybe<&2, Inline.context>>:
  match ind:
    case None{}: Inline.motive_plain_view_state(F.Shape.inductive(F.Term.t, shape), scrut, names, self, context)
    case Some{name}: Inline.motive_view_state(F.Shape.inductive(F.Term.t, shape), shape, scrut, name, names, self, context)

def Inline.motive_scope(scope: Maybe<&2, Inline.context>, context: Inline.context) -> Inline.context:
  match scope:
    case None{}: Inline.root(context)
    case Some{found}: found

def Inline.replacement_choice(equal: Bool, rewritten: F.Term.t, other: Maybe<&2, F.Term.t>) -> Maybe<&2, F.Term.t>:
  match equal:
    case True{}: Some{rewritten}
    case False{}: other

def Inline.replacement(replacements: List<&2, F.Pair2<F.Term.t, F.Term.t>>, +original: F.Term.t) -> Maybe<&2, F.Term.t>:
  match replacements:
    case Nil{}: None{}
    case F.Pair2{source, rewritten} <> rest:
      Inline.replacement_choice(Inline.term_equal(original, source), rewritten, Inline.replacement(rest, original))

def Inline.require_replacement_state(value: Maybe<&2, F.Term.t>) -> R.Erase.State<F.Term.t>:
  match value:
    case None{}: R.Erase.Raise{F.Error.Mismatch{"shape payload is absent from its traversal"}}
    case Some{term}: R.Erase.Return{term}

def Inline.replace_payload_state(xs: List<&2, F.Term.t>, +replacements: List<&2, F.Pair2<F.Term.t, F.Term.t>>) -> R.Erase.State<List<&2, F.Term.t>>:
  match xs:
    case Nil{}: R.Erase.Return{Nil{}}
    case h <> t:
      do R.Erase.State<List<&2, F.Term.t>>:
        first: F.Term.t <- Inline.require_replacement_state(Inline.replacement(replacements, h))
        rest: List<&2, F.Term.t> <- Inline.replace_payload_state(t, replacements)
        R.Erase.Return{first <> rest}

def Inline.walk_result_state() -> Type:
  R.Erase.State<F.Pair2<F.Term.t, Inline.state>>

type Inline.Task is Type:
  Inline.Walk{context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, term: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}
  Inline.Classified{proof: Maybe<&2, F.Term.t>, context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, term: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}
  Inline.Node{context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, term: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}
  Inline.SealType{context: Inline.context, state: Inline.state, ty: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}
  Inline.Domains{locals: List<&2, Inline.local>, context: Inline.context, state: Inline.state, walked: List<&2, Inline.local>, ty: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}
  Inline.DomainLocal{proof: Bool, name: String, domain: F.Term.t, value: F.Term.t, locals: List<&2, Inline.local>, context: Inline.context, state: Inline.state, walked: List<&2, Inline.local>, ty: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}
  Inline.Shape{context: Inline.context, state: Inline.state, shape: F.Shape.t<F.Term.t>, done: F.Shape.t<F.Term.t> -> Inline.state -> Inline.walk_result_state}
  Inline.Payload{terms: List<&2, F.Term.t>, replacements: List<&2, F.Pair2<F.Term.t, F.Term.t>>, context: Inline.context, state: Inline.state, done: List<&2, F.Pair2<F.Term.t, F.Term.t>> -> Inline.state -> Inline.walk_result_state}
  Inline.PayloadItem{found: Maybe<&2, F.Term.t>, original: F.Term.t, terms: List<&2, F.Term.t>, replacements: List<&2, F.Pair2<F.Term.t, F.Term.t>>, context: Inline.context, state: Inline.state, done: List<&2, F.Pair2<F.Term.t, F.Term.t>> -> Inline.state -> Inline.walk_result_state}
  Inline.Address{context: Inline.context, state: Inline.state, address: F.Term.addr, done: F.Term.addr -> Inline.state -> Inline.walk_result_state}
  Inline.Terms{context: Inline.context, state: Inline.state, terms: List<&2, F.Term.t>, done: List<&2, F.Term.t> -> Inline.state -> Inline.walk_result_state}
  Inline.Leg{context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, leg: F.Term.leg, done: F.Term.leg -> Inline.state -> Inline.walk_result_state}
  Inline.LegContext{scope: Maybe<&2, F.Pair2<Inline.context, F.Term.t>>, context: Inline.context, state: Inline.state, leg: F.Term.leg, done: F.Term.leg -> Inline.state -> Inline.walk_result_state}
  Inline.Legs{context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, legs: List<&2, F.Term.leg>, done: List<&2, F.Term.leg> -> Inline.state -> Inline.walk_result_state}
  Inline.Motive{shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, context: Inline.context, state: Inline.state, motive: Maybe<&2, F.Term.motive>, done: Maybe<&2, F.Term.motive> -> Inline.state -> Inline.walk_result_state}
  Inline.Branch{scope: Maybe<&2, Inline.context>, context: Inline.context, state: Inline.state, leg: F.Term.leg, done: F.Term.leg -> Inline.state -> Inline.walk_result_state}
  Inline.Branches{shape: F.Shape.t<F.Term.t>, scrut: F.Term.t, context: Inline.context, state: Inline.state, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, done: List<&2, F.Pair2<F.Term.addr, F.Term.leg>> -> Inline.state -> Inline.walk_result_state}
  Inline.Let{needed: Bool, context: Inline.context, state: Inline.state, name: String, ty: F.Term.t, value: F.Term.t, body: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state}

def Inline.install_postulate_state(~ops: Inline.Semantics, fresh: F.Pair2<String, Inline.state>, scope: Inline.context, +ty: F.Term.t, done: F.Term.t -> Inline.state -> Inline.walk_result_state) -> Inline.walk_result_state:
  F.Pair2{+name, Inline.State{globals, index}} = fresh
  +sealed_globals = F.Global.add(name, F.Global.Axiom{F.Global.AxiomEntry{ty}}, globals)
  Inline.bind_state(F.Term.t, F.Pair2<F.Term.t, Inline.state>, Inline.instantiate_state(~ops, scope, sealed_globals, name, ty), replacement =>
    done(replacement, Inline.State{sealed_globals, index}))

# Only this driver ties the mutually recursive erasure walks together. It has
# no traversal fuel; typed continuations preserve every intermediate result.
@unsafe
def Inline.run_state(~ops: Inline.Semantics, task: Inline.Task) -> Inline.walk_result_state:
  match task:
    case Inline.Walk{+context, state, +expected, +term, done}:
      Inline.Context{checker, domains} = context
      Inline.bind_state(Maybe<&2, F.Term.t>, F.Pair2<F.Term.t, Inline.state>, Inline.proof_type_state(~ops, checker, expected, term), proof =>
        Inline.run_state(~ops, Inline.Classified{proof, context, state, expected, term, done}))
    case Inline.Classified{proof, +context, state, expected, +term, done}:
      match proof:
        case None{}: Inline.run_state(~ops, Inline.Node{context, state, expected, term, done})
        case Some{+ty}:
          +scope = Inline.scope_closed(Bool.and(Inline.closed(0n, ty), Inline.closed(0n, term)), context)
          Inline.run_state(~ops, Inline.SealType{scope, state, ty, closed_ty => next =>
            Inline.install_postulate_state(~ops, Inline.fresh(next), scope, closed_ty, done)})
    case Inline.SealType{+context, state, ty, done}:
      Inline.Context{checker, domains} = context
      Inline.run_state(~ops, Inline.Domains{Inline.reverse(Inline.local, domains, Nil{}), Inline.root(context), state, Nil{}, ty, done})
    case Inline.Domains{locals, +context, state, walked, ty, done}:
      match locals:
        case Nil{}:
          Inline.run_state(~ops, Inline.Walk{context, state, None{}, ty, body => next => done(Inline.abstract(walked, body), next)})
        case local <> rest:
          match local:
            case Inline.Param{+name, +domain}:
              Inline.run_state(~ops, Inline.Walk{context, state, None{}, domain, rewritten => next =>
                Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.bind_domain_state(context, name, F.Quantity.Zero{}, domain), scope =>
                  Inline.run_state(~ops, Inline.Domains{rest, scope, next, Inline.Param{name, rewritten} <> walked, ty, done}))})
            case Inline.Local{name, +domain, value}:
              Inline.Context{checker, domains} = context
              Inline.bind_state(Bool, F.Pair2<F.Term.t, Inline.state>, Inline.proposition_state(~ops, checker, domain), proof =>
                Inline.run_state(~ops, Inline.DomainLocal{proof, name, domain, value, rest, context, state, walked, ty, done}))
    case Inline.DomainLocal{proof, +name, +domain, +value, locals, +context, state, walked, ty, done}:
      match proof:
        case True{}:
          Inline.run_state(~ops, Inline.Walk{context, state, None{}, domain, rewritten => next =>
            Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.define_let_state(context, name, domain, value), scope =>
              Inline.run_state(~ops, Inline.Domains{locals, scope, next, Inline.Local{name, rewritten, value} <> walked, ty, done}))})
        case False{}:
          Inline.run_state(~ops, Inline.Walk{context, state, Some{domain}, value, sealed => next =>
            Inline.run_state(~ops, Inline.Walk{context, next, None{}, domain, rewritten => after =>
              Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.define_let_state(context, name, domain, value), scope =>
                Inline.run_state(~ops, Inline.Domains{locals, scope, after, Inline.Local{name, rewritten, sealed} <> walked, ty, done}))})})
    case Inline.Shape{+context, state, +shape, done}:
      Inline.run_state(~ops, Inline.Payload{F.Shape.payload(F.Term.t, shape), Nil{}, context, state, replacements => next =>
        (do R.Erase.State<F.Pair2<F.Term.t, Inline.state>>:
          payload: List<&2, F.Term.t> <- Inline.replace_payload_state(F.Shape.payload(F.Term.t, shape), replacements)
          rewritten: F.Shape.t<F.Term.t> <- R.Erase.State.lift(F.Shape.t<F.Term.t>, F.Shape.with_payload(F.Term.t, F.Term.t, shape, payload))
          done(rewritten, next))})
    case Inline.Payload{terms, +replacements, context, state, done}:
      match terms:
        case Nil{}: done(replacements, state)
        case +original <> rest:
          Inline.run_state(~ops, Inline.PayloadItem{Inline.replacement(replacements, original), original, rest, replacements, context, state, done})
    case Inline.PayloadItem{found, +original, terms, replacements, +context, state, done}:
      match found:
        case Some{rewritten}: Inline.run_state(~ops, Inline.Payload{terms, replacements, context, state, done})
        case None{}:
          Inline.run_state(~ops, Inline.Walk{context, state, None{}, original, rewritten => next =>
            Inline.run_state(~ops, Inline.Payload{terms, F.Pair2{original, rewritten} <> replacements, context, next, done})})
    case Inline.Address{context, state, address, done}:
      match address:
        case F.Term.APt{q, term}:
          Inline.run_state(~ops, Inline.Walk{context, state, None{}, term, rewritten => next => done(F.Term.APt{q, rewritten}, next)})
        case other: done(other, state)
    case Inline.Terms{+context, state, terms, done}:
      match terms:
        case Nil{}: done(Nil{}, state)
        case h <> t:
          Inline.run_state(~ops, Inline.Walk{context, state, None{}, h, rewritten => next =>
            Inline.run_state(~ops, Inline.Terms{context, next, t, rest => after => done(rewritten <> rest, after)})})
    case Inline.Leg{+context, state, expected, +leg, done}:
      Inline.bind_state(Maybe<&2, F.Pair2<Inline.context, F.Term.t>>, F.Pair2<F.Term.t, Inline.state>, Inline.lambda_context_state(expected, leg, context), scope =>
        Inline.run_state(~ops, Inline.LegContext{scope, context, state, leg, done}))
    case Inline.LegContext{scope, context, state, leg, done}:
      match scope:
        case Some{F.Pair2{next_context, codomain}}:
          F.Term.Leg{binders, body} = leg
          Inline.run_state(~ops, Inline.Walk{next_context, state, Some{codomain}, body, rewritten => next => done(F.Term.Leg{binders, rewritten}, next)})
        case None{}:
          F.Term.Leg{+binders, body} = leg
          Inline.run_state(~ops, Inline.Walk{Inline.leg_scope(binders, context), state, None{}, body, rewritten => next => done(F.Term.Leg{binders, rewritten}, next)})
    case Inline.Legs{+context, state, +expected, legs, done}:
      match legs:
        case Nil{}: done(Nil{}, state)
        case h <> t:
          Inline.run_state(~ops, Inline.Leg{context, state, expected, h, rewritten => next =>
            Inline.run_state(~ops, Inline.Legs{context, next, expected, t, rest => after => done(rewritten <> rest, after)})})
    case Inline.Motive{shape, scrut, +context, state, motive, done}:
      match motive:
        case None{}: done(None{}, state)
        case Some{F.Term.Motive{+ind, +idx, +self, body}}:
          Inline.bind_state(Maybe<&2, Inline.context>, F.Pair2<F.Term.t, Inline.state>, Inline.motive_context_state(shape, scrut, ind, idx, self, context), scope =>
            Inline.run_state(~ops, Inline.Walk{Inline.motive_scope(scope, context), state, None{}, body, rewritten => next => done(Some{F.Term.Motive{ind, idx, self, rewritten}}, next)}))
    case Inline.Branch{scope, context, state, leg, done}:
      match scope:
        case None{}: Inline.run_state(~ops, Inline.Leg{context, state, None{}, leg, done})
        case Some{next_context}:
          F.Term.Leg{binders, body} = leg
          Inline.run_state(~ops, Inline.Walk{next_context, state, None{}, body, rewritten => next => done(F.Term.Leg{binders, rewritten}, next)})
    case Inline.Branches{+shape, +scrut, +context, state, branches, done}:
      match branches:
        case Nil{}: done(Nil{}, state)
        case F.Pair2{+address, +leg} <> rest:
          F.Term.Leg{binders, body} = leg
          Inline.bind_state(Maybe<&2, Inline.context>, F.Pair2<F.Term.t, Inline.state>, Inline.branch_scrutinee_state(shape, scrut, address, binders, context), scope =>
            Inline.run_state(~ops, Inline.Address{context, state, address, new_address => next =>
              Inline.run_state(~ops, Inline.Branch{scope, context, next, leg, new_leg => after_leg =>
                Inline.run_state(~ops, Inline.Branches{shape, scrut, context, after_leg, rest, more => after => done(F.Pair2{new_address, new_leg} <> more, after)})})}))
    case Inline.Let{needed, +context, state, +name, +ty, +value, body, done}:
      match needed:
        case True{}:
          Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.define_let_state(context, name, ty, value), scope =>
            Inline.run_state(~ops, Inline.Walk{context, state, None{}, ty, new_ty => next =>
              Inline.run_state(~ops, Inline.Walk{scope, next, None{}, body, new_body => after => done(F.Term.Let{name, new_ty, value, new_body}, after)})}))
        case False{}:
          Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.bind_let_state(~ops, context, name, ty, value), scope =>
            Inline.run_state(~ops, Inline.Walk{context, state, Some{ty}, value, new_value => after_value =>
              Inline.run_state(~ops, Inline.Walk{context, after_value, None{}, ty, new_ty => next =>
                Inline.run_state(~ops, Inline.Walk{scope, next, None{}, body, new_body => after => done(F.Term.Let{name, new_ty, new_value, new_body}, after)})})}))
    case Inline.Node{+context, state, expected, term, done}:
      match term:
        case F.Term.Lan{+shape, diagram}:
          Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.diagram_context_state(context, shape), scope =>
            Inline.run_state(~ops, Inline.Shape{context, state, shape, s => next =>
              Inline.run_state(~ops, Inline.Walk{scope, next, None{}, diagram, body => after => done(F.Term.Lan{s, body}, after)})}))
        case F.Term.Ran{+shape, diagram}:
          Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, Inline.diagram_context_state(context, shape), scope =>
            Inline.run_state(~ops, Inline.Shape{context, state, shape, s => next =>
              Inline.run_state(~ops, Inline.Walk{scope, next, None{}, diagram, body => after => done(F.Term.Ran{s, body}, after)})}))
        case F.Term.In{shape, address, args}:
          Inline.run_state(~ops, Inline.Shape{context, state, shape, s => next =>
            Inline.run_state(~ops, Inline.Address{context, next, address, a => after_address =>
              Inline.run_state(~ops, Inline.Terms{context, after_address, args, xs => after => done(F.Term.In{s, a, xs}, after)})})})
        case F.Term.Out{shape, address, head}:
          Inline.run_state(~ops, Inline.Shape{context, state, shape, s => next =>
            Inline.run_state(~ops, Inline.Address{context, next, address, a => after_address =>
              Inline.run_state(~ops, Inline.Walk{context, after_address, None{}, head, h => after => done(F.Term.Out{s, a, h}, after)})})})
        case F.Term.Sec{shape, legs}:
          Inline.run_state(~ops, Inline.Shape{context, state, shape, s => next =>
            Inline.run_state(~ops, Inline.Legs{context, next, expected, legs, ls => after => done(F.Term.Sec{s, ls}, after)})})
        case F.Term.Let{name, +ty, value, +body}:
          Inline.bind_state(Bool, F.Pair2<F.Term.t, Inline.state>, Inline.needed_proof_state(~ops, context, ty, body), needed =>
            Inline.run_state(~ops, Inline.Let{needed, context, state, name, ty, value, body, done}))
        case F.Term.Ann{value, +ty}:
          Inline.run_state(~ops, Inline.Walk{context, state, Some{ty}, value, new_value => next =>
            Inline.run_state(~ops, Inline.Walk{context, next, None{}, ty, new_ty => after => done(F.Term.Ann{new_value, new_ty}, after)})})
        case F.Term.Elim{F.Term.Elimination{+shape, +scrut, quantity, motive, branches}}:
          Inline.run_state(~ops, Inline.Shape{context, state, shape, s => next =>
            Inline.run_state(~ops, Inline.Walk{context, next, None{}, scrut, sc => after_scrut =>
              Inline.run_state(~ops, Inline.Motive{shape, scrut, context, after_scrut, motive, mo => after_motive =>
                Inline.run_state(~ops, Inline.Branches{shape, scrut, context, after_motive, branches, bs => after => done(F.Term.Elim{F.Term.Elimination{s, sc, quantity, mo, bs}}, after)})})})})
        case other: done(other, state)

def Inline.term_state(~ops: Inline.Semantics, context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, term: F.Term.t) -> Inline.walk_result_state:
  Inline.run_state(~ops, Inline.Walk{context, state, expected, term, rewritten => next => R.Erase.Return{F.Pair2{rewritten, next}}})

def Inline.entry_axiom_result_state(result: F.Pair2<F.Term.t, Inline.state>) -> R.Erase.State<F.Pair2<F.Global.entry, Inline.state>>:
  F.Pair2{rewritten, next} = result
  R.Erase.Return{F.Pair2{F.Global.Axiom{F.Global.AxiomEntry{rewritten}}, next}}

def Inline.entry_def_type_state(result: F.Pair2<F.Term.t, Inline.state>, body: F.Term.t, reducible: Bool, recursive: Maybe<&2, Nat>, partial: Bool) -> R.Erase.State<F.Pair2<F.Global.entry, Inline.state>>:
  F.Pair2{ty, state} = result
  R.Erase.Return{F.Pair2{F.Global.Def{F.Global.DefEntry{ty, body, reducible, recursive, partial}}, state}}

def Inline.entry_def_body_state(~ops: Inline.Semantics, result: F.Pair2<F.Term.t, Inline.state>, context: Inline.context, ty: F.Term.t, reducible: Bool, recursive: Maybe<&2, Nat>, partial: Bool) -> R.Erase.State<F.Pair2<F.Global.entry, Inline.state>>:
  F.Pair2{body, state} = result
  Inline.bind_state(F.Pair2<F.Term.t, Inline.state>, F.Pair2<F.Global.entry, Inline.state>, Inline.term_state(~ops, context, state, None{}, ty), result =>
    Inline.entry_def_type_state(result, body, reducible, recursive, partial))

def Inline.entry_state(~ops: Inline.Semantics, entry: F.Global.entry, +context: Inline.context, state: Inline.state) -> R.Erase.State<F.Pair2<F.Global.entry, Inline.state>>:
  match entry:
    case F.Global.Prim{primitive}: R.Erase.Return{F.Pair2{F.Global.Prim{primitive}, state}}
    case F.Global.Axiom{F.Global.AxiomEntry{ty}}:
      Inline.bind_state(F.Pair2<F.Term.t, Inline.state>, F.Pair2<F.Global.entry, Inline.state>, Inline.term_state(~ops, context, state, None{}, ty), Inline.entry_axiom_result_state)
    case F.Global.Def{F.Global.DefEntry{+ty, body, reducible, recursive, partial}}:
      Inline.bind_state(F.Pair2<F.Term.t, Inline.state>, F.Pair2<F.Global.entry, Inline.state>, Inline.term_state(~ops, context, state, Some{ty}, body), result =>
        Inline.entry_def_body_state(~ops, result, context, ty, reducible, recursive, partial))

def Inline.install_entry(result: F.Pair2<F.Global.entry, Inline.state>, name: String) -> Inline.state:
  F.Pair2{rewritten, Inline.State{globals, next}} = result
  Inline.State{F.Global.add(name, rewritten, globals), next}

def Inline.rewrite_environment_state(~ops: Inline.Semantics, rows: List<&2, F.Pair2<String, F.Global.entry>>, +context: Inline.context, state: Inline.state) -> R.Erase.State<Inline.state>:
  match rows:
    case Nil{}: R.Erase.Return{state}
    case F.Pair2{name, original} <> rest:
      Inline.bind_state(F.Pair2<F.Global.entry, Inline.state>, Inline.state, Inline.entry_state(~ops, original, context, state), result =>
        Inline.rewrite_environment_state(~ops, rest, context, Inline.install_entry(result, name)))

def Inline.member_name(names: List<&2, String>, +name: String) -> Bool:
  match names:
    case Nil{}: False{}
    case h <> t: Bool.or(String.eq(h, name), Inline.member_name(t, name))

def Inline.original_equal(found: Maybe<&2, F.Global.entry>, original: F.Global.entry) -> Bool:
  match found:
    case None{}: False{}
    case Some{entry}: Inline.entry_equal(entry, original)

def Inline.validate_equal_state(equal: Bool, name: String, seen: List<&2, String>) -> R.Erase.State<List<&2, String>>:
  match equal:
    case True{}: R.Erase.Return{name <> seen}
    case False{}: R.Erase.Raise{F.Error.Mismatch{"erasure row differs from its environment: " ++ name}}

def Inline.validate_seen_state(seen_before: Bool, globals: F.Global.t, +name: String, original: F.Global.entry, seen: List<&2, String>) -> R.Erase.State<List<&2, String>>:
  match seen_before:
    case True{}: R.Erase.Return{seen}
    case False{}: Inline.validate_equal_state(Inline.original_equal(F.Global.find(name, globals), original), name, seen)

def Inline.validate_rows_state(rows: List<&2, F.Pair2<String, F.Global.entry>>, +globals: F.Global.t) -> R.Erase.State<List<&2, String>>:
  match rows:
    case Nil{}: R.Erase.Return{Nil{}}
    case F.Pair2{+name, original} <> rest:
      Inline.bind_state(List<&2, String>, List<&2, String>, Inline.validate_rows_state(rest, globals), found =>
        (+seen : List<&2, String> = found
         Inline.validate_seen_state(Inline.member_name(seen, name), globals, name, original, seen)))

def Inline.require_entry_state(found: Maybe<&2, F.Global.entry>, name: String) -> R.Erase.State<F.Pair2<String, F.Global.entry>>:
  match found:
    case None{}: R.Erase.Raise{F.Error.Unbound{name}}
    case Some{entry}: R.Erase.Return{F.Pair2{name, entry}}

def Inline.resolve_rows_state(rows: List<&2, F.Pair2<String, F.Global.entry>>, +globals: F.Global.t) -> R.Erase.State<List<&2, F.Pair2<String, F.Global.entry>>>:
  match rows:
    case Nil{}: R.Erase.Return{Nil{}}
    case F.Pair2{+name, original} <> rest:
      do R.Erase.State<List<&2, F.Pair2<String, F.Global.entry>>>:
        here: F.Pair2<String, F.Global.entry> <- Inline.require_entry_state(F.Global.find(name, globals), name)
        more: List<&2, F.Pair2<String, F.Global.entry>> <- Inline.resolve_rows_state(rest, globals)
        R.Erase.Return{here <> more}

def Inline.prepare_state_state(~ops: Inline.Semantics, state: Inline.state, globals: F.Global.t, +rows: List<&2, F.Pair2<String, F.Global.entry>>) -> R.Erase.State<F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  Inline.State{+rewritten, index} = state
  Inline.bind_state(List<&2, String>, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Inline.validate_rows_state(rows, globals), seen =>
    Inline.bind_state(List<&2, F.Pair2<String, F.Global.entry>>, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Inline.resolve_rows_state(rows, rewritten), output =>
      R.Erase.Return{F.Pair2{rewritten, output}}))

def Inline.prepare_state(~ops: Inline.Semantics, checker: C.Check.ctx, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> R.Erase.State<F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  Inline.bind_state(Inline.state, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Inline.rewrite_environment_state(~ops, F.Global.entries(globals), Inline.Context{checker, Nil{}}, Inline.State{globals, 0n}), state =>
    Inline.prepare_state_state(~ops, state, globals, rows))

def Inline.walk_result() -> Data:
  Result<&2,&2,F.Error.t,F.Pair2<F.Term.t,Inline.state>>

def Inline.context_budget(context:Inline.context) -> C.Budget.t:
  Inline.Context{checker,domains} = context
  C.Check.budget(checker)

def Inline.bind(-A: Data, -B: Data, r: Result<&2, &2, F.Error.t, A>, next: A -> Result<&2, &2, F.Error.t, B>) -> Result<&2, &2, F.Error.t, B>:
  Result.bind(&2, &2, F.Error.t, A, B, r, next)


def Inline.prepare(~ops: Inline.Semantics, +checker: C.Check.ctx, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  R.Erase.State.finish(F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Inline.prepare_state(~ops, checker, globals, rows), C.Check.budget(checker))

def Inline.prepare_stateful(~ops: Inline.Semantics, +checker: C.Check.ctx, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> F.Pair2<Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>,C.Budget.t>:
  R.Erase.State.execute(F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Inline.prepare_state(~ops, checker, globals, rows), C.Check.budget(checker))

def Inline.term(~ops: Inline.Semantics, +context: Inline.context, state: Inline.state, expected: Maybe<&2, F.Term.t>, term: F.Term.t) -> Inline.walk_result:
  R.Erase.State.finish(F.Pair2<F.Term.t, Inline.state>, Inline.term_state(~ops, context, state, expected, term), Inline.context_budget(context))
