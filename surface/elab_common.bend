import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_eval.bend as E
import ../lib/kernel_primitives.bend as K
import syntax.bend as S
import elab_requests.bend as R

type Elab.mu_ref is Data:
  Elab.RFam{family: F.Positivity.family}
  Elab.RCtor{family: F.Positivity.family, ctor: F.Positivity.ctor}

def Elab.no_expect(what: String) -> F.Error.t:
  F.Error.Cannot_infer{what ++ " needs an expected type"}

def Elab.index_next(value: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match value:
    case None{}: None{}
    case Some{index}: Some{(index + 1n : Nat)}

def Elab.index_choose(equal: Bool, next: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match equal:
    case True{}: Some{0n}
    case False{}: Elab.index_next(next)

def Elab.index_of(names: List<&2, String>, +name: String) -> Maybe<&2, Nat>:
  match names:
    case Nil{}: None{}
    case Con{head, tail}: Elab.index_choose(String.eq(name, head), Elab.index_of(tail, name))

def Elab.local_ref(name: String, index: Maybe<&2, Nat>) -> F.Term.t:
  match index:
    case None{}: F.Term.Global{name}
    case Some{value}: F.Term.Var{value}

def Elab.eval(+ctx: C.Check.ctx, term: F.Term.t) -> R.Elab.Program<F.Value.t>:
  R.Elab.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), C.Check.environment(ctx), term))

def Elab.whnf(ctx: C.Check.ctx, value: F.Value.t) -> R.Elab.Program<F.Value.t>:
  R.Elab.lift(F.Value.t, E.Eval.whnf(C.Check.global(ctx), value))

def Elab.quote(+ctx: C.Check.ctx, value: F.Value.t) -> R.Elab.Program<F.Term.t>:
  R.Elab.lift(F.Term.t, E.Eval.quote(C.Check.global(ctx), C.Check.size(ctx), value))

def Elab.open(ctx: C.Check.ctx, closure: F.Value.closure, args: List<&2, F.Value.t>) -> R.Elab.Program<F.Value.t>:
  R.Elab.lift(F.Value.t, E.Eval.open_closure(C.Check.global(ctx), closure, args))

def Elab.type_of(+ctx: C.Check.ctx, term: F.Term.t) -> R.Elab.Program<F.Value.t>:
  do R.Elab.Program<F.Value.t>:
    value : F.Value.t <- R.Elab.infer(ctx, term)
    Elab.whnf(ctx, value)

def Elab.universe(level: F.Bignum.t, checked: Maybe<&2, F.Level.t>) -> R.Elab.Program<F.Term.t>:
  match checked:
    case None{}: R.Elab.Fail{F.Error.Universe{"the universe level " ++ F.Bignum.to_string(level) ++ " is not a level"}}
    case Some{level}: R.Elab.Done{F.Term.Univ{level}}

def Elab.univ_of_bignum(+level: F.Bignum.t) -> R.Elab.Program<F.Term.t>:
  Elab.universe(level, F.Level.of_bignum(level))

def Elab.count(value: F.Bignum.t) -> R.Elab.Program<Nat>:
  R.Elab.option(Nat, F.Bignum.to_nat(value), F.Error.Wrong_leg{"the leg address is outside the collection"})

def Elab.arity_is(what: String, +want: Nat, +got: Nat) -> R.Elab.Program<Unit>:
  R.Elab.guard(Nat.is_eq(want, got), F.Error.Mismatch{what ++ " takes " ++ Nat.show(want) ++ " arguments and the term gives " ++ Nat.show(got)})

def Elab.spine(term: S.Syntax.t, acc: List<&2, S.Syntax.t>) -> F.Pair2<S.Syntax.t, List<&2, S.Syntax.t>>:
  match term:
    case S.Syntax.SApp{fun, arg}: Elab.spine(fun, Con{arg, acc})
    case _: F.Pair2{term, acc}

def Elab.ctor_choose(equal: Bool, ctor: F.Positivity.ctor, next: Maybe<&2, F.Positivity.ctor>) -> Maybe<&2, F.Positivity.ctor>:
  match equal:
    case True{}: Some{ctor}
    case False{}: next

def Elab.ctor_of(ctors: List<&2, F.Positivity.ctor>, +name: String) -> Maybe<&2, F.Positivity.ctor>:
  match ctors:
    case Nil{}: None{}
    case Con{+ctor, tail}:
      F.Positivity.Ctor{cname, args, res, arity, recursive} = ctor
      Elab.ctor_choose(String.eq(cname, name), ctor, Elab.ctor_of(tail, name))

def Elab.family_ctor(family: F.Positivity.family, name: String) -> Maybe<&2, F.Positivity.ctor>:
  F.Positivity.Family{fname, params, indices, level, status, ctors, positive} = family
  Elab.ctor_of(ctors, name)

def Elab.find_ctor_found(family: F.Positivity.family, ctor: Maybe<&2, F.Positivity.ctor>, next: Maybe<&2, Elab.mu_ref>) -> Maybe<&2, Elab.mu_ref>:
  match ctor:
    case None{}: next
    case Some{ctor}: Some{Elab.RCtor{family, ctor}}

def Elab.find_ctor(families: List<&2, F.Pair2<String, F.Positivity.family>>, +name: String) -> Maybe<&2, Elab.mu_ref>:
  match families:
    case Nil{}: None{}
    case Con{head, tail}:
      F.Pair2{key, +family} = head
      Elab.find_ctor_found(family, Elab.family_ctor(family, name), Elab.find_ctor(tail, name))

def Elab.mu_ref_family(family: Maybe<&2, F.Positivity.family>, globals: F.Global.t, name: String) -> Maybe<&2, Elab.mu_ref>:
  match family:
    case Some{family}: Some{Elab.RFam{family}}
    case None{}:
      Elab.find_ctor(F.Global.families(globals), name)

def Elab.mu_ref_local(index: Maybe<&2, Nat>, +globals: F.Global.t, +name: String) -> Maybe<&2, Elab.mu_ref>:
  match index:
    case Some{index}: None{}
    case None{}: Elab.mu_ref_family(F.Global.find_family(name, globals), globals, name)

def Elab.mu_ref_of(+ctx: C.Check.ctx, +name: String) -> Maybe<&2, Elab.mu_ref>:
  Elab.mu_ref_local(Elab.index_of(C.Check.names_of(ctx), name), C.Check.global(ctx), name)

def Elab.point(shape: F.Shape.t<F.Value.t>, message: String) -> R.Elab.Program<F.Triple3<F.Quantity.t, String, F.Value.t>>:
  match shape:
    case F.Shape.SPi{q, name, dom}: R.Elab.Done{F.Triple3{q, name, dom}}
    case _: R.Elab.Fail{F.Error.Mismatch{message}}

def Elab.left(value: F.Value.t, message: String) -> R.Elab.Program<F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>>:
  R.Elab.option(F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>, F.Value.as_lan(value), F.Error.Mismatch{message})

def Elab.right(value: F.Value.t, message: String) -> R.Elab.Program<F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>>:
  R.Elab.option(F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>, F.Value.as_ran(value), F.Error.Mismatch{message})

def Elab.collection(shape: F.Shape.t<F.Value.t>, message: String) -> R.Elab.Program<Nat>:
  match shape:
    case F.Shape.SColl{width}: R.Elab.Done{width}
    case _: R.Elab.Fail{F.Error.Mismatch{message}}

def Elab.coll_legs_value(value: F.Value.t) -> R.Elab.Program<List<&2, F.Value.vleg>>:
  match value:
    case F.Value.VSec{shape, legs}: R.Elab.Done{legs}
    case _: R.Elab.Fail{F.Error.Mismatch{"the diagram is not a section of the declared width"}}

def Elab.coll_legs_of(ctx: C.Check.ctx, closure: F.Value.closure) -> R.Elab.Program<List<&2, F.Value.vleg>>:
  do R.Elab.Program<List<&2, F.Value.vleg>>:
    value : F.Value.t <- Elab.open(ctx, closure, Nil{})
    Elab.coll_legs_value(value)

def Elab.open_leg(ctx: C.Check.ctx, leg: F.Value.vleg) -> R.Elab.Program<F.Value.t>:
  F.Value.Leg{binders, closure} = leg
  Elab.open(ctx, closure, Nil{})

def Elab.coll_leg_ty(+ctx: C.Check.ctx, legs: List<&2, F.Value.vleg>, index: Nat) -> R.Elab.Program<F.Value.t>:
  do R.Elab.Program<F.Value.t>:
    leg : F.Value.vleg <- R.Elab.option(F.Value.vleg, List.get(&2, F.Value.vleg, legs, index), F.Error.Wrong_leg{"the leg address is outside the collection"})
    Elab.open_leg(ctx, leg)

def Elab.leg_option(ctx: C.Check.ctx, leg: F.Value.vleg) -> R.Elab.Program<Maybe<&2, F.Value.t>>:
  do R.Elab.Program<Maybe<&2, F.Value.t>>:
    value : F.Value.t <- Elab.open_leg(ctx, leg)
    return Some{value}

def Elab.param_env(+ctx: C.Check.ctx, closure: F.Value.closure) -> R.Elab.Program<List<&2, F.Value.t>>:
  do R.Elab.Program<List<&2, F.Value.t>>:
    legs : List<&2, F.Value.vleg> <- Elab.coll_legs_of(ctx, closure)
    values : List<&2, F.Value.t> <- R.Elab.map(F.Value.vleg, F.Value.t, Elab.open_leg, legs, ctx)
    return List.reverse(&2, F.Value.t, values)

def Elab.none_terms(ctx: C.Check.ctx, term: S.Syntax.t) -> R.Elab.Program<F.Term.t>:
  R.Elab.term(ctx, None{}, term)

def Elab.term_legs(terms: List<&2, F.Term.t>) -> List<&2, F.Term.leg>:
  match terms:
    case Nil{}: Nil{}
    case Con{head, tail}: Con{K.Rules.leg_of(head), Elab.term_legs(tail)}

def Elab.proj_branch(q: F.Quantity.t, which: Nat) -> List<&2, F.Pair2<F.Term.addr, F.Term.leg>>:
  [F.Pair2{F.Term.ALeg{0n}, F.Term.Leg{[F.Pair2{q, "x"}, F.Pair2{F.Quantity.Many{}, "y"}], F.Term.Var{Nat.sub(1n, which)}}}]
