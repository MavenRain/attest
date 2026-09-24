import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_eval.bend as E
import syntax.bend as S
import elab_requests.bend as R
import elab_common.bend as H

type Elab.bound is Data:
  Elab.Bound{q: F.Quantity.t, name: String, ty: F.Term.t, ctx: C.Check.ctx}

def Elab.binder(+binder: S.Syntax.binder, +ctx: C.Check.ctx) -> R.Elab.Program<Elab.bound>:
  S.Syntax.Binder{+q, +name, ty} = binder
  do R.Elab.Program<Elab.bound>:
    +term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
    value : F.Value.t <- H.Elab.eval(ctx, term)
    return Elab.Bound{q, name, term, C.Check.bind(name, q, value, ctx)}

def Elab.cod_value(+value: F.Value.t, +ctx: C.Check.ctx) -> R.Elab.Program<Maybe<&2, F.Value.t>>:
  match value:
    case F.Value.VRan{F.Shape.SPi{q, name, dom}, closure, universe}:
      do R.Elab.Program<Maybe<&2, F.Value.t>>:
        cod : F.Value.t <- H.Elab.open(ctx, closure, [F.Value.var(C.Check.size(ctx))])
        return Some{cod}
    case _: R.Elab.Done{None{}}

def Elab.cod_of(+expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx) -> R.Elab.Program<Maybe<&2, F.Value.t>>:
  match expected:
    case None{}: R.Elab.Done{None{}}
    case Some{value}:
      do R.Elab.Program<Maybe<&2, F.Value.t>>:
        weak : F.Value.t <- H.Elab.whnf(ctx, value)
        Elab.cod_value(weak, ctx)

type Elab.fun_job is Data:
  Elab.FunStart{binders: List<&2, S.Syntax.binder>, body: S.Syntax.t, ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>}
  Elab.FunBound{bound: Elab.bound, rest: List<&2, S.Syntax.binder>, body: S.Syntax.t, ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>}

@unsafe
def Elab.function(+job: Elab.fun_job) -> R.Elab.Program<F.Term.t>:
  match job:
    case Elab.FunStart{binders, body, +ctx, expected}:
      match binders:
        case Nil{}: R.Elab.term(ctx, expected, body)
        case Con{head, tail}:
          do R.Elab.Program<F.Term.t>:
            bound : Elab.bound <- Elab.binder(head, ctx)
            Elab.function(Elab.FunBound{bound, tail, body, ctx, expected})
    case Elab.FunBound{bound, rest, body, ctx, expected}:
      match bound:
        case Elab.Bound{+q, +name, ty, inner_ctx}:
          do R.Elab.Program<F.Term.t>:
            inner : Maybe<&2, F.Value.t> <- Elab.cod_of(expected, ctx)
            term : F.Term.t <- Elab.function(Elab.FunStart{rest, body, inner_ctx, inner})
            return F.Term.Sec{F.Shape.SPi{q, name, ty}, [F.Term.Leg{[F.Pair2{q, name}], term}]}

def Elab.former(+left: Bool,+shape: F.Shape.t<F.Term.t>,+cod: F.Term.t) -> F.Term.t:
  match left:
    case True{}: F.Term.Lan{shape, cod}
    case False{}: F.Term.Ran{shape, cod}

def Elab.group_bound(+bound: Elab.bound,+cod: S.Syntax.t,+left: Bool) -> R.Elab.Program<F.Term.t>:
  Elab.Bound{q, name, ty, ctx} = bound
  do R.Elab.Program<F.Term.t>:
    body : F.Term.t <- R.Elab.term(ctx, None{}, cod)
    return Elab.former(left, F.Shape.SPi{q, name, ty}, body)

def Elab.group(+ctx: C.Check.ctx,+binder: S.Syntax.binder,+cod: S.Syntax.t,+left: Bool) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    bound : Elab.bound <- Elab.binder(binder, ctx)
    Elab.group_bound(bound, cod, left)

def Elab.pair_point(+point: F.Triple3<F.Quantity.t, String, F.Value.t>,+closure: F.Value.closure,+a: S.Syntax.t,+b: S.Syntax.t, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Triple3{+q, name, +dom} = point
  do R.Elab.Program<F.Term.t>:
    +point : F.Term.t <- R.Elab.term(ctx, Some{dom}, a)
    point_value : F.Value.t <- H.Elab.eval(ctx, point)
    cod : F.Value.t <- H.Elab.open(ctx, closure, [point_value])
    fibre : F.Term.t <- R.Elab.term(ctx, Some{cod}, b)
    dom_term : F.Term.t <- H.Elab.quote(ctx, dom)
    return F.Term.In{F.Shape.SPi{q, name, dom_term}, F.Term.APt{q, point}, [fibre]}

def Elab.pair_former(+former: F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>,+a: S.Syntax.t,+b: S.Syntax.t, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Triple3{shape, closure, universe} = former
  do R.Elab.Program<F.Term.t>:
    point : F.Triple3<F.Quantity.t, String, F.Value.t> <- H.Elab.point(shape, "a pair needs a point former")
    Elab.pair_point(point, closure, a, b, ctx)

def Elab.pair(+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>,+a: S.Syntax.t,+b: S.Syntax.t) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    ty : F.Value.t <- R.Elab.option(F.Value.t, expected, H.Elab.no_expect("a pair"))
    weak : F.Value.t <- H.Elab.whnf(ctx, ty)
    former : F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>> <- H.Elab.left(weak, "a pair needs a left former as its expected type")
    Elab.pair_former(former, a, b, ctx)

@unsafe
def Elab.expected_legs(+count: Nat, +index: Nat, +legs: List<&2, F.Value.vleg>, +ctx: C.Check.ctx) -> R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
  match count:
    case 0n: R.Elab.Done{Nil{}}
    case 1n+remaining:
      do R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
        value : F.Value.t <- H.Elab.coll_leg_ty(ctx, legs, index)
        rest : List<&2, Maybe<&2, F.Value.t>> <- Elab.expected_legs(remaining, (index + 1n : Nat), legs, ctx)
        return Con{Some{value}, rest}

# Source arities use arbitrary precision until the corresponding list exists.
@unsafe
def Elab.unknowns_loop(zero: Bool, count: F.Bignum.t, acc: List<&2, Maybe<&2, F.Value.t>>) -> List<&2, Maybe<&2, F.Value.t>>:
  match zero:
    case True{}: acc
    case False{}:
      +next : F.Bignum.t = F.Bignum.sub(count, F.Bignum.from_nat(1n))
      Elab.unknowns_loop(F.Bignum.equal(next, F.Bignum.from_nat(0n)), next, Con{None{}, acc})

# The accumulator keeps every recursive call in tail position, so a wide collection uses constant stack depth.
def Elab.unknowns_nat(+size: Nat, +acc: List<&2, Maybe<&2, F.Value.t>>) -> List<&2, Maybe<&2, F.Value.t>>:
  match size:
    case 0n: acc
    case 1n+remaining: Elab.unknowns_nat(remaining, Con{None{}, acc})

def Elab.unknowns_size(size: Maybe<&2, Nat>, count: F.Bignum.t) -> List<&2, Maybe<&2, F.Value.t>>:
  match size:
    case Some{size}: Elab.unknowns_nat(size, Nil{})
    case None{}: Elab.unknowns_loop(False{}, count, Nil{})

def Elab.unknowns(+count: F.Bignum.t) -> List<&2, Maybe<&2, F.Value.t>>:
  Elab.unknowns_size(F.Bignum.to_nat(count), count)

def Elab.expect_width(+equal: Bool,+ctx: C.Check.ctx,+closure: F.Value.closure,+count: F.Bignum.t, width: Nat) -> R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
  match equal:
    case False{}: R.Elab.Done{Elab.unknowns(count)}
    case True{}:
      do R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
        legs : List<&2, F.Value.vleg> <- H.Elab.coll_legs_of(ctx, closure)
        Elab.expected_legs(width, 0n, legs, ctx)

def Elab.expect_value(+value: F.Value.t,+left: Bool, +ctx: C.Check.ctx, +count: F.Bignum.t) -> R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
  match value left:
    case F.Value.VLan{F.Shape.SColl{+width}, closure, universe} True{}: Elab.expect_width(F.Bignum.equal(F.Bignum.from_nat(width), count), ctx, closure, count, width)
    case F.Value.VRan{F.Shape.SColl{+width}, closure, universe} False{}: Elab.expect_width(F.Bignum.equal(F.Bignum.from_nat(width), count), ctx, closure, count, width)
    case _ _: R.Elab.Done{Elab.unknowns(count)}

def Elab.leg_expectations(+expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx,+count: F.Bignum.t,+left: Bool) -> R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
  match expected:
    case None{}: R.Elab.Done{Elab.unknowns(count)}
    case Some{ty}:
      do R.Elab.Program<List<&2, Maybe<&2, F.Value.t>>>:
        weak : F.Value.t <- H.Elab.whnf(ctx, ty)
        Elab.expect_value(weak, left, ctx, count)

@unsafe
def Elab.items(+items: List<&2, S.Syntax.t>,+expected: List<&2, Maybe<&2, F.Value.t>>, +ctx: C.Check.ctx) -> R.Elab.Program<List<&2, F.Term.t>>:
  match items expected:
    case Nil{} Nil{}: R.Elab.Done{Nil{}}
    case Con{item, items} Con{ty, tys}:
      do R.Elab.Program<List<&2, F.Term.t>>:
        term : F.Term.t <- R.Elab.term(ctx, ty, item)
        rest : List<&2, F.Term.t> <- Elab.items(items, tys, ctx)
        return Con{term, rest}
    case _ _: R.Elab.Fail{F.Error.Mismatch{"the item count and the leg count differ"}}

def Elab.tuple(+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>, +items: List<&2, S.Syntax.t>) -> R.Elab.Program<F.Term.t>:
  +count : Nat = List.length(&2, S.Syntax.t, items)
  do R.Elab.Program<F.Term.t>:
    types : List<&2, Maybe<&2, F.Value.t>> <- Elab.leg_expectations(expected, ctx, F.Bignum.from_nat(count), False{})
    terms : List<&2, F.Term.t> <- Elab.items(items, types, ctx)
    return F.Term.Sec{F.Shape.SColl{count}, H.Elab.term_legs(terms)}

def Elab.join_option(+option: Maybe<&2, Maybe<&2, F.Value.t>>) -> Maybe<&2, F.Value.t>:
  match option:
    case None{}: None{}
    case Some{inner}: inner

def Elab.payload_expected(index: Maybe<&2, Nat>, types: List<&2, Maybe<&2, F.Value.t>>) -> Maybe<&2, F.Value.t>:
  match index:
    case None{}: None{}
    case Some{index}: Elab.join_option(List.get(&2, Maybe<&2, F.Value.t>, types, index))

# The width list of an injection can be as long as the source arity.
# The count is carried in acc, so every recursive call is a tail call.
def Elab.length_onto(types: List<&2, Maybe<&2, F.Value.t>>, +acc: Nat) -> Nat:
  match types:
    case Nil{}: acc
    case Con{head, tail}: Elab.length_onto(tail, (acc + 1n : Nat))

def Elab.injection(+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>,+key: F.Bignum.t,+arity: F.Bignum.t,+term: S.Syntax.t) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    +types : List<&2, Maybe<&2, F.Value.t>> <- Elab.leg_expectations(expected, ctx, arity, True{})
    payload : F.Term.t <- R.Elab.term(ctx, Elab.payload_expected(F.Bignum.to_nat(key), types), term)
    k : Nat <- H.Elab.count(key)
    n : Nat = Elab.length_onto(types, 0n)
    return F.Term.In{F.Shape.SColl{n}, F.Term.ALeg{k}, [payload]}

def Elab.projection_which(+first: Bool,+second: Bool) -> R.Elab.Program<Nat>:
  match first second:
    case True{} _: R.Elab.Done{0n}
    case _ True{}: R.Elab.Done{1n}
    case _ _: R.Elab.Fail{F.Error.Wrong_leg{"a pair carries the projections .1 and .2 only"}}

def Elab.projection_body(+which: Nat, +ctx: C.Check.ctx,+shape: F.Shape.t<F.Value.t>,+q: F.Quantity.t,+dom: F.Value.t,+closure: F.Value.closure) -> R.Elab.Program<F.Value.t>:
  match which:
    case 0n: R.Elab.Done{dom}
    case 1n+remaining:
      do R.Elab.Program<F.Value.t>:
        point : F.Value.t <- R.Elab.lift(F.Value.t, E.Rules.elim_value(C.Check.global(ctx), shape, q, None{}, H.Elab.proj_branch(q, 0n), C.Check.environment(ctx), F.Value.var(C.Check.size(ctx))))
        H.Elab.open(ctx, closure, [point])

def Elab.projection_point(+point: F.Triple3<F.Quantity.t, String, F.Value.t>, +shape: F.Shape.t<F.Value.t>,+closure: F.Value.closure,+key: F.Bignum.t,+scrut: F.Term.t, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Triple3{+q, name, +dom} = point
  do R.Elab.Program<F.Term.t>:
    +which : Nat <- Elab.projection_which(F.Bignum.equal(key, F.Bignum.one), F.Bignum.equal(key, F.Bignum.from_nat(2n)))
    body_value : F.Value.t <- Elab.projection_body(which, ctx, shape, q, dom, closure)
    motive_body : F.Term.t <- R.Elab.lift(F.Term.t, E.Eval.quote(C.Check.global(ctx), (C.Check.size(ctx) + 1n : Nat), body_value))
    dom_term : F.Term.t <- H.Elab.quote(ctx, dom)
    return F.Term.Elim{F.Term.Elimination{F.Shape.SPi{q, name, dom_term}, scrut, F.Quantity.One{}, Some{F.Term.Motive{None{}, Nil{}, "self", motive_body}}, H.Elab.proj_branch(q, which)}}

def Elab.projection_type(+value: F.Value.t,+scrut: F.Term.t,+key: F.Bignum.t, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  match value:
    case F.Value.VLan{+shape, closure, universe}:
      do R.Elab.Program<F.Term.t>:
        point : F.Triple3<F.Quantity.t, String, F.Value.t> <- H.Elab.point(shape, "a pair projection needs a point former")
        Elab.projection_point(point, shape, closure, key, scrut, ctx)
    case F.Value.VRan{shape, closure, universe}:
      do R.Elab.Program<F.Term.t>:
        width : Nat <- H.Elab.collection(shape, "a leg projection needs a collection former")
        index : Nat <- H.Elab.count(key)
        return F.Term.Out{F.Shape.SColl{width}, F.Term.ALeg{index}, scrut}
    case _: R.Elab.Fail{F.Error.Mismatch{"a projection reads a pair or a tuple, and this scrutinee is neither"}}

def Elab.projection(+ctx: C.Check.ctx,+term: S.Syntax.t,+key: F.Bignum.t) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    +scrut : F.Term.t <- R.Elab.term(ctx, None{}, term)
    ty : F.Value.t <- H.Elab.type_of(ctx, scrut)
    Elab.projection_type(ty, scrut, key, ctx)
