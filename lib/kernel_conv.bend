import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_primitives.bend as P
import ./kernel_context.bend as C
import ./kernel_program.bend as S
import ./kernel_check.bend as K
import ./kernel_rules.bend as R
import ./kernel_mu.bend as M
import ./kernel_eval.bend as E

def Conv.placeholder() -> F.Value.t:
  F.Value.VUniv{F.Level.zero}

def Conv.then(equal: Bool, next: Unit -> S.Kernel.Program<Bool>) -> S.Kernel.Program<Bool>:
  match equal:
    case False{}: S.Kernel.Done{False{}}
    case True{}: next(Unit{})

def Conv.grow(count: Nat, ctx: C.Check.ctx) -> C.Check.ctx:
  match count:
    case Zero{}: ctx
    case Succ{pred}: Conv.grow(pred, C.Check.bind("_", F.Quantity.Many{}, Conv.placeholder, ctx))

def Conv.values(xs: List<&2, F.Value.t>, ys: List<&2, F.Value.t>, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  match xs ys:
    case Nil{} Nil{}: S.Kernel.Done{True{}}
    case Con{x, rest} Con{y, more}:
      do S.Kernel.Program<Bool>:
        equal: Bool <- S.Conv.conv_type(ctx, x, y)
        Conv.then(equal, unit => Conv.values(rest, more, ctx))
    case Nil{} Con{y, more}: S.Kernel.Done{False{}}
    case Con{x, rest} Nil{}: S.Kernel.Done{False{}}

def Conv.shape(a: F.Shape.t<F.Value.t>, b: F.Shape.t<F.Value.t>, ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  F.Shape.same_fold(F.Value.t, C.Check.ctx, S.Kernel.Program<Bool>, a, b, ctx,
    q1 => n1 => d1 => q2 => n2 => d2 => state =>
      Conv.then(F.Quantity.equal(q1, q2), unit => S.Conv.conv_type(state, d1, d2)),
    n1 => n2 => state => S.Kernel.Done{Nat.is_eq(n1, n2)},
    a => b => c => d => state => S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}},
    n1 => ix1 => n2 => ix2 => state => Conv.then(String.eq(n1, n2), unit => Conv.values(ix1, ix2, state)),
    n1 => ix1 => n2 => ix2 => state => S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}},
    state => S.Kernel.Done{False{}})

def Conv.admitted(shape: F.Shape.t<F.Value.t>) -> S.Kernel.Program<Unit>:
  F.Shape.fold(F.Value.t, Unit, S.Kernel.Program<Unit>, shape, Unit{},
    q => name => domain => unit => (
      S.Kernel.Done{Unit{}}
    ),
    width => unit => (
      S.Kernel.Done{Unit{}}
    ),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      S.Kernel.Done{Unit{}}
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Conv.annotation(shape: F.Shape.t<F.Value.t>, a: Maybe<&2, F.Level.t>, b: Maybe<&2, F.Level.t>) -> Bool:
  F.Shape.fold(F.Value.t, Unit, Bool, shape, Unit{},
    q => name => domain => unit => (
      True{}
    ),
    width => unit => (
      Bool.or(Nat.is_ne(width, 0n), F.Level.equal(Maybe.default(&2, F.Level.t, a, F.Level.zero), Maybe.default(&2, F.Level.t, b, F.Level.zero)))
    ),
    x => y => unit => (
      True{}
    ),
    name => indices => unit => (
      True{}
    ),
    name => indices => unit => (
      True{}
    ))

def Conv.diagram(+shape: F.Shape.t<F.Value.t>, +a: F.Value.closure, +b: F.Value.closure, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  F.Shape.fold(F.Value.t, Unit, S.Kernel.Program<Bool>, shape, Unit{},
    q => name => domain => unit => (
      +fresh = F.Value.var(C.Check.size(ctx))
      do S.Kernel.Program<Bool>:
        x: F.Value.t <- K.Check.open(ctx, a, [fresh])
        y: F.Value.t <- K.Check.open(ctx, b, [fresh])
        S.Conv.conv_type(C.Check.bind(name, q, domain, ctx), x, y)
    ),
    width => unit => (
      do S.Kernel.Program<Bool>:
        x: F.Value.t <- K.Check.open(ctx, a, Nil{})
        y: F.Value.t <- K.Check.open(ctx, b, Nil{})
        S.Conv.conv_type(ctx, x, y)
    ),
    x => y => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      do S.Kernel.Program<Bool>:
        x: F.Value.t <- K.Check.open(ctx, a, Nil{})
        y: F.Value.t <- K.Check.open(ctx, b, Nil{})
        S.Conv.conv_type(ctx, x, y)
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Conv.formers(+s1: F.Shape.t<F.Value.t>, d1: F.Value.closure, u1: Maybe<&2, F.Level.t>,
  s2: F.Shape.t<F.Value.t>, d2: F.Value.closure, u2: Maybe<&2, F.Level.t>, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  do S.Kernel.Program<Bool>:
    unit: Unit <- Conv.admitted(s1)
    same: Bool <- Conv.shape(s1, s2, ctx)
    Conv.then(Bool.and(same, Conv.annotation(s1, u1, u2)), unit => Conv.diagram(s1, d1, d2, ctx))

def Conv.addr_type(ty: Maybe<&2, F.Value.t>, ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t) -> S.Kernel.Program<Bool>:
  match ty:
    case None{}: S.Conv.conv_type(ctx, a, b)
    case Some{value}: S.Conv.conv(ctx, value, a, b)
def Conv.addr(a: F.Value.vaddr, b: F.Value.vaddr, ctx: C.Check.ctx, ty: Maybe<&2, F.Value.t>) -> S.Kernel.Program<Bool>:
  match a b:
    case F.Value.VAPt{q1, a} F.Value.VAPt{q2, b}: Conv.addr_type(ty, ctx, a, b)
    case F.Value.VALeg{i} F.Value.VALeg{j}: S.Kernel.Done{Nat.is_eq(i, j)}
    case F.Value.VACtor{a} F.Value.VACtor{b}: S.Kernel.Done{String.eq(a, b)}
    case _ _: S.Kernel.Done{False{}}

def Conv.closures(+ctx: C.Check.ctx, +arity: Nat, a: F.Value.closure, other: Nat, b: F.Value.closure) -> S.Kernel.Program<Bool>:
  Conv.then(Nat.is_eq(arity, other), unit => (
    do S.Kernel.Program<Bool>:
      x: F.Value.t <- K.Check.open(ctx, a, E.Eval.variables(arity, C.Check.size(ctx)))
      y: F.Value.t <- K.Check.open(ctx, b, E.Eval.variables(arity, C.Check.size(ctx)))
      S.Conv.conv_type(Conv.grow(arity, ctx), x, y)
  ))

def Conv.leg(a: F.Value.vleg, b: F.Value.vleg, ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  F.Value.Leg{binders1, closure1} = a
  F.Value.Leg{binders2, closure2} = b
  Conv.closures(ctx, List.length(&2, F.Pair2<F.Quantity.t, String>, binders1), closure1,
    List.length(&2, F.Pair2<F.Quantity.t, String>, binders2), closure2)
def Conv.legs(xs: List<&2, F.Value.vleg>, ys: List<&2, F.Value.vleg>, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  match xs ys:
    case Nil{} Nil{}: S.Kernel.Done{True{}}
    case Con{x, rest} Con{y, more}:
      do S.Kernel.Program<Bool>:
        same: Bool <- Conv.leg(x, y, ctx)
        Conv.then(same, unit => Conv.legs(rest, more, ctx))
    case _ _: S.Kernel.Done{False{}}

def Conv.branch_addr(a: F.Term.addr, b: F.Term.addr, +ctx: C.Check.ctx, env1: List<&2, F.Value.t>, env2: List<&2, F.Value.t>)
  -> S.Kernel.Program<Bool>:
  match a b:
    case F.Term.APt{q1, t1} F.Term.APt{q2, t2}:
      do S.Kernel.Program<Bool>:
        x: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env1, t1))
        y: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env2, t2))
        S.Conv.conv_type(ctx, x, y)
    case F.Term.ALeg{i} F.Term.ALeg{j}: S.Kernel.Done{Nat.is_eq(i, j)}
    case F.Term.ACtor{x} F.Term.ACtor{y}: S.Kernel.Done{String.eq(x, y)}
    case _ _: S.Kernel.Done{False{}}

def Conv.branch(a: F.Pair2<F.Term.addr, F.Term.leg>, b: F.Pair2<F.Term.addr, F.Term.leg>, +ctx: C.Check.ctx,
  +env1: List<&2, F.Value.t>, +env2: List<&2, F.Value.t>) -> S.Kernel.Program<Bool>:
  F.Pair2{addr1, leg1} = a
  F.Term.Leg{binders1, body1} = leg1
  F.Pair2{addr2, leg2} = b
  F.Term.Leg{binders2, body2} = leg2
  do S.Kernel.Program<Bool>:
    same: Bool <- Conv.branch_addr(addr1, addr2, ctx, env1, env2)
    Conv.then(same, unit => Conv.closures(ctx, List.length(&2, F.Pair2<F.Quantity.t, String>, binders1), F.Value.Closure{env1, body1},
      List.length(&2, F.Pair2<F.Quantity.t, String>, binders2), F.Value.Closure{env2, body2}))

def Conv.branches(xs: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, ys: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>,
  +ctx: C.Check.ctx, +env1: List<&2, F.Value.t>, +env2: List<&2, F.Value.t>) -> S.Kernel.Program<Bool>:
  match xs ys:
    case Nil{} Nil{}: S.Kernel.Done{True{}}
    case Con{x, rest} Con{y, more}:
      do S.Kernel.Program<Bool>:
        same: Bool <- Conv.branch(x, y, ctx, env1, env2)
        Conv.then(same, unit => Conv.branches(rest, more, ctx, env1, env2))
    case _ _: S.Kernel.Done{False{}}

def Conv.motives(a: Maybe<&2, F.Term.motive>, b: Maybe<&2, F.Term.motive>, +ctx: C.Check.ctx,
  env1: List<&2, F.Value.t>, env2: List<&2, F.Value.t>) -> S.Kernel.Program<Bool>:
  match a b:
    case None{} None{}: S.Kernel.Done{True{}}
    case Some{F.Term.Motive{ind1, indices1, self1, body1}} Some{F.Term.Motive{ind2, indices2, self2, body2}}:
      Conv.closures(ctx, (List.length(&2, String, indices1) + 1n : Nat), F.Value.Closure{env1, body1},
        (List.length(&2, String, indices2) + 1n : Nat), F.Value.Closure{env2, body2})
    case _ _: S.Kernel.Done{False{}}

def Conv.stuck(a: F.Value.stuck_elim, b: F.Value.stuck_elim, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  F.Value.StuckElim{s1, q1, m1, br1, +env1} = a
  F.Value.StuckElim{s2, q2, m2, br2, +env2} = b
  do S.Kernel.Program<Bool>:
    same: Bool <- Conv.shape(s1, s2, ctx)
    motive: Bool <- Conv.motives(m1, m2, ctx, env1, env2)
    Conv.then(Bool.and(same, Bool.and(F.Quantity.equal(q1, q2), motive)), unit => Conv.branches(br1, br2, ctx, env1, env2))

def Conv.spine_info() -> Data:
  F.Pair2<Maybe<&2, F.Value.t>, F.Value.t>
def Conv.spine_arg(step: Maybe<&2, Conv.spine_info>) -> Maybe<&2, F.Value.t>:
  match step:
    case None{}: None{}
    case Some{pair}: U.Kernel.fst(Maybe<&2, F.Value.t>, F.Value.t, pair)
def Conv.spine_next(step: Maybe<&2, Conv.spine_info>) -> F.Value.t:
  match step:
    case None{}: Conv.placeholder
    case Some{pair}: U.Kernel.snd(Maybe<&2, F.Value.t>, F.Value.t, pair)

def Conv.spine_leg(leg: Maybe<&2, F.Value.vleg>, ctx: C.Check.ctx) -> S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
  match leg:
    case None{}: S.Kernel.Done{None{}}
    case Some{value}:
      do S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
        ty: F.Value.t <- K.Check.open(ctx, R.Rules.value_leg_closure(value), Nil{})
        return Some{F.Pair2{None{}, ty}}

def Conv.spine_point_addr(addr: F.Value.vaddr, domain: F.Value.t, diagram: F.Value.closure, ctx: C.Check.ctx)
  -> S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
  match addr:
    case F.Value.VAPt{aq, arg}:
      do S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
        codomain: F.Value.t <- K.Check.open(ctx, diagram, [arg])
        return Some{F.Pair2{Some{domain}, codomain}}
    case _: S.Kernel.Done{None{}}

def Conv.spine_collection_addr(addr: F.Value.vaddr, diagram: F.Value.closure, +ctx: C.Check.ctx)
  -> S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
  match addr:
    case F.Value.VALeg{k}:
      do S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
        legs: List<&2, F.Value.vleg> <- R.Rules.coll_legs_of(ctx, diagram)
        Conv.spine_leg(List.get(&2, F.Value.vleg, legs, k), ctx)
    case _: S.Kernel.Done{None{}}

def Conv.spine_shape(+shape: F.Shape.t<F.Value.t>, +addr: F.Value.vaddr, +diagram: F.Value.closure, +ctx: C.Check.ctx)
  -> S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
  F.Shape.fold(F.Value.t, Unit, S.Kernel.Program<Maybe<&2, Conv.spine_info>>, shape, Unit{},
    q => name => domain => unit => Conv.spine_point_addr(addr, domain, diagram, ctx),
    width => unit => Conv.spine_collection_addr(addr, diagram, ctx),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      S.Kernel.Done{None{}}
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Conv.spine_former(ty: F.Value.t, shape: F.Shape.t<F.Value.t>, addr: F.Value.vaddr, ctx: C.Check.ctx)
  -> S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
  match ty:
    case F.Value.VRan{s, diagram, level}: Conv.spine_shape(shape, addr, diagram, ctx)
    case _: S.Kernel.Done{None{}}
def Conv.spine_step(+ctx: C.Check.ctx, ty: F.Value.t, shape: F.Shape.t<F.Value.t>, addr: F.Value.vaddr)
  -> S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
  do S.Kernel.Program<Maybe<&2, Conv.spine_info>>:
    weak: F.Value.t <- K.Check.whnf(ctx, ty)
    Conv.spine_former(weak, shape, addr, ctx)

def Conv.spines(xs: List<&2, F.Value.spine>, ys: List<&2, F.Value.spine>, +ctx: C.Check.ctx, ty: F.Value.t) -> S.Kernel.Program<Bool>:
  match xs ys:
    case Nil{} Nil{}: S.Kernel.Done{True{}}
    case Con{F.Value.SOut{+s1, +a1}, rest} Con{F.Value.SOut{s2, a2}, more}:
      do S.Kernel.Program<Bool>:
        same: Bool <- Conv.shape(s1, s2, ctx)
        +step: Maybe<&2, Conv.spine_info> <- Conv.spine_step(ctx, ty, s1, a1)
        address: Bool <- Conv.addr(a1, a2, ctx, Conv.spine_arg(step))
        Conv.then(Bool.and(same, address), unit => Conv.spines(rest, more, ctx, Conv.spine_next(step)))
    case Con{F.Value.SElim{a}, rest} Con{F.Value.SElim{b}, more}:
      do S.Kernel.Program<Bool>:
        same: Bool <- Conv.stuck(a, b, ctx)
        Conv.then(same, unit => Conv.spines(rest, more, ctx, Conv.placeholder))
    case _ _: S.Kernel.Done{False{}}

def Conv.structural_values(a: F.Value.t, b: F.Value.t, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  match a b:
    case F.Value.VUniv{l1} F.Value.VUniv{l2}: S.Kernel.Done{F.Level.equal(l1, l2)}
    case F.Value.VLit{l1} F.Value.VLit{l2}: S.Kernel.Done{F.Literal.equal(l1, l2)}
    case F.Value.VLan{s1, d1, u1} F.Value.VLan{s2, d2, u2}: Conv.formers(s1, d1, u1, s2, d2, u2, ctx)
    case F.Value.VRan{s1, d1, u1} F.Value.VRan{s2, d2, u2}: Conv.formers(s1, d1, u1, s2, d2, u2, ctx)
    case F.Value.VIn{s1, a1, args1} F.Value.VIn{s2, a2, args2}:
      do S.Kernel.Program<Bool>:
        same: Bool <- Conv.shape(s1, s2, ctx)
        address: Bool <- Conv.addr(a1, a2, ctx, None{})
        Conv.then(Bool.and(same, address), unit => Conv.values(args1, args2, ctx))
    case F.Value.VSec{s1, legs1} F.Value.VSec{s2, legs2}:
      do S.Kernel.Program<Bool>:
        same: Bool <- Conv.shape(s1, s2, ctx)
        Conv.then(same, unit => Conv.legs(legs1, legs2, ctx))
    case F.Value.VNeutral{+h1, sp1} F.Value.VNeutral{h2, sp2}:
      Conv.then(F.Value.head_equal(h1, h2), unit => (
        do S.Kernel.Program<Bool>:
          ty: F.Value.t <- K.Check.head_ty(ctx, h1)
          Conv.spines(List.reverse(&2, F.Value.spine, sp1), List.reverse(&2, F.Value.spine, sp2), ctx, ty)
      ))
    case _ _: S.Kernel.Done{False{}}

def Conv.structural_node(+ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t) -> S.Kernel.Program<Bool>:
  do S.Kernel.Program<Bool>:
    x: F.Value.t <- K.Check.whnf(ctx, a)
    y: F.Value.t <- K.Check.whnf(ctx, b)
    Conv.structural_values(x, y, ctx)

def Conv.projection_index(first: Bool) -> Nat:
  match first:
    case True{}: 1n
    case False{}: 0n
def Conv.proj_branch(q: F.Quantity.t, first: Bool) -> List<&2, F.Pair2<F.Term.addr, F.Term.leg>>:
  [F.Pair2{F.Term.ALeg{0n}, F.Term.Leg{[F.Pair2{q, "x"}, F.Pair2{F.Quantity.Many{}, "y"}], F.Term.Var{Conv.projection_index(first)}}}]

def Conv.proj_value(first: Bool, +ctx: C.Check.ctx, shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure,
  +q: F.Quantity.t, domain: F.Value.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  match first:
    case True{}: Done{domain}
    case False{}:
      do Result<&2, &2, F.Error.t, F.Value.t>:
        point: F.Value.t <- E.Rules.elim_value(C.Check.global(ctx), shape, q, None{}, Conv.proj_branch(q, True{}), C.Check.environment(ctx), F.Value.var(C.Check.size(ctx)))
        E.Eval.open_closure(C.Check.global(ctx), diagram, [point])

def Conv.proj_motive(+ctx: C.Check.ctx, shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure,
  +q: F.Quantity.t, name: String, +domain: F.Value.t, first: Bool) -> S.Kernel.Program<Maybe<&2, F.Term.motive>>:
  do S.Kernel.Program<Maybe<&2, F.Term.motive>>:
    body: F.Value.t <- S.Kernel.lift(F.Value.t, Conv.proj_value(first, ctx, shape, diagram, q, domain))
    term: F.Term.t <- S.Kernel.lift(F.Term.t, E.Eval.quote(C.Check.global(ctx), C.Check.size(C.Check.bind(name, q, domain, ctx)), body))
    return Some{F.Term.Motive{None{}, Nil{}, "self", term}}

def Conv.pi_eta_right_point(point: Maybe<&2, F.Triple3<F.Quantity.t, String, F.Value.t>>, +ctx: C.Check.ctx, +shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, a: F.Value.t, b: F.Value.t)
  -> S.Kernel.Program<Bool>:
  match point:
    case Some{F.Triple3{+q, name, domain}}:
      +fresh = F.Value.var(C.Check.size(ctx))
      do S.Kernel.Program<Bool>:
        codomain: F.Value.t <- K.Check.open(ctx, diagram, [fresh])
        x: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.out_value(C.Check.global(ctx), shape, F.Value.VAPt{q, fresh}, a))
        y: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.out_value(C.Check.global(ctx), shape, F.Value.VAPt{q, fresh}, b))
        S.Conv.conv(C.Check.bind(name, q, domain, ctx), codomain, x, y)
    case None{}: S.Kernel.Fail{F.Error.Mismatch{P.Rules.wrong_pack}}

def Conv.pi_eta_right(+ctx: C.Check.ctx, +shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, a: F.Value.t, b: F.Value.t)
  -> S.Kernel.Program<Bool>:
  Conv.pi_eta_right_point(F.Shape.point(F.Value.t, shape), ctx, shape, diagram, a, b)

def Conv.pi_eta_left_point(point: Maybe<&2, F.Triple3<F.Quantity.t, String, F.Value.t>>, +ctx: C.Check.ctx, +shape: F.Shape.t<F.Value.t>, +diagram: F.Value.closure, +a: F.Value.t, +b: F.Value.t)
  -> S.Kernel.Program<Bool>:
  match point:
    case Some{F.Triple3{+q, +name, +domain}}:
      do S.Kernel.Program<Bool>:
        +first_motive: Maybe<&2, F.Term.motive> <- Conv.proj_motive(ctx, shape, diagram, q, name, domain, True{})
        +x1: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.elim_value(C.Check.global(ctx), shape, F.Quantity.One{}, first_motive,
          Conv.proj_branch(q, True{}), C.Check.environment(ctx), a))
        y1: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.elim_value(C.Check.global(ctx), shape, F.Quantity.One{}, first_motive,
          Conv.proj_branch(q, True{}), C.Check.environment(ctx), b))
        first: Bool <- S.Conv.conv(ctx, domain, x1, y1)
        Conv.then(first, unit => (
          do S.Kernel.Program<Bool>:
            codomain: F.Value.t <- K.Check.open(ctx, diagram, [x1])
            +second_motive: Maybe<&2, F.Term.motive> <- Conv.proj_motive(ctx, shape, diagram, q, name, domain, False{})
            x2: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.elim_value(C.Check.global(ctx), shape, F.Quantity.One{}, second_motive,
              Conv.proj_branch(q, False{}), C.Check.environment(ctx), a))
            y2: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.elim_value(C.Check.global(ctx), shape, F.Quantity.One{}, second_motive,
              Conv.proj_branch(q, False{}), C.Check.environment(ctx), b))
            S.Conv.conv(ctx, codomain, x2, y2)
        ))
    case None{}: S.Kernel.Fail{F.Error.Mismatch{P.Rules.wrong_pack}}

def Conv.pi_eta_left(+ctx: C.Check.ctx, +shape: F.Shape.t<F.Value.t>, +diagram: F.Value.closure, +a: F.Value.t, +b: F.Value.t)
  -> S.Kernel.Program<Bool>:
  Conv.pi_eta_left_point(F.Shape.point(F.Value.t, shape), ctx, shape, diagram, a, b)

def Conv.coll_eta(remaining: Nat, +k: Nat, +ctx: C.Check.ctx, +shape: F.Shape.t<F.Value.t>, +legs: List<&2, F.Value.vleg>, +a: F.Value.t, +b: F.Value.t)
  -> S.Kernel.Program<Bool>:
  match remaining:
    case Zero{}: S.Kernel.Done{True{}}
    case Succ{pred}:
      do S.Kernel.Program<Bool>:
        ty: F.Value.t <- R.Rules.coll_leg_ty(ctx, legs, k)
        x: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.out_value(C.Check.global(ctx), shape, F.Value.VALeg{k}, a))
        y: F.Value.t <- S.Kernel.lift(F.Value.t, E.Rules.out_value(C.Check.global(ctx), shape, F.Value.VALeg{k}, b))
        same: Bool <- S.Conv.conv(ctx, ty, x, y)
        Conv.then(same, unit => Conv.coll_eta(pred, (k + 1n : Nat), ctx, shape, legs, a, b))

def Conv.subsingleton(sub: Bool, ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t) -> S.Kernel.Program<Bool>:
  match sub:
    case True{}: S.Kernel.Done{True{}}
    case False{}: S.Conv.structural(ctx, a, b)

def Conv.by_type(+ty: F.Value.t, +a: F.Value.t, +b: F.Value.t, +ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  match ty:
    case F.Value.VLan{+shape, +diagram, level}:
      F.Shape.fold(F.Value.t, Unit, S.Kernel.Program<Bool>, shape, Unit{},
        q => name => domain => unit => (
          Conv.pi_eta_left(ctx, shape, diagram, a, b)
        ),
        width => unit => (
          S.Conv.structural(ctx, a, b)
        ),
        x => y => unit => (
          S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
        ),
        name => indices => unit => (
          Conv.subsingleton(M.Mu.subsingleton(ctx, name), ctx, a, b)
        ),
        name => indices => unit => (
          S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
        ))
    case F.Value.VRan{+shape, +diagram, level}:
      F.Shape.fold(F.Value.t, Unit, S.Kernel.Program<Bool>, shape, Unit{},
        q => name => domain => unit => (
          Conv.pi_eta_right(ctx, shape, diagram, a, b)
        ),
        width => unit => (
          do S.Kernel.Program<Bool>:
            legs: List<&2, F.Value.vleg> <- R.Rules.coll_legs_of(ctx, diagram)
            Conv.coll_eta(width, 0n, ctx, shape, legs, a, b)
        ),
        x => y => unit => (
          S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
        ),
        name => indices => unit => (
          S.Conv.structural(ctx, a, b)
        ),
        name => indices => unit => (
          S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
        ))
    case _: S.Conv.structural(ctx, a, b)

def Conv.prop_level(level: Maybe<&2, F.Level.t>) -> Bool:
  match level:
    case None{}: False{}
    case Some{value}: F.Level.equal(value, F.Level.zero)
def Conv.prop_quote(quoted: Result<&2, &2, F.Error.t, F.Term.t>, ctx: C.Check.ctx) -> S.Kernel.Program<Bool>:
  match quoted:
    case Fail{error}: S.Kernel.Done{False{}}
    case Done{term}:
      do S.Kernel.Program<Bool>:
        level: Maybe<&2, F.Level.t> <- S.Check.try_univ(ctx, term)
        return Conv.prop_level(level)
def Conv.after_prop(prop: Bool, +ctx: C.Check.ctx, ty: F.Value.t, a: F.Value.t, b: F.Value.t) -> S.Kernel.Program<Bool>:
  match prop:
    case True{}: S.Kernel.Done{True{}}
    case False{}:
      do S.Kernel.Program<Bool>:
        weak: F.Value.t <- K.Check.whnf(ctx, ty)
        Conv.by_type(weak, a, b, ctx)
def Conv.conv_node(+ctx: C.Check.ctx, +ty: F.Value.t, a: F.Value.t, b: F.Value.t) -> S.Kernel.Program<Bool>:
  do S.Kernel.Program<Bool>:
    prop: Bool <- Conv.prop_quote(E.Eval.quote(C.Check.global(ctx), C.Check.size(ctx), ty), ctx)
    Conv.after_prop(prop, ctx, ty, a, b)
