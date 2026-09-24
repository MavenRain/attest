import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_primitives.bend as P
import ./kernel_context.bend as C
import ./kernel_program.bend as S
import ./kernel_check.bend as K
import ./kernel_eval.bend as E

type Rules.Former is Data:
  Rules.Former{whole: F.Value.t, shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, level: Maybe<&2, F.Level.t>}


def Rules.former_shape(former: Rules.Former) -> F.Shape.t<F.Value.t>:
  Rules.Former{whole, shape, diagram, level} = former
  shape


def Rules.former_diagram(former: Rules.Former) -> F.Value.closure:
  Rules.Former{whole, shape, diagram, level} = former
  diagram


def Rules.former_whole(former: Rules.Former) -> F.Value.t:
  Rules.Former{whole, shape, diagram, level} = former
  whole


def Rules.former_data(data: F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>, whole: F.Value.t) -> Rules.Former:
  F.Triple3{shape, diagram, level} = data
  Rules.Former{whole, shape, diagram, level}


def Rules.former_view(left: Bool, +value: F.Value.t, message: String) -> S.Kernel.Program<Rules.Former>:
  match left:
    case True{}:
      do S.Kernel.Program<Rules.Former>:
        data: F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>> <- S.Kernel.option(
          F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>, F.Value.as_lan(value), F.Error.Mismatch{message})
        return Rules.former_data(data, value)
    case False{}:
      do S.Kernel.Program<Rules.Former>:
        data: F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>> <- S.Kernel.option(
          F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>, F.Value.as_ran(value), F.Error.Mismatch{message})
        return Rules.former_data(data, value)


def Rules.former(ctx: C.Check.ctx, expected: F.Value.t, left: Bool, message: String) -> S.Kernel.Program<Rules.Former>:
  do S.Kernel.Program<Rules.Former>:
    value: F.Value.t <- K.Check.whnf(ctx, expected)
    Rules.former_view(left, value, message)


def Rules.binder_quantity(subject: String, source: String, name: String, +marked: F.Quantity.t, +declared: F.Quantity.t)
  -> S.Kernel.Program<Unit>:
  S.Kernel.guard(F.Quantity.equal(marked, declared), F.Error.Quantity{"the " ++ subject ++ " " ++ name ++ " is marked " ++
    F.Quantity.to_string(marked) ++ " and the " ++ source ++ " marks it " ++ F.Quantity.to_string(declared)})


def Rules.pi_level(left: Bool, domain: F.Level.t, codomain: F.Level.t) -> F.Level.t:
  match left:
    case True{}: F.Level.max(domain, codomain)
    case False{}: P.Rules.imax(domain, codomain)


def Rules.pi_levels(+ctx: C.Check.ctx, q: F.Quantity.t, name: String, +domain: F.Term.t, diagram: F.Term.t, left: Bool)
  -> S.Kernel.Program<F.Level.t>:
  do S.Kernel.Program<F.Level.t>:
    dom_level: F.Level.t <- S.Check.infer_univ(ctx, domain)
    dom: F.Value.t <- K.Check.eval(ctx, domain)
    cod_level: F.Level.t <- S.Check.infer_univ(C.Check.bind(name, q, dom, ctx), diagram)
    return Rules.pi_level(left, dom_level, cod_level)


def Rules.term_section(term: F.Term.t) -> Maybe<&2, F.Pair2<F.Shape.t<F.Term.t>, List<&2, F.Term.leg>>>:
  match term:
    case F.Term.Sec{shape, legs}: Some{F.Pair2{shape, legs}}
    case F.Term.Var{index}: None{}
    case F.Term.Univ{level}: None{}
    case F.Term.Lan{shape, diagram}: None{}
    case F.Term.Ran{shape, diagram}: None{}
    case F.Term.In{shape, addr, args}: None{}
    case F.Term.Elim{elimination}: None{}
    case F.Term.Out{shape, addr, scrutinee}: None{}
    case F.Term.Let{name, ty, definition, body}: None{}
    case F.Term.Ann{term, ty}: None{}
    case F.Term.Global{name}: None{}
    case F.Term.Lit{literal}: None{}
    case F.Term.Auto{}: None{}


def Rules.leg_body(leg: F.Term.leg) -> F.Term.t:
  F.Term.Leg{binders, body} = leg
  body


def Rules.leg_binders(leg: F.Term.leg) -> List<&2, F.Pair2<F.Quantity.t, String>>:
  F.Term.Leg{binders, body} = leg
  binders


def Rules.value_leg_closure(leg: F.Value.vleg) -> F.Value.closure:
  F.Value.Leg{binders, closure} = leg
  closure


def Rules.no_binders(legs: List<&2, F.Term.leg>) -> Bool:
  match legs:
    case Nil{}: True{}
    case Con{leg, rest}:
      Bool.and(List.is_empty(&2, F.Pair2<F.Quantity.t, String>, Rules.leg_binders(leg)), Rules.no_binders(rest))


def Rules.coll_levels(legs: List<&2, F.Term.leg>, +ctx: C.Check.ctx) -> S.Kernel.Program<F.Level.t>:
  match legs:
    case Nil{}: S.Kernel.Done{F.Level.zero}
    case Con{leg, rest}:
      do S.Kernel.Program<F.Level.t>:
        level: F.Level.t <- S.Check.infer_univ(ctx, Rules.leg_body(leg))
        more: F.Level.t <- Rules.coll_levels(rest, ctx)
        return F.Level.max(level, more)


def Rules.coll_level(width: Nat, level: F.Level.t, expected: Maybe<&2, F.Level.t>) -> F.Level.t:
  match width:
    case Zero{}: Maybe.default(&2, F.Level.t, expected, F.Level.zero)
    case Succ{pred}: level


def Rules.coll_form_section(section: F.Pair2<F.Shape.t<F.Term.t>, List<&2, F.Term.leg>>, ctx: C.Check.ctx, +width: Nat,
  expected: Maybe<&2, F.Level.t>) -> S.Kernel.Program<F.Level.t>:
  F.Pair2{shape, +legs} = section
  do S.Kernel.Program<F.Level.t>:
    dw: Nat <- S.Kernel.option(Nat, P.Rules.as_vcoll(F.Term.t, shape), F.Error.Mismatch{P.Rules.diagram_msg})
    one: Unit <- S.Kernel.guard(Bool.and(Nat.is_eq(dw, width), Nat.is_eq(List.length(&2, F.Term.leg, legs), width)), F.Error.Mismatch{P.Rules.diagram_msg})
    two: Unit <- S.Kernel.guard(Rules.no_binders(legs), F.Error.Mismatch{"a diagram leg binds nothing"})
    level: F.Level.t <- Rules.coll_levels(legs, ctx)
    return Rules.coll_level(width, level, expected)


def Rules.coll_form(ctx: C.Check.ctx, width: Nat, diagram: F.Term.t, expected: Maybe<&2, F.Level.t>) -> S.Kernel.Program<F.Level.t>:
  do S.Kernel.Program<F.Level.t>:
    section: F.Pair2<F.Shape.t<F.Term.t>, List<&2, F.Term.leg>> <- S.Kernel.option(F.Pair2<F.Shape.t<F.Term.t>, List<&2, F.Term.leg>>,
      Rules.term_section(diagram), F.Error.Mismatch{P.Rules.diagram_msg})
    Rules.coll_form_section(section, ctx, width, expected)


def Rules.coll_legs_of(+ctx: C.Check.ctx, closure: F.Value.closure) -> S.Kernel.Program<List<&2, F.Value.vleg>>:
  do S.Kernel.Program<List<&2, F.Value.vleg>>:
    value: F.Value.t <- K.Check.open(ctx, closure, Nil{})
    section: F.Pair2<F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>> <- S.Kernel.option(F.Pair2<F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>>,
      F.Value.as_sec(value), F.Error.Mismatch{P.Rules.diagram_msg})
    return U.Kernel.snd(F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>, section)


def Rules.coll_leg_ty(ctx: C.Check.ctx, legs: List<&2, F.Value.vleg>, k: Nat) -> S.Kernel.Program<F.Value.t>:
  do S.Kernel.Program<F.Value.t>:
    leg: F.Value.vleg <- S.Kernel.option(F.Value.vleg, List.get(&2, F.Value.vleg, legs, k), F.Error.Wrong_leg{P.Rules.leg_msg})
    K.Check.open(ctx, Rules.value_leg_closure(leg), Nil{})


def Rules.pi_sec_binder(binder: F.Pair2<F.Quantity.t, String>, +ctx: C.Check.ctx, +mode: F.Quantity.t,
  q: F.Quantity.t, domain: F.Value.t, diagram: F.Value.closure, body: F.Term.t) -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{+bq, +name} = binder
  do S.Kernel.Program<F.Quantity.usage>:
    unit: Unit <- Rules.binder_quantity("binder", "type", name, bq, q)
    codomain: F.Value.t <- K.Check.open(ctx, diagram, [F.Value.var(C.Check.size(ctx))])
    +inner: C.Check.ctx = C.Check.bind(name, bq, domain, ctx)
    uses: F.Quantity.usage <- S.Check.check_uses(inner, F.Quantity.runtime(mode), body, codomain)
    free: F.Quantity.usage <- K.Check.close(inner, C.Check.size(ctx), mode, uses, False{})
    return F.Quantity.scale(mode, F.Quantity.captures(free))


def Rules.pi_sec_domain(pi: F.Triple3<F.Quantity.t, String, F.Value.t>, ctx: C.Check.ctx, mode: F.Quantity.t,
  diagram: F.Value.closure, legs: List<&2, F.Term.leg>) -> S.Kernel.Program<F.Quantity.usage>:
  F.Triple3{q, name, domain} = pi
  do S.Kernel.Program<F.Quantity.usage>:
    +leg: F.Term.leg <- S.Kernel.option(F.Term.leg, U.Kernel.one(F.Term.leg, legs), F.Error.Mismatch{"a section at the point shape has one leg"})
    binder: F.Pair2<F.Quantity.t, String> <- S.Kernel.option(F.Pair2<F.Quantity.t, String>,
      U.Kernel.one(F.Pair2<F.Quantity.t, String>, Rules.leg_binders(leg)), F.Error.Mismatch{"the leg binds the point once"})
    Rules.pi_sec_binder(binder, ctx, mode, q, domain, diagram, Rules.leg_body(leg))


def Rules.pi_intro_sec(+ctx: C.Check.ctx, mode: F.Quantity.t, legs: List<&2, F.Term.leg>, expected: F.Value.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +former: Rules.Former <- Rules.former(ctx, expected, False{}, "a section needs a right former as its expected type")
    pi: F.Triple3<F.Quantity.t, String, F.Value.t> <- S.Kernel.option(F.Triple3<F.Quantity.t, String, F.Value.t>,
      P.Rules.as_vpi(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{"a section at the point shape needs a point former"})
    Rules.pi_sec_domain(pi, ctx, mode, Rules.former_diagram(former), legs)


def Rules.pi_in_point(point: F.Pair2<F.Quantity.t, F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t,
  q: F.Quantity.t, domain: F.Value.t, diagram: F.Value.closure, args: List<&2, F.Term.t>) -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{aq, +term} = point
  do S.Kernel.Program<F.Quantity.usage>:
    fibre: F.Term.t <- S.Kernel.option(F.Term.t, U.Kernel.one(F.Term.t, args), F.Error.Mismatch{"a pair carries one fibre element"})
    point_uses: F.Quantity.usage <- S.Check.check_uses(ctx, F.Quantity.mul(mode, q), term, domain)
    value: F.Value.t <- K.Check.eval(ctx, term)
    codomain: F.Value.t <- K.Check.open(ctx, diagram, [value])
    fibre_uses: F.Quantity.usage <- S.Check.check_uses(ctx, mode, fibre, codomain)
    return F.Quantity.sequence(point_uses, fibre_uses)


def Rules.pi_in_domain(pi: F.Triple3<F.Quantity.t, String, F.Value.t>, ctx: C.Check.ctx, mode: F.Quantity.t,
  diagram: F.Value.closure, addr: F.Term.addr, args: List<&2, F.Term.t>) -> S.Kernel.Program<F.Quantity.usage>:
  F.Triple3{q, name, domain} = pi
  do S.Kernel.Program<F.Quantity.usage>:
    point: F.Pair2<F.Quantity.t, F.Term.t> <- S.Kernel.option(F.Pair2<F.Quantity.t, F.Term.t>, F.Term.as_apt(addr), F.Error.Wrong_leg{"a pair takes the point address"})
    Rules.pi_in_point(point, ctx, mode, q, domain, diagram, args)


def Rules.pi_intro_in(+ctx: C.Check.ctx, mode: F.Quantity.t, addr: F.Term.addr, args: List<&2, F.Term.t>, expected: F.Value.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +former: Rules.Former <- Rules.former(ctx, expected, True{}, "a pair needs a left former as its expected type")
    pi: F.Triple3<F.Quantity.t, String, F.Value.t> <- S.Kernel.option(F.Triple3<F.Quantity.t, String, F.Value.t>,
      P.Rules.as_vpi(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{"a pair needs a point former"})
    Rules.pi_in_domain(pi, ctx, mode, Rules.former_diagram(former), addr, args)


def Rules.pi_out_domain(pi: F.Triple3<F.Quantity.t, String, F.Value.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t,
  diagram: F.Value.closure, +point: F.Term.t, head_uses: F.Quantity.usage) -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Triple3{q, name, domain} = pi
  do S.Kernel.Program<S.Kernel.Inferred>:
    point_uses: F.Quantity.usage <- S.Check.check_uses(ctx, F.Quantity.mul(mode, q), point, domain)
    value: F.Value.t <- K.Check.eval(ctx, point)
    result: F.Value.t <- K.Check.open(ctx, diagram, [value])
    return F.Pair2{result, F.Quantity.sequence(head_uses, point_uses)}


def Rules.pi_out_point(point: F.Pair2<F.Quantity.t, F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t, head: F.Term.t)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Pair2{aq, arg} = point
  do S.Kernel.Program<S.Kernel.Inferred>:
    +inferred: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, head)
    +former: Rules.Former <- Rules.former(ctx, U.Kernel.fst(F.Value.t, F.Quantity.usage, inferred), False{}, "the head of an application is not a function")
    pi: F.Triple3<F.Quantity.t, String, F.Value.t> <- S.Kernel.option(F.Triple3<F.Quantity.t, String, F.Value.t>,
      P.Rules.as_vpi(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{"the head of an application is not a function"})
    Rules.pi_out_domain(pi, ctx, mode, Rules.former_diagram(former), arg, U.Kernel.snd(F.Value.t, F.Quantity.usage, inferred))


def Rules.pi_out(ctx: C.Check.ctx, mode: F.Quantity.t, addr: F.Term.addr, head: F.Term.t) -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    point: F.Pair2<F.Quantity.t, F.Term.t> <- S.Kernel.option(F.Pair2<F.Quantity.t, F.Term.t>, F.Term.as_apt(addr), F.Error.Wrong_leg{"an application takes the point address"})
    Rules.pi_out_point(point, ctx, mode, head)


def Rules.coll_sec_legs(legs: List<&2, F.Term.leg>, diagrams: List<&2, F.Value.vleg>, +ctx: C.Check.ctx, +mode: F.Quantity.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  match legs diagrams:
    case Nil{} Nil{}: S.Kernel.Done{F.Quantity.empty}
    case Con{leg, rest} Con{diagram, more}:
      do S.Kernel.Program<F.Quantity.usage>:
        ty: F.Value.t <- K.Check.open(ctx, Rules.value_leg_closure(diagram), Nil{})
        uses: F.Quantity.usage <- S.Check.check_uses(ctx, mode, Rules.leg_body(leg), ty)
        others: F.Quantity.usage <- Rules.coll_sec_legs(rest, more, ctx, mode)
        return F.Quantity.sequence(uses, others)
    case Nil{} Con{diagram, more}: S.Kernel.Fail{F.Error.Mismatch{P.Rules.diagram_msg}}
    case Con{leg, rest} Nil{}: S.Kernel.Fail{F.Error.Mismatch{P.Rules.diagram_msg}}


def Rules.coll_intro_sec(+ctx: C.Check.ctx, mode: F.Quantity.t, +width: Nat, +legs: List<&2, F.Term.leg>, expected: F.Value.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +former: Rules.Former <- Rules.former(ctx, expected, False{}, "a tuple needs a right former as its expected type")
    dw: Nat <- S.Kernel.option(Nat, P.Rules.as_vcoll(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    unit: Unit <- S.Kernel.guard(Bool.and(Nat.is_eq(dw, width), Nat.is_eq(List.length(&2, F.Term.leg, legs), width)),
      F.Error.Mismatch{"the tuple width and the type width differ"})
    +diagrams: List<&2, F.Value.vleg> <- Rules.coll_legs_of(ctx, Rules.former_diagram(former))
    zip_ok: Unit <- S.Kernel.guard(Nat.is_eq(List.length(&2, F.Term.leg, legs), List.length(&2, F.Value.vleg, diagrams)), F.Error.Mismatch{P.Rules.diagram_msg})
    Rules.coll_sec_legs(legs, diagrams, ctx, mode)


def Rules.coll_intro_in(+ctx: C.Check.ctx, mode: F.Quantity.t, addr: F.Term.addr, args: List<&2, F.Term.t>, expected: F.Value.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +former: Rules.Former <- Rules.former(ctx, expected, True{}, "an injection needs a left former as its expected type")
    width: Nat <- S.Kernel.option(Nat, P.Rules.as_vcoll(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    +k: Nat <- S.Kernel.option(Nat, F.Term.as_aleg(addr), F.Error.Wrong_leg{"an injection takes the leg address"})
    unit: Unit <- S.Kernel.guard(Nat.is_lt(k, width), F.Error.Wrong_leg{P.Rules.leg_msg})
    diagrams: List<&2, F.Value.vleg> <- Rules.coll_legs_of(ctx, Rules.former_diagram(former))
    ty: F.Value.t <- Rules.coll_leg_ty(ctx, diagrams, k)
    payload: F.Term.t <- S.Kernel.option(F.Term.t, U.Kernel.one(F.Term.t, args), F.Error.Mismatch{"an injection carries one payload"})
    S.Check.check_uses(ctx, mode, payload, ty)


def Rules.coll_out(+ctx: C.Check.ctx, mode: F.Quantity.t, addr: F.Term.addr, head: F.Term.t) -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    +k: Nat <- S.Kernel.option(Nat, F.Term.as_aleg(addr), F.Error.Wrong_leg{"a projection takes the leg address"})
    +inferred: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, head)
    +former: Rules.Former <- Rules.former(ctx, U.Kernel.fst(F.Value.t, F.Quantity.usage, inferred), False{}, "a projection needs a right former")
    width: Nat <- S.Kernel.option(Nat, P.Rules.as_vcoll(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    unit: Unit <- S.Kernel.guard(Nat.is_lt(k, width), F.Error.Wrong_leg{P.Rules.leg_msg})
    diagrams: List<&2, F.Value.vleg> <- Rules.coll_legs_of(ctx, Rules.former_diagram(former))
    ty: F.Value.t <- Rules.coll_leg_ty(ctx, diagrams, k)
    return F.Pair2{ty, U.Kernel.snd(F.Value.t, F.Quantity.usage, inferred)}


def Rules.elim_scrutinee(elimination: F.Term.elim) -> F.Term.t:
  F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
  scrutinee


def Rules.elim_motive(elimination: F.Term.elim) -> Maybe<&2, F.Term.motive>:
  F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
  motive


def Rules.elim_branches(elimination: F.Term.elim) -> List<&2, F.Pair2<F.Term.addr, F.Term.leg>>:
  F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
  branches


def Rules.infer_scrutinee(ctx: C.Check.ctx, +mode: F.Quantity.t, elimination: F.Term.elim) -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Term.Elimination{shape, scrutinee, +q, motive, branches} = elimination
  do S.Kernel.Program<S.Kernel.Inferred>:
    unit: Unit <- S.Kernel.guard(Bool.or(F.Quantity.equal(mode, F.Quantity.Zero{}), Bool.not(F.Quantity.equal(q, F.Quantity.Zero{}))),
      F.Error.Quantity{"an erased scrutinee cannot be eliminated at runtime"})
    S.Check.infer_uses(ctx, F.Quantity.mul(mode, q), scrutinee)


def Rules.elim_result(motive: Maybe<&2, F.Term.motive>, +ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>, self: F.Value.t)
  -> S.Kernel.Program<F.Value.t>:
  match motive:
    case None{}:
      S.Kernel.option(F.Value.t, expected, F.Error.Cannot_infer{"an elimination without a motive needs an expected type"})
    case Some{mo}:
      F.Term.Motive{ind, indices, name, body} = mo
      S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), Con{self, C.Check.environment(ctx)}, body))


def Rules.check_motive(motive: Maybe<&2, F.Term.motive>, ctx: C.Check.ctx, scrutinee_ty: F.Value.t) -> S.Kernel.Program<Unit>:
  match motive:
    case None{}: S.Kernel.Done{Unit{}}
    case Some{mo}:
      F.Term.Motive{ind, indices, name, body} = mo
      do S.Kernel.Program<Unit>:
        level: F.Level.t <- S.Check.infer_univ(C.Check.bind(name, F.Quantity.Zero{}, scrutinee_ty, ctx), body)
        return Unit{}


def Rules.coll_branch_binder(binder: F.Pair2<F.Quantity.t, String>, +ctx: C.Check.ctx, +mode: F.Quantity.t,
  ty: F.Value.t, target: F.Value.t, body: F.Term.t) -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{q, name} = binder
  +inner = C.Check.bind(name, q, ty, ctx)
  do S.Kernel.Program<F.Quantity.usage>:
    uses: F.Quantity.usage <- S.Check.check_uses(inner, F.Quantity.runtime(mode), body, target)
    K.Check.close(inner, C.Check.size(ctx), mode, uses, False{})


def Rules.coll_branch(+ctx: C.Check.ctx, mode: F.Quantity.t, +elimination: F.Term.elim, shape: F.Shape.t<F.Value.t>,
  diagrams: List<&2, F.Value.vleg>, expected: Maybe<&2, F.Value.t>, +k: Nat) -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +leg: F.Term.leg <- S.Kernel.option(F.Term.leg, E.Eval.branch(Rules.elim_branches(elimination), F.Value.VALeg{k}),
      F.Error.Missing_branch{"no branch at leg " ++ Nat.show(k)})
    binder: F.Pair2<F.Quantity.t, String> <- S.Kernel.option(F.Pair2<F.Quantity.t, String>,
      U.Kernel.one(F.Pair2<F.Quantity.t, String>, Rules.leg_binders(leg)), F.Error.Missing_branch{"each branch binds its payload once"})
    ty: F.Value.t <- Rules.coll_leg_ty(ctx, diagrams, k)
    target: F.Value.t <- Rules.elim_result(Rules.elim_motive(elimination), ctx, expected,
      F.Value.VIn{shape, F.Value.VALeg{k}, [F.Value.var(C.Check.size(ctx))]})
    Rules.coll_branch_binder(binder, ctx, mode, ty, target, Rules.leg_body(leg))


def Rules.coll_branches(remaining: Nat, +k: Nat, +ctx: C.Check.ctx, +mode: F.Quantity.t, +elimination: F.Term.elim,
  +shape: F.Shape.t<F.Value.t>, +diagrams: List<&2, F.Value.vleg>, +expected: Maybe<&2, F.Value.t>) -> S.Kernel.Program<F.Quantity.usage>:
  match remaining:
    case Zero{}: S.Kernel.Done{F.Quantity.unreachable}
    case Succ{pred}:
      do S.Kernel.Program<F.Quantity.usage>:
        uses: F.Quantity.usage <- Rules.coll_branch(ctx, mode, elimination, shape, diagrams, expected, k)
        more: F.Quantity.usage <- Rules.coll_branches(pred, (k + 1n : Nat), ctx, mode, elimination, shape, diagrams, expected)
        return F.Quantity.alternative(uses, more)


def Rules.coll_elim(+ctx: C.Check.ctx, +mode: F.Quantity.t, +elimination: F.Term.elim, +expected: Maybe<&2, F.Value.t>)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    +inferred: S.Kernel.Inferred <- Rules.infer_scrutinee(ctx, mode, elimination)
    +former: Rules.Former <- Rules.former(ctx, U.Kernel.fst(F.Value.t, F.Quantity.usage, inferred), True{}, "the scrutinee is not a left former")
    +width: Nat <- S.Kernel.option(Nat, P.Rules.as_vcoll(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    one: Unit <- Rules.check_motive(Rules.elim_motive(elimination), ctx, Rules.former_whole(former))
    scrutinee: F.Value.t <- K.Check.eval(ctx, Rules.elim_scrutinee(elimination))
    result: F.Value.t <- Rules.elim_result(Rules.elim_motive(elimination), ctx, expected, scrutinee)
    +count: Nat = List.length(&2, F.Pair2<F.Term.addr, F.Term.leg>, Rules.elim_branches(elimination))
    two: Unit <- S.Kernel.guard(Nat.is_eq(count, width), F.Error.Missing_branch{"the case has " ++ Nat.show(count) ++ " branches and the type has " ++ Nat.show(width) ++ " legs"})
    diagrams: List<&2, F.Value.vleg> <- Rules.coll_legs_of(ctx, Rules.former_diagram(former))
    uses: F.Quantity.usage <- Rules.coll_branches(width, 0n, ctx, mode, elimination, Rules.former_shape(former), diagrams, expected)
    return F.Pair2{result, F.Quantity.sequence(U.Kernel.snd(F.Value.t, F.Quantity.usage, inferred), F.Quantity.scale(mode, uses))}


def Rules.pi_branch_binders(binders: F.Pair2<F.Pair2<F.Quantity.t, String>, F.Pair2<F.Quantity.t, String>>,
  +ctx: C.Check.ctx, +mode: F.Quantity.t, +q: F.Quantity.t, domain: F.Value.t, +shape: F.Shape.t<F.Value.t>,
  diagram: F.Value.closure, motive: Maybe<&2, F.Term.motive>, expected: Maybe<&2, F.Value.t>, body: F.Term.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{first, second} = binders
  F.Pair2{+q1, +x1} = first
  F.Pair2{q2, x2} = second
  +point = F.Value.var(C.Check.size(ctx))
  fibre = F.Value.var((C.Check.size(ctx) + 1n : Nat))
  do S.Kernel.Program<F.Quantity.usage>:
    unit: Unit <- Rules.binder_quantity("branch binder", "type", x1, q1, q)
    codomain: F.Value.t <- K.Check.open(ctx, diagram, [point])
    +inner: C.Check.ctx = C.Check.bind(x2, q2, codomain, C.Check.bind(x1, q1, domain, ctx))
    target: F.Value.t <- Rules.elim_result(motive, ctx, expected, F.Value.VIn{shape, F.Value.VAPt{q, point}, [fibre]})
    uses: F.Quantity.usage <- S.Check.check_uses(inner, F.Quantity.runtime(mode), body, target)
    K.Check.close(inner, C.Check.size(ctx), mode, uses, False{})


def Rules.pi_branch(branch: F.Pair2<F.Term.addr, F.Term.leg>, ctx: C.Check.ctx, mode: F.Quantity.t,
  pi: F.Triple3<F.Quantity.t, String, F.Value.t>, shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure,
  motive: Maybe<&2, F.Term.motive>, expected: Maybe<&2, F.Value.t>) -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{key, +leg} = branch
  F.Triple3{q, name, domain} = pi
  do S.Kernel.Program<F.Quantity.usage>:
    k: Nat <- S.Kernel.option(Nat, F.Term.as_aleg(key), F.Error.Wrong_leg{"the branch takes the leg address"})
    unit: Unit <- S.Kernel.guard(Nat.is_eq(k, 0n), F.Error.Wrong_leg{P.Rules.leg_msg})
    binders: F.Pair2<F.Pair2<F.Quantity.t, String>, F.Pair2<F.Quantity.t, String>> <- S.Kernel.option(
      F.Pair2<F.Pair2<F.Quantity.t, String>, F.Pair2<F.Quantity.t, String>>,
      U.Kernel.two(F.Pair2<F.Quantity.t, String>, Rules.leg_binders(leg)), F.Error.Missing_branch{"the branch binds the point and the fibre element (D-M0-3)"})
    Rules.pi_branch_binders(binders, ctx, mode, q, domain, shape, diagram, motive, expected, Rules.leg_body(leg))


def Rules.pi_elim(+ctx: C.Check.ctx, +mode: F.Quantity.t, +elimination: F.Term.elim, +expected: Maybe<&2, F.Value.t>)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    +inferred: S.Kernel.Inferred <- Rules.infer_scrutinee(ctx, mode, elimination)
    +former: Rules.Former <- Rules.former(ctx, U.Kernel.fst(F.Value.t, F.Quantity.usage, inferred), True{}, "the scrutinee is not a left former")
    pi: F.Triple3<F.Quantity.t, String, F.Value.t> <- S.Kernel.option(F.Triple3<F.Quantity.t, String, F.Value.t>,
      P.Rules.as_vpi(F.Value.t, Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    unit: Unit <- Rules.check_motive(Rules.elim_motive(elimination), ctx, Rules.former_whole(former))
    scrutinee: F.Value.t <- K.Check.eval(ctx, Rules.elim_scrutinee(elimination))
    result: F.Value.t <- Rules.elim_result(Rules.elim_motive(elimination), ctx, expected, scrutinee)
    branch: F.Pair2<F.Term.addr, F.Term.leg> <- S.Kernel.option(F.Pair2<F.Term.addr, F.Term.leg>,
      U.Kernel.one(F.Pair2<F.Term.addr, F.Term.leg>, Rules.elim_branches(elimination)), F.Error.Missing_branch{"an elimination at the point shape has one branch"})
    free: F.Quantity.usage <- Rules.pi_branch(branch, ctx, mode, pi, Rules.former_shape(former), Rules.former_diagram(former), Rules.elim_motive(elimination), expected)
    return F.Pair2{result, F.Quantity.sequence(U.Kernel.snd(F.Value.t, F.Quantity.usage, inferred), F.Quantity.scale(mode, free))}
