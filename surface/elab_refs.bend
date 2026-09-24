import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_eval.bend as E
import syntax.bend as S
import elab_requests.bend as R
import elab_common.bend as H

@unsafe
def Elab.eval_under(+terms: List<&2, F.Term.t>, +globals: F.Global.t, +env: List<&2, F.Value.t>) -> R.Elab.Program<List<&2, F.Value.t>>:
  match terms:
    case Nil{}: R.Elab.Done{Nil{}}
    case Con{head, tail}:
      do R.Elab.Program<List<&2, F.Value.t>>:
        value : F.Value.t <- R.Elab.lift(F.Value.t, E.Eval.eval(globals, env, head))
        rest : List<&2, F.Value.t> <- Elab.eval_under(tail, globals, env)
        return Con{value, rest}

def Elab.fam_ref(+family: F.Positivity.family,+args: List<&2, S.Syntax.t>, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Positivity.Family{+name, +params, indices, level, status, ctors, positive} = family
  +np : Nat = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, params)
  do R.Elab.Program<F.Term.t>:
    valid : Unit <- H.Elab.arity_is(name, (np + List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, indices) : Nat), List.length(&2, S.Syntax.t, args))
    +terms : List<&2, F.Term.t> <- R.Elab.map(S.Syntax.t, F.Term.t, H.Elab.none_terms, args, ctx)
    return F.Term.Lan{F.Shape.SMu{name, List.drop(&2, F.Term.t, terms, np)}, F.Term.Sec{F.Shape.SColl{np}, H.Elab.term_legs(List.take(&2, F.Term.t, terms, np))}}

def Elab.no_ctor_params(+params: F.Positivity.telescope,+name: String) -> R.Elab.Program<Unit>:
  match params:
    case Nil{}: R.Elab.Done{Unit{}}
    case Con{head, tail}: R.Elab.Fail{H.Elab.no_expect("the constructor " ++ name)}

def Elab.ctor_ref(+family: F.Positivity.family,+ctor: F.Positivity.ctor, +args: List<&2, S.Syntax.t>, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Positivity.Family{fname, params, indices, level, status, ctors, positive} = family
  F.Positivity.Ctor{+name, fields, results, arity, recursive} = ctor
  do R.Elab.Program<F.Term.t>:
    valid : Unit <- H.Elab.arity_is(name, List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, fields), List.length(&2, S.Syntax.t, args))
    unparameterized : Unit <- Elab.no_ctor_params(params, name)
    +terms : List<&2, F.Term.t> <- R.Elab.map(S.Syntax.t, F.Term.t, H.Elab.none_terms, args, ctx)
    values : List<&2, F.Value.t> <- R.Elab.map(F.Term.t, F.Value.t, (c => t => H.Elab.eval(c, t)), terms, ctx)
    index_values : List<&2, F.Value.t> <- Elab.eval_under(results, C.Check.global(ctx), List.reverse(&2, F.Value.t, values))
    index_terms : List<&2, F.Term.t> <- R.Elab.map(F.Value.t, F.Term.t, (c => v => H.Elab.quote(c, v)), index_values, ctx)
    return F.Term.In{F.Shape.SMu{fname, index_terms}, F.Term.ACtor{name}, terms}

def Elab.mu_ref(+reference: H.Elab.mu_ref,+args: List<&2, S.Syntax.t>,+ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  match reference:
    case H.Elab.RFam{family}: Elab.fam_ref(family, args, ctx)
    case H.Elab.RCtor{family, ctor}: Elab.ctor_ref(family, ctor, args, ctx)

def Elab.var_ref(+reference: Maybe<&2, H.Elab.mu_ref>,+name: String,+ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  match reference:
    case None{}: R.Elab.Done{H.Elab.local_ref(name, H.Elab.index_of(C.Check.names_of(ctx), name))}
    case Some{reference}: Elab.mu_ref(reference, Nil{}, ctx)

def Elab.variable(+ctx: C.Check.ctx, +name: String) -> R.Elab.Program<F.Term.t>:
  Elab.var_ref(H.Elab.mu_ref_of(ctx, name), name, ctx)

def Elab.application_point_shape(+point: F.Triple3<F.Quantity.t, String, F.Value.t>,+head: F.Term.t,+arg: S.Syntax.t, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Triple3{+q, name, +dom} = point
  do R.Elab.Program<F.Term.t>:
    term : F.Term.t <- R.Elab.term(ctx, Some{dom}, arg)
    dom_term : F.Term.t <- H.Elab.quote(ctx, dom)
    return F.Term.Out{F.Shape.SPi{q, name, dom_term}, F.Term.APt{q, term}, head}

def Elab.application_point_type(+former: F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>>,+head: F.Term.t,+arg: S.Syntax.t, +ctx: C.Check.ctx) -> R.Elab.Program<F.Term.t>:
  F.Triple3{shape, closure, universe} = former
  do R.Elab.Program<F.Term.t>:
    point : F.Triple3<F.Quantity.t, String, F.Value.t> <- H.Elab.point(shape, "the head of an application is not a function")
    Elab.application_point_shape(point, head, arg, ctx)

def Elab.app_point(+ctx: C.Check.ctx,+fun: S.Syntax.t,+arg: S.Syntax.t) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    +head : F.Term.t <- R.Elab.term(ctx, None{}, fun)
    ty : F.Value.t <- H.Elab.type_of(ctx, head)
    former : F.Triple3<F.Shape.t<F.Value.t>, F.Value.closure, Maybe<&2, F.Level.t>> <- H.Elab.right(ty, "the head of an application is not a function")
    Elab.application_point_type(former, head, arg, ctx)

def Elab.app_reference(+reference: Maybe<&2, H.Elab.mu_ref>,+ctx: C.Check.ctx,+fun: S.Syntax.t,+arg: S.Syntax.t,+args: List<&2, S.Syntax.t>) -> R.Elab.Program<F.Term.t>:
  match reference:
    case None{}: Elab.app_point(ctx, fun, arg)
    case Some{reference}: Elab.mu_ref(reference, args, ctx)

def Elab.app_spine(+spine: F.Pair2<S.Syntax.t, List<&2, S.Syntax.t>>, +ctx: C.Check.ctx,+fun: S.Syntax.t,+arg: S.Syntax.t) -> R.Elab.Program<F.Term.t>:
  F.Pair2{head, args} = spine
  match head:
    case S.Syntax.SVar{name}: Elab.app_reference(H.Elab.mu_ref_of(ctx, name), ctx, fun, arg, args)
    case _: Elab.app_point(ctx, fun, arg)

def Elab.application(+ctx: C.Check.ctx, +fun: S.Syntax.t, +arg: S.Syntax.t) -> R.Elab.Program<F.Term.t>:
  Elab.app_spine(H.Elab.spine(S.Syntax.SApp{fun, arg}, Nil{}), ctx, fun, arg)
