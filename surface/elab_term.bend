import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_primitives.bend as K
import syntax.bend as S
import elab_requests.bend as R
import elab_common.bend as H
import elab_refs.bend as A
import elab_forms.bend as B
import elab_cases.bend as D

def Elab.expand(term: S.Syntax.t, +ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>) -> R.Elab.Program<F.Term.t>:
  match term:
    case S.Syntax.SVar{name}: A.Elab.variable(ctx, name)
    case S.Syntax.SNat{value}: R.Elab.Done{F.Term.Lit{F.Literal.LInt{value}}}
    case S.Syntax.SProp{}: R.Elab.Done{F.Term.Univ{F.Level.zero}}
    case S.Syntax.SType{level}: H.Elab.univ_of_bignum(F.Bignum.add(level, F.Bignum.one))
    case S.Syntax.SPrim{prim}: R.Elab.Done{F.Term.Global{S.Syntax.prim_name(prim)}}
    case S.Syntax.SUnit{}: R.Elab.Done{K.Rules.unit_val}
    case S.Syntax.SAuto{}: R.Elab.Done{F.Term.Auto{}}
    case S.Syntax.SPair{a, b}: B.Elab.pair(ctx, expected, a, b)
    case S.Syntax.STuple{items}: B.Elab.tuple(ctx, expected, items)
    case S.Syntax.SSum{items}:
      do R.Elab.Program<F.Term.t>:
        types : List<&2, F.Term.t> <- R.Elab.map(S.Syntax.t, F.Term.t, H.Elab.none_terms, items, ctx)
        return K.Rules.sum_ty(types)
    case S.Syntax.SProd{items}:
      do R.Elab.Program<F.Term.t>:
        types : List<&2, F.Term.t> <- R.Elab.map(S.Syntax.t, F.Term.t, H.Elab.none_terms, items, ctx)
        return K.Rules.prod_ty(types)
    case S.Syntax.SProj{term, key}: B.Elab.projection(ctx, term, key)
    case S.Syntax.SInj{key, arity, term}: B.Elab.injection(ctx, expected, key, arity, term)
    case S.Syntax.SAbsurd{term}:
      do R.Elab.Program<F.Term.t>:
        scrut : F.Term.t <- R.Elab.term(ctx, None{}, term)
        return F.Term.Elim{F.Term.Elimination{F.Shape.SColl{0n}, scrut, F.Quantity.One{}, None{}, Nil{}}}
    case S.Syntax.SApp{fun, arg}: A.Elab.application(ctx, fun, arg)
    case S.Syntax.SFun{binders, body}: B.Elab.function(B.Elab.FunStart{binders, body, ctx, expected})
    case S.Syntax.SArrow{binder, cod}: B.Elab.group(ctx, binder, cod, False{})
    case S.Syntax.SStar{binder, cod}: B.Elab.group(ctx, binder, cod, True{})
    case S.Syntax.SLet{+name, ty, val, body}:
      do R.Elab.Program<F.Term.t>:
        +ty_term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        +ty_value : F.Value.t <- H.Elab.eval(ctx, ty_term)
        +val_term : F.Term.t <- R.Elab.term(ctx, Some{ty_value}, val)
        val_value : F.Value.t <- H.Elab.eval(ctx, val_term)
        body_term : F.Term.t <- R.Elab.term(C.Check.define(name, F.Quantity.Many{}, ty_value, val_value, ctx), expected, body)
        return F.Term.Let{name, ty_term, val_term, body_term}
    case S.Syntax.SAnn{term, ty}:
      do R.Elab.Program<F.Term.t>:
        +ty_term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        ty_value : F.Value.t <- H.Elab.eval(ctx, ty_term)
        term : F.Term.t <- R.Elab.term(ctx, Some{ty_value}, term)
        return F.Term.Ann{term, ty_term}
    case S.Syntax.SCase{scrut, motive, branches}: D.Elab.case(ctx, expected, scrut, motive, branches, False{})
    case S.Syntax.SMatch{scrut, motive, branches}: D.Elab.case(ctx, expected, scrut, motive, branches, True{})
