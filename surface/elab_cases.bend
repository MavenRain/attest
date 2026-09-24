import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel_eval.bend as E
import syntax.bend as S
import elab_requests.bend as R
import elab_common.bend as H
import elab_refs.bend as A

type Elab.scope is Data:
  Elab.Scope{ctx: C.Check.ctx, env: List<&2, F.Value.t>, values: List<&2, F.Value.t>}

def Elab.field_binders(+fields: List<&2, S.Syntax.field>) -> List<&2, F.Pair2<F.Quantity.t, String>>:
  match fields:
    case Nil{}: Nil{}
    case Con{S.Syntax.Field{q, name, ty}, tail}: Con{F.Pair2{q, name}, Elab.field_binders(tail)}

def Elab.field_annotation(+field: S.Syntax.field, +ctx: C.Check.ctx,+expected: F.Value.t) -> R.Elab.Program<Unit>:
  match field:
    case S.Syntax.Field{q, name, None{}}: R.Elab.Done{Unit{}}
    case S.Syntax.Field{q, name, Some{ty}}:
      do R.Elab.Program<Unit>:
        +term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        level : F.Level.t <- R.Elab.infer_univ(ctx, term)
        actual : F.Value.t <- H.Elab.eval(ctx, term)
        agrees : Bool <- R.Elab.conv_type(ctx, actual, expected)
        R.Elab.guard(agrees, F.Error.Mismatch{"the annotation of constructor field " ++ name ++ " differs from its declared type"})

@unsafe
def Elab.bind_indices(+indices: F.Positivity.telescope,+names: List<&2, String>, +ctx: C.Check.ctx, +env: List<&2, F.Value.t>,+values: List<&2, F.Value.t>) -> R.Elab.Program<Elab.scope>:
  match indices names:
    case Nil{} Nil{}: R.Elab.Done{Elab.Scope{ctx, env, values}}
    case Con{F.Triple3{q, old_name, ty}, rest} Con{name, names}:
      do R.Elab.Program<Elab.scope>:
        actual : F.Value.t <- R.Elab.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, ty))
        Elab.bind_indices(rest, names, C.Check.bind(name, F.Quantity.Zero{}, actual, ctx), Con{F.Value.var(C.Check.size(ctx)), env}, Con{F.Value.var(C.Check.size(ctx)), values})
    case _ _: R.Elab.Fail{F.Error.Mismatch{"the index telescope and motive names differ"}}

def Elab.bind_field(+field: S.Syntax.field,+ty: F.Value.t,+ctx: C.Check.ctx) -> C.Check.ctx:
  S.Syntax.Field{q, name, annotation} = field
  C.Check.bind(name, q, ty, ctx)

@unsafe
def Elab.bind_fields(+args: F.Positivity.telescope,+fields: List<&2, S.Syntax.field>, +ctx: C.Check.ctx, +env: List<&2, F.Value.t>,+values: List<&2, F.Value.t>) -> R.Elab.Program<Elab.scope>:
  match args fields:
    case Nil{} Nil{}: R.Elab.Done{Elab.Scope{ctx, env, values}}
    case Con{F.Triple3{q, old_name, ty}, args} Con{+field, fields}:
      do R.Elab.Program<Elab.scope>:
        +actual : F.Value.t <- R.Elab.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, ty))
        valid : Unit <- Elab.field_annotation(field, ctx, actual)
        Elab.bind_fields(args, fields, Elab.bind_field(field, actual, ctx), Con{F.Value.var(C.Check.size(ctx)), env}, Con{F.Value.var(C.Check.size(ctx)), values})
    case _ _: R.Elab.Fail{F.Error.Missing_branch{"the field telescope and branch fields differ"}}

def Elab.coll_motive_plain(+ind: Maybe<&2, String>) -> R.Elab.Program<Unit>:
  match ind:
    case None{}: R.Elab.Done{Unit{}}
    case Some{name}: R.Elab.Fail{F.Error.Mismatch{"a case at a collection takes no index clause and its motive names " ++ name}}

def Elab.coll_motive(+motive: Maybe<&2, S.Syntax.motive>,+ctx: C.Check.ctx,+ty: F.Value.t) -> R.Elab.Program<Maybe<&2, F.Term.motive>>:
  match motive:
    case None{}: R.Elab.Done{None{}}
    case Some{S.Syntax.Motive{+name, ind, indices, body}}:
      do R.Elab.Program<Maybe<&2, F.Term.motive>>:
        valid : Unit <- Elab.coll_motive_plain(ind)
        term : F.Term.t <- R.Elab.term(C.Check.bind(name, F.Quantity.Zero{}, ty, ctx), None{}, body)
        return Some{F.Term.Motive{None{}, Nil{}, name, term}}

def Elab.branch_target(+motive: Maybe<&2, F.Term.motive>,+expected: Maybe<&2, F.Value.t>,+self: F.Value.t, +ctx: C.Check.ctx) -> R.Elab.Program<Maybe<&2, F.Value.t>>:
  match motive:
    case None{}: R.Elab.Done{expected}
    case Some{F.Term.Motive{ind, indices, name, body}}:
      do R.Elab.Program<Maybe<&2, F.Value.t>>:
        value : F.Value.t <- R.Elab.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), Con{self, C.Check.environment(ctx)}, body))
        return Some{value}

def Elab.mu_target(+motive: Maybe<&2, F.Term.motive>,+expected: Maybe<&2, F.Value.t>,+indices: List<&2, F.Value.t>,+self: F.Value.t, +ctx: C.Check.ctx) -> R.Elab.Program<Maybe<&2, F.Value.t>>:
  match motive:
    case None{}: R.Elab.Done{expected}
    case Some{F.Term.Motive{ind, names, name, body}}:
      do R.Elab.Program<Maybe<&2, F.Value.t>>:
        value : F.Value.t <- R.Elab.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), Con{self, List.append(&2, F.Value.t, List.reverse(&2, F.Value.t, indices), C.Check.environment(ctx))}, body))
        return Some{value}

def Elab.single_binder(+binders: List<&2, S.Syntax.binder>) -> R.Elab.Program<S.Syntax.binder>:
  match binders:
    case Con{binder, Nil{}}: R.Elab.Done{binder}
    case _: R.Elab.Fail{F.Error.Missing_branch{"each branch binds its payload once"}}

def Elab.coll_branch_binder(+binder: S.Syntax.binder, +key: Nat,+body: S.Syntax.t,+shape: F.Shape.t<F.Value.t>,+legs: List<&2, F.Value.vleg>,+motive: Maybe<&2, F.Term.motive>,+expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx) -> R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
  S.Syntax.Binder{+q, +name, annotation} = binder
  do R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
    ty : F.Value.t <- H.Elab.coll_leg_ty(ctx, legs, key)
    target : Maybe<&2, F.Value.t> <- Elab.branch_target(motive, expected, F.Value.VIn{shape, F.Value.VALeg{key}, [F.Value.var(C.Check.size(ctx))]}, ctx)
    term : F.Term.t <- R.Elab.term(C.Check.bind(name, q, ty, ctx), target, body)
    return F.Pair2{F.Term.ALeg{key}, F.Term.Leg{[F.Pair2{q, name}], term}}

def Elab.coll_branch(+branch: S.Syntax.branch,+shape: F.Shape.t<F.Value.t>,+legs: List<&2, F.Value.vleg>,+motive: Maybe<&2, F.Term.motive>,+expected: Maybe<&2, F.Value.t>,+ctx: C.Check.ctx) -> R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
  match branch:
    case S.Syntax.BrCtor{name, fields, body}: R.Elab.Fail{F.Error.Wrong_leg{"the branch at " ++ name ++ " keys a constructor and a case at a collection keys a leg"}}
    case S.Syntax.BrLeg{key, binders, body}:
      do R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
        binder : S.Syntax.binder <- Elab.single_binder(binders)
        index : Nat <- H.Elab.count(key)
        Elab.coll_branch_binder(binder, index, body, shape, legs, motive, expected, ctx)

@unsafe
def Elab.coll_branches(+branches: List<&2, S.Syntax.branch>, +shape: F.Shape.t<F.Value.t>, +legs: List<&2, F.Value.vleg>, +motive: Maybe<&2, F.Term.motive>, +expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx) -> R.Elab.Program<List<&2, F.Pair2<F.Term.addr, F.Term.leg>>>:
  match branches:
    case Nil{}: R.Elab.Done{Nil{}}
    case Con{head, tail}:
      do R.Elab.Program<List<&2, F.Pair2<F.Term.addr, F.Term.leg>>>:
        branch : F.Pair2<F.Term.addr, F.Term.leg> <- Elab.coll_branch(head, shape, legs, motive, expected, ctx)
        rest : List<&2, F.Pair2<F.Term.addr, F.Term.leg>> <- Elab.coll_branches(tail, shape, legs, motive, expected, ctx)
        return Con{branch, rest}

def Elab.coll_case(+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>,+scrut: F.Term.t,+ty: F.Value.t, +shape: F.Shape.t<F.Value.t>,+closure: F.Value.closure,+motive: Maybe<&2, S.Syntax.motive>,+branches: List<&2, S.Syntax.branch>) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    width : Nat <- H.Elab.collection(shape, "a case eliminates a collection")
    legs : List<&2, F.Value.vleg> <- H.Elab.coll_legs_of(ctx, closure)
    +mot : Maybe<&2, F.Term.motive> <- Elab.coll_motive(motive, ctx, ty)
    brs : List<&2, F.Pair2<F.Term.addr, F.Term.leg>> <- Elab.coll_branches(branches, shape, legs, mot, expected, ctx)
    return F.Term.Elim{F.Term.Elimination{F.Shape.SColl{width}, scrut, F.Quantity.One{}, mot, brs}}

def Elab.mu_motive_scope(+scope: Elab.scope,+name: String,+closure: F.Value.closure,+universe: Maybe<&2, F.Level.t>,+motive: S.Syntax.motive) -> R.Elab.Program<Maybe<&2, F.Term.motive>>:
  Elab.Scope{ctx, env, values} = scope
  S.Syntax.Motive{+self, ind, indices, body} = motive
  self_ty : F.Value.t = F.Value.VLan{F.Shape.SMu{name, List.reverse(&2, F.Value.t, values)}, closure, universe}
  do R.Elab.Program<Maybe<&2, F.Term.motive>>:
    term : F.Term.t <- R.Elab.term(C.Check.bind(self, F.Quantity.Zero{}, self_ty, ctx), None{}, body)
    return Some{F.Term.Motive{ind, indices, self, term}}

def Elab.mu_motive(+motive: Maybe<&2, S.Syntax.motive>,+name: String,+family: F.Positivity.family,+closure: F.Value.closure,+universe: Maybe<&2, F.Level.t>,+env: List<&2, F.Value.t>,+ctx: C.Check.ctx) -> R.Elab.Program<Maybe<&2, F.Term.motive>>:
  match motive:
    case None{}: R.Elab.Done{None{}}
    case Some{+motive}:
      match motive:
        case S.Syntax.Motive{self, ind, +names, body}:
          match family:
            case F.Positivity.Family{fname, params, +indices, level, status, ctors, positive}:
              do R.Elab.Program<Maybe<&2, F.Term.motive>>:
                valid : Unit <- R.Elab.guard(Nat.is_eq(List.length(&2, String, names), List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, indices)), F.Error.Mismatch{"the motive of " ++ name ++ " binds " ++ Nat.show(List.length(&2, String, names)) ++ " index names and the family has " ++ Nat.show(List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, indices))})
                scope : Elab.scope <- Elab.bind_indices(indices, names, ctx, env, Nil{})
                Elab.mu_motive_scope(scope, name, closure, universe, motive)

def Elab.mu_branch_scope(+scope: Elab.scope,+results: List<&2, F.Term.t>, +name: String, +cname: String,+fields: List<&2, S.Syntax.field>,+body: S.Syntax.t,+motive: Maybe<&2, F.Term.motive>,+expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx) -> R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
  Elab.Scope{inner, env, values} = scope
  do R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
    +indices : List<&2, F.Value.t> <- A.Elab.eval_under(results, C.Check.global(ctx), env)
    target : Maybe<&2, F.Value.t> <- Elab.mu_target(motive, expected, indices, F.Value.VIn{F.Shape.SMu{name, indices}, F.Value.VACtor{cname}, List.reverse(&2, F.Value.t, values)}, ctx)
    term : F.Term.t <- R.Elab.term(inner, target, body)
    return F.Pair2{F.Term.ACtor{cname}, F.Term.Leg{Elab.field_binders(fields), term}}

def Elab.mu_branch_ctor(+ctor: F.Positivity.ctor,+name: String, +cname: String, +fields: List<&2, S.Syntax.field>,+body: S.Syntax.t,+motive: Maybe<&2, F.Term.motive>,+env: List<&2, F.Value.t>,+expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx) -> R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
  F.Positivity.Ctor{ctor_name, +args, results, arity, recursive} = ctor
  do R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
    valid : Unit <- R.Elab.guard(Nat.is_eq(List.length(&2, S.Syntax.field, fields), List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, args)), F.Error.Missing_branch{"the branch at " ++ cname ++ " binds " ++ Nat.show(List.length(&2, S.Syntax.field, fields)) ++ " fields and " ++ cname ++ " takes " ++ Nat.show(List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, args))})
    scope : Elab.scope <- Elab.bind_fields(args, fields, ctx, env, Nil{})
    Elab.mu_branch_scope(scope, results, name, cname, fields, body, motive, expected, ctx)

def Elab.mu_branch(+branch: S.Syntax.branch, +name: String,+family: F.Positivity.family,+motive: Maybe<&2, F.Term.motive>,+env: List<&2, F.Value.t>,+expected: Maybe<&2, F.Value.t>,+ctx: C.Check.ctx) -> R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
  match branch:
    case S.Syntax.BrLeg{key, binders, body}: R.Elab.Fail{F.Error.Wrong_leg{"the branch " ++ F.Bignum.to_string(key) ++ " keys a leg and a case at " ++ name ++ " keys a constructor"}}
    case S.Syntax.BrCtor{+cname, fields, body}:
      do R.Elab.Program<F.Pair2<F.Term.addr, F.Term.leg>>:
        ctor : F.Positivity.ctor <- R.Elab.option(F.Positivity.ctor, H.Elab.family_ctor(family, cname), F.Error.Unbound{cname ++ " is not a constructor of " ++ name})
        Elab.mu_branch_ctor(ctor, name, cname, fields, body, motive, env, expected, ctx)

@unsafe
def Elab.mu_branches(+branches: List<&2, S.Syntax.branch>, +name: String, +family: F.Positivity.family, +motive: Maybe<&2, F.Term.motive>, +env: List<&2, F.Value.t>, +expected: Maybe<&2, F.Value.t>, +ctx: C.Check.ctx) -> R.Elab.Program<List<&2, F.Pair2<F.Term.addr, F.Term.leg>>>:
  match branches:
    case Nil{}: R.Elab.Done{Nil{}}
    case Con{head, tail}:
      do R.Elab.Program<List<&2, F.Pair2<F.Term.addr, F.Term.leg>>>:
        branch : F.Pair2<F.Term.addr, F.Term.leg> <- Elab.mu_branch(head, name, family, motive, env, expected, ctx)
        rest : List<&2, F.Pair2<F.Term.addr, F.Term.leg>> <- Elab.mu_branches(tail, name, family, motive, env, expected, ctx)
        return Con{branch, rest}

def Elab.mu_case(+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>,+scrut: F.Term.t, +name: String,+indices: List<&2, F.Value.t>, +closure: F.Value.closure,+universe: Maybe<&2, F.Level.t>,+motive: Maybe<&2, S.Syntax.motive>,+branches: List<&2, S.Syntax.branch>) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    +family : F.Positivity.family <- R.Elab.option(F.Positivity.family, F.Global.find_family(name, C.Check.global(ctx)), F.Error.Unbound{"the family " ++ name ++ " is not declared"})
    +env : List<&2, F.Value.t> <- H.Elab.param_env(ctx, closure)
    +mot : Maybe<&2, F.Term.motive> <- Elab.mu_motive(motive, name, family, closure, universe, env, ctx)
    brs : List<&2, F.Pair2<F.Term.addr, F.Term.leg>> <- Elab.mu_branches(branches, name, family, mot, env, expected, ctx)
    ix : List<&2, F.Term.t> <- R.Elab.map(F.Value.t, F.Term.t, (c => v => H.Elab.quote(c, v)), indices, ctx)
    return F.Term.Elim{F.Term.Elimination{F.Shape.SMu{name, ix}, scrut, F.Quantity.One{}, mot, brs}}

def Elab.case_type(+ty: F.Value.t,+fibered: Bool,+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>,+scrut: F.Term.t,+motive: Maybe<&2, S.Syntax.motive>,+branches: List<&2, S.Syntax.branch>) -> R.Elab.Program<F.Term.t>:
  match ty fibered:
    case F.Value.VLan{F.Shape.SMu{name, indices}, closure, universe} _: Elab.mu_case(ctx, expected, scrut, name, indices, closure, universe, motive, branches)
    case _ True{}: R.Elab.Fail{F.Error.Mismatch{"a match needs a mu family as the type of its scrutinee"}}
    case F.Value.VLan{shape, closure, universe} False{}: Elab.coll_case(ctx, expected, scrut, ty, shape, closure, motive, branches)
    case _ False{}: R.Elab.Fail{F.Error.Mismatch{"a case needs a left former as the type of its scrutinee"}}

def Elab.case(+ctx: C.Check.ctx,+expected: Maybe<&2, F.Value.t>,+scrut: S.Syntax.t,+motive: Maybe<&2, S.Syntax.motive>,+branches: List<&2, S.Syntax.branch>,+fibered: Bool) -> R.Elab.Program<F.Term.t>:
  do R.Elab.Program<F.Term.t>:
    +term : F.Term.t <- R.Elab.term(ctx, None{}, scrut)
    ty : F.Value.t <- H.Elab.type_of(ctx, term)
    Elab.case_type(ty, fibered, ctx, expected, term, motive, branches)
