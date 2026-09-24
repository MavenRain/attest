import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_primitives.bend as P
import ./kernel_context.bend as C
import ./kernel_program.bend as S
import ./kernel_check.bend as K
import ./kernel_rules.bend as R
import ./kernel_eval.bend as E

def Mu.view(-A: Data, shape: F.Shape.t<A>) -> Maybe<&2, F.Pair2<String, List<&2, A>>>:
  F.Shape.inductive(A, shape)

def Mu.params(family: F.Positivity.family) -> F.Positivity.telescope:
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  params
def Mu.indices(family: F.Positivity.family) -> F.Positivity.telescope:
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  indices
def Mu.level(family: F.Positivity.family) -> F.Level.t:
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  level
def Mu.ctor_args(ctor: F.Positivity.ctor) -> F.Positivity.telescope:
  F.Positivity.Ctor{name, args, indices, arity, recursive} = ctor
  args
def Mu.ctor_indices(ctor: F.Positivity.ctor) -> List<&2, F.Term.t>:
  F.Positivity.Ctor{name, args, indices, arity, recursive} = ctor
  indices
def Mu.ctor_name(ctor: F.Positivity.ctor) -> String:
  F.Positivity.Ctor{name, args, indices, arity, recursive} = ctor
  name

def Mu.choose_ctor(hit: Bool, ctor: F.Positivity.ctor, rest: Maybe<&2, F.Positivity.ctor>) -> Maybe<&2, F.Positivity.ctor>:
  match hit:
    case True{}: Some{ctor}
    case False{}: rest
def Mu.find_ctor(ctors: List<&2, F.Positivity.ctor>, +name: String) -> Maybe<&2, F.Positivity.ctor>:
  match ctors:
    case Nil{}: None{}
    case Con{+ctor, rest}: Mu.choose_ctor(String.eq(Mu.ctor_name(ctor), name), ctor, Mu.find_ctor(rest, name))
def Mu.ctor_of(name: String, family: F.Positivity.family) -> Maybe<&2, F.Positivity.ctor>:
  F.Positivity.Family{fname, params, indices, level, status, ctors, positive} = family
  Mu.find_ctor(ctors, name)

def Mu.family_status(status: F.Positivity.ctor_status, positive: Bool, family: F.Positivity.family)
  -> Result<&2, &2, F.Error.t, F.Positivity.family>:
  match status:
    case F.Positivity.Builtin{}: Done{family}
    case F.Positivity.Provisional{}: Done{family}
    case F.Positivity.Complete{names}:
      do Result<&2, &2, F.Error.t, F.Positivity.family>:
        unit: Unit <- U.Kernel.guard(positive, F.Error.Not_yet{"a family that is not strictly positive arrives at M2"})
        return family
def Mu.family_checked(+family: F.Positivity.family) -> Result<&2, &2, F.Error.t, F.Positivity.family>:
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  Mu.family_status(status, positive, family)
def Mu.family(ctx: C.Check.ctx, +name: String) -> Result<&2, &2, F.Error.t, F.Positivity.family>:
  do Result<&2, &2, F.Error.t, F.Positivity.family>:
    family: F.Positivity.family <- U.Kernel.from_maybe(F.Positivity.family, F.Global.find_family(name, C.Check.global(ctx)),
      F.Error.Unbound{"the family " ++ name ++ " is not declared"})
    Mu.family_checked(family)

def Mu.all_erased(args: F.Positivity.telescope) -> Bool:
  match args:
    case Nil{}: True{}
    case Con{arg, rest}:
      F.Triple3{q, name, ty} = arg
      Bool.and(F.Quantity.equal(q, F.Quantity.Zero{}), Mu.all_erased(rest))
def Mu.zero_ctor(ctor: Maybe<&2, F.Positivity.ctor>) -> Bool:
  match ctor:
    case None{}: False{}
    case Some{value}:
      F.Positivity.Ctor{name, args, indices, arity, recursive} = value
      Bool.and(Mu.all_erased(args), Bool.not(recursive))
def Mu.zero_status(status: F.Positivity.ctor_status, family: F.Positivity.family) -> Bool:
  match status:
    case F.Positivity.Provisional{}: False{}
    case F.Positivity.Builtin{}: False{}
    case F.Positivity.Complete{names}:
      match names:
        case Nil{}: True{}
        case Con{name, rest}:
          match rest:
            case Nil{}: Mu.zero_ctor(Mu.ctor_of(name, family))
            case Con{other, more}: False{}
def Mu.zero_eliminable(+family: F.Positivity.family) -> Bool:
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  Mu.zero_status(status, family)
def Mu.subsingleton_result(result: Result<&2, &2, F.Error.t, F.Positivity.family>) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{+family}: Bool.and(F.Level.equal(Mu.level(family), F.Level.zero), Mu.zero_eliminable(family))
def Mu.subsingleton(ctx: C.Check.ctx, name: String) -> Bool:
  Mu.subsingleton_result(Mu.family(ctx, name))

def Mu.terms_of_legs(legs: List<&2, F.Term.leg>) -> List<&2, F.Term.t>:
  match legs:
    case Nil{}: Nil{}
    case Con{leg, rest}: Con{R.Rules.leg_body(leg), Mu.terms_of_legs(rest)}
def Mu.params_of(diagram: F.Term.t) -> S.Kernel.Program<List<&2, F.Term.t>>:
  do S.Kernel.Program<List<&2, F.Term.t>>:
    section: F.Pair2<F.Shape.t<F.Term.t>, List<&2, F.Term.leg>> <- S.Kernel.option(F.Pair2<F.Shape.t<F.Term.t>, List<&2, F.Term.leg>>,
      R.Rules.term_section(diagram), F.Error.Mismatch{P.Rules.diagram_msg})
    return Mu.terms_of_legs(U.Kernel.snd(F.Shape.t<F.Term.t>, List<&2, F.Term.leg>, section))

def Mu.tele_go(tele: F.Positivity.telescope, args: List<&2, F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t,
  +env: List<&2, F.Value.t>, uses: F.Quantity.usage) -> S.Kernel.Program<F.Pair2<List<&2, F.Value.t>, F.Quantity.usage>>:
  match tele args:
    case Nil{} Nil{}: S.Kernel.Done{F.Pair2{env, uses}}
    case Con{F.Triple3{q, name, ty}, rest} Con{+arg, more}:
      do S.Kernel.Program<F.Pair2<List<&2, F.Value.t>, F.Quantity.usage>>:
        tyv: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, ty))
        arg_uses: F.Quantity.usage <- S.Check.check_uses(ctx, F.Quantity.mul(mode, q), arg, tyv)
        value: F.Value.t <- K.Check.eval(ctx, arg)
        Mu.tele_go(rest, more, ctx, mode, Con{value, env}, F.Quantity.sequence(uses, arg_uses))
    case Nil{} Con{arg, more}: S.Kernel.Fail{F.Error.Mismatch{"telescope length mismatch"}}
    case Con{binder, rest} Nil{}: S.Kernel.Fail{F.Error.Mismatch{"telescope length mismatch"}}
def Mu.telescope(+ctx: C.Check.ctx, mode: F.Quantity.t, what: String, +tele: F.Positivity.telescope,
  +args: List<&2, F.Term.t>, env: List<&2, F.Value.t>) -> S.Kernel.Program<F.Pair2<List<&2, F.Value.t>, F.Quantity.usage>>:
  +want = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, tele)
  +got = List.length(&2, F.Term.t, args)
  do S.Kernel.Program<F.Pair2<List<&2, F.Value.t>, F.Quantity.usage>>:
    unit: Unit <- S.Kernel.guard(Nat.is_eq(want, got), F.Error.Mismatch{what ++ " takes " ++ Nat.show(want) ++ " arguments and the term gives " ++ Nat.show(got)})
    Mu.tele_go(tele, args, ctx, mode, env, F.Quantity.empty)

def Mu.form(+ctx: C.Check.ctx, +name: String, indices: List<&2, F.Term.t>, diagram: F.Term.t) -> S.Kernel.Program<F.Level.t>:
  do S.Kernel.Program<F.Level.t>:
    +family: F.Positivity.family <- S.Kernel.lift(F.Positivity.family, Mu.family(ctx, name))
    params: List<&2, F.Term.t> <- Mu.params_of(diagram)
    penv: F.Pair2<List<&2, F.Value.t>, F.Quantity.usage> <- Mu.telescope(ctx, F.Quantity.Zero{}, name, Mu.params(family), params, Nil{})
    ienv: F.Pair2<List<&2, F.Value.t>, F.Quantity.usage> <- Mu.telescope(ctx, F.Quantity.Zero{}, "the indices of " ++ name,
      Mu.indices(family), indices, U.Kernel.fst(List<&2, F.Value.t>, F.Quantity.usage, penv))
    return Mu.level(family)

def Mu.force_legs(legs: List<&2, F.Value.vleg>, +ctx: C.Check.ctx) -> S.Kernel.Program<List<&2, F.Value.t>>:
  match legs:
    case Nil{}: S.Kernel.Done{Nil{}}
    case Con{leg, rest}:
      do S.Kernel.Program<List<&2, F.Value.t>>:
        value: F.Value.t <- K.Check.open(ctx, R.Rules.value_leg_closure(leg), Nil{})
        values: List<&2, F.Value.t> <- Mu.force_legs(rest, ctx)
        return Con{value, values}
def Mu.param_env(+ctx: C.Check.ctx, diagram: F.Value.closure) -> S.Kernel.Program<List<&2, F.Value.t>>:
  do S.Kernel.Program<List<&2, F.Value.t>>:
    legs: List<&2, F.Value.vleg> <- R.Rules.coll_legs_of(ctx, diagram)
    values: List<&2, F.Value.t> <- Mu.force_legs(legs, ctx)
    return List.reverse(&2, F.Value.t, values)

def Mu.index_go(indices: List<&2, F.Term.t>, wanted: List<&2, F.Value.t>, +ctx: C.Check.ctx, +env: List<&2, F.Value.t>, +name: String, +ctor: String)
  -> S.Kernel.Program<Unit>:
  match indices wanted:
    case Nil{} Nil{}: S.Kernel.Done{Unit{}}
    case Con{term, rest} Con{+want, more}:
      do S.Kernel.Program<Unit>:
        +got: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, term))
        equal: Bool <- S.Conv.conv_type(ctx, got, want)
        unit: Unit <- S.Kernel.guard(equal, F.Error.Mismatch{"the constructor " ++ ctor ++ " of " ++ name ++ " gives the index " ++
          K.Check.pp_value(ctx, got) ++ " and the type asks for " ++ K.Check.pp_value(ctx, want)})
        Mu.index_go(rest, more, ctx, env, name, ctor)
    case Nil{} Con{value, more}: S.Kernel.Fail{F.Error.Mismatch{"result index length mismatch"}}
    case Con{term, rest} Nil{}: S.Kernel.Fail{F.Error.Mismatch{"result index length mismatch"}}
def Mu.check_indices(ctx: C.Check.ctx, +name: String, ctor: F.Positivity.ctor, +wanted: List<&2, F.Value.t>, env: List<&2, F.Value.t>)
  -> S.Kernel.Program<Unit>:
  F.Positivity.Ctor{+ctor_name, args, +indices, arity, recursive} = ctor
  +got = List.length(&2, F.Term.t, indices)
  +want = List.length(&2, F.Value.t, wanted)
  do S.Kernel.Program<Unit>:
    unit: Unit <- S.Kernel.guard(Nat.is_eq(got, want), F.Error.Mismatch{ctor_name ++ " gives " ++ Nat.show(got) ++ " result indices and " ++ name ++ " takes " ++ Nat.show(want)})
    Mu.index_go(indices, wanted, ctx, env, name, ctor_name)

def Mu.intro_shape(view: F.Pair2<String, List<&2, F.Value.t>>, +ctx: C.Check.ctx, mode: F.Quantity.t,
  diagram: F.Value.closure, addr: F.Term.addr, args: List<&2, F.Term.t>) -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{+name, indices} = view
  do S.Kernel.Program<F.Quantity.usage>:
    +c: String <- S.Kernel.option(String, F.Term.as_actor(addr), F.Error.Wrong_leg{"a constructor takes a constructor address"})
    family: F.Positivity.family <- S.Kernel.lift(F.Positivity.family, Mu.family(ctx, name))
    +ctor: F.Positivity.ctor <- S.Kernel.option(F.Positivity.ctor, Mu.ctor_of(c, family), F.Error.Unbound{c ++ " is not a constructor of " ++ name})
    params: List<&2, F.Value.t> <- Mu.param_env(ctx, diagram)
    +result: F.Pair2<List<&2, F.Value.t>, F.Quantity.usage> <- Mu.telescope(ctx, mode, c, Mu.ctor_args(ctor), args, params)
    unit: Unit <- Mu.check_indices(ctx, name, ctor, indices, U.Kernel.fst(List<&2, F.Value.t>, F.Quantity.usage, result))
    return U.Kernel.snd(List<&2, F.Value.t>, F.Quantity.usage, result)
def Mu.intro(+ctx: C.Check.ctx, mode: F.Quantity.t, addr: F.Term.addr, args: List<&2, F.Term.t>, expected: F.Value.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +former: R.Rules.Former <- R.Rules.former(ctx, expected, True{}, "a constructor needs a left former")
    view: F.Pair2<String, List<&2, F.Value.t>> <- S.Kernel.option(F.Pair2<String, List<&2, F.Value.t>>,
      Mu.view(F.Value.t, R.Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    Mu.intro_shape(view, ctx, mode, R.Rules.former_diagram(former), addr, args)

def Mu.motive_check(+mo: F.Term.motive, +name: String, family: F.Positivity.family, values: List<&2, F.Value.t>) -> S.Kernel.Program<F.Term.motive>:
  F.Term.Motive{ind, indices, self, body} = mo
  +want = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, Mu.indices(family))
  +got = List.length(&2, String, indices)
  +applied = List.length(&2, F.Value.t, values)
  do S.Kernel.Program<F.Term.motive>:
    +mn: String <- S.Kernel.option(String, ind, F.Error.Mismatch{"the motive of an elimination at " ++ name ++ " names no family"})
    a: Unit <- S.Kernel.guard(String.eq(mn, name), F.Error.Mismatch{"the motive is built for " ++ mn ++ " and the scrutinee is at " ++ name})
    b: Unit <- S.Kernel.guard(Nat.is_eq(got, want), F.Error.Mismatch{"the motive of " ++ name ++ " binds " ++ Nat.show(got) ++ " indices and the family has " ++ Nat.show(want)})
    c: Unit <- S.Kernel.guard(Nat.is_eq(applied, want), F.Error.Mismatch{name ++ " is applied to " ++ Nat.show(applied) ++ " indices and the family has " ++ Nat.show(want)})
    return mo

def Mu.motive_of(name: String, family: F.Positivity.family, values: List<&2, F.Value.t>, elimination: F.Term.elim) -> S.Kernel.Program<F.Term.motive>:
  do S.Kernel.Program<F.Term.motive>:
    motive: F.Term.motive <- S.Kernel.option(F.Term.motive, R.Rules.elim_motive(elimination), F.Error.Cannot_infer{"an elimination at a mu shape needs a motive"})
    Mu.motive_check(motive, name, family, values)

def Mu.result(+ctx: C.Check.ctx, motive: F.Term.motive, indices: List<&2, F.Value.t>, self: F.Value.t) -> S.Kernel.Program<F.Value.t>:
  F.Term.Motive{ind, names, self_name, body} = motive
  S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), Con{self, U.Kernel.rev_append(F.Value.t, indices, C.Check.environment(ctx))}, body))

type Mu.Context is Data:
  Mu.Context{ctx: C.Check.ctx, env: List<&2, F.Value.t>, values: List<&2, F.Value.t>}

def Mu.context_ctx(state: Mu.Context) -> C.Check.ctx:
  Mu.Context{ctx, env, values} = state
  ctx
def Mu.context_env(state: Mu.Context) -> List<&2, F.Value.t>:
  Mu.Context{ctx, env, values} = state
  env
def Mu.context_values(state: Mu.Context) -> List<&2, F.Value.t>:
  Mu.Context{ctx, env, values} = state
  values

def Mu.bind_indices(tele: F.Positivity.telescope, names: List<&2, String>, +ctx: C.Check.ctx, +env: List<&2, F.Value.t>, values: List<&2, F.Value.t>)
  -> S.Kernel.Program<Mu.Context>:
  match tele names:
    case Nil{} Nil{}: S.Kernel.Done{Mu.Context{ctx, env, values}}
    case Con{F.Triple3{q, old_name, ty}, rest} Con{name, more}:
      +value = F.Value.var(C.Check.size(ctx))
      do S.Kernel.Program<Mu.Context>:
        tyv: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, ty))
        Mu.bind_indices(rest, more, C.Check.bind(name, F.Quantity.Zero{}, tyv, ctx), Con{value, env}, Con{value, values})
    case Nil{} Con{name, more}: S.Kernel.Fail{F.Error.Mismatch{"motive index length mismatch"}}
    case Con{binder, rest} Nil{}: S.Kernel.Fail{F.Error.Mismatch{"motive index length mismatch"}}

def Mu.motive_level(ctx: C.Check.ctx, +name: String, family: F.Positivity.family, motive: F.Term.motive,
  diagram: F.Value.closure, level: Maybe<&2, F.Level.t>, env: List<&2, F.Value.t>) -> S.Kernel.Program<F.Level.t>:
  F.Term.Motive{ind, +names, self, body} = motive
  +tele = Mu.indices(family)
  do S.Kernel.Program<F.Level.t>:
    unit: Unit <- S.Kernel.guard(Nat.is_eq(List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, tele), List.length(&2, String, names)),
      F.Error.Mismatch{"the motive of " ++ name ++ " does not bind the indices"})
    +state: Mu.Context <- Mu.bind_indices(tele, names, ctx, env, Nil{})
    S.Check.infer_univ(C.Check.bind(self, F.Quantity.Zero{}, F.Value.VLan{F.Shape.make_inductive(F.Value.t, name,
      List.reverse(&2, F.Value.t, Mu.context_values(state))), diagram, level}, Mu.context_ctx(state)), body)

def Mu.large(name: String, +family: F.Positivity.family, level: F.Level.t) -> S.Kernel.Program<Unit>:
  S.Kernel.guard(Bool.or(Bool.not(F.Level.equal(Mu.level(family), F.Level.zero)),
    Bool.or(F.Level.equal(level, F.Level.zero), Mu.zero_eliminable(family))),
    F.Error.Universe{"a large elimination out of a proposition needs a subsingleton family at " ++ name})

def Mu.ctor_names(name: String, family: F.Positivity.family) -> S.Kernel.Program<List<&2, String>>:
  F.Positivity.Family{family_name, params, indices, level, status, ctors, positive} = family
  match status:
    case F.Positivity.Complete{names}: S.Kernel.Done{names}
    case F.Positivity.Provisional{}: S.Kernel.Fail{F.Error.Unbound{"the family " ++ name ++ " is still under declaration"}}
    case F.Positivity.Builtin{}: S.Kernel.Fail{F.Error.Mismatch{"the family " ++ name ++ " is a kernel family and has no branches"}}

def Mu.keys(branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +name: String) -> S.Kernel.Program<List<&2, String>>:
  match branches:
    case Nil{}: S.Kernel.Done{Nil{}}
    case Con{branch, rest}:
      F.Pair2{addr, leg} = branch
      do S.Kernel.Program<List<&2, String>>:
        key: String <- S.Kernel.option(String, F.Term.as_actor(addr), F.Error.Wrong_leg{"a branch of " ++ name ++ " takes the constructor address"})
        more: List<&2, String> <- Mu.keys(rest, name)
        return Con{key, more}

def Mu.count(keys: List<&2, String>, +name: String) -> Nat:
  match keys:
    case Nil{}: 0n
    case Con{key, rest}: (U32.to_nat(Bool.to_u32(String.eq(key, name))) + Mu.count(rest, name) : Nat)

def Mu.cover_count(count: Nat, name: String, ctor: String) -> S.Kernel.Program<Unit>:
  match count:
    case Zero{}: S.Kernel.Fail{F.Error.Missing_branch{"the elimination of " ++ name ++ " has no branch at " ++ ctor}}
    case Succ{pred}:
      S.Kernel.guard(Nat.is_eq(pred, 0n), F.Error.Wrong_leg{"the elimination of " ++ name ++ " repeats the branch at " ++ ctor})
def Mu.cover_names(names: List<&2, String>, +keys: List<&2, String>, +family: String) -> S.Kernel.Program<Unit>:
  match names:
    case Nil{}: S.Kernel.Done{Unit{}}
    case Con{+name, rest}:
      do S.Kernel.Program<Unit>:
        unit: Unit <- Mu.cover_count(Mu.count(keys, name), family, name)
        Mu.cover_names(rest, keys, family)
def Mu.cover_keys(keys: List<&2, String>, +names: List<&2, String>, +family: String) -> S.Kernel.Program<Unit>:
  match keys:
    case Nil{}: S.Kernel.Done{Unit{}}
    case Con{+key, rest}:
      do S.Kernel.Program<Unit>:
        unit: Unit <- S.Kernel.guard(U.Kernel.member(names, key), F.Error.Unbound{key ++ " is not a constructor of " ++ family})
        Mu.cover_keys(rest, names, family)
def Mu.cover(+name: String, +names: List<&2, String>, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>) -> S.Kernel.Program<Unit>:
  do S.Kernel.Program<Unit>:
    +keys: List<&2, String> <- Mu.keys(branches, name)
    unit: Unit <- Mu.cover_names(names, keys, name)
    Mu.cover_keys(keys, names, name)

def Mu.bind_fields(tele: F.Positivity.telescope, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +ctx: C.Check.ctx,
  +env: List<&2, F.Value.t>, values: List<&2, F.Value.t>) -> S.Kernel.Program<Mu.Context>:
  match tele binders:
    case Nil{} Nil{}: S.Kernel.Done{Mu.Context{ctx, env, values}}
    case Con{F.Triple3{+q, name, ty}, rest} Con{F.Pair2{bq, +bx}, more}:
      +value = F.Value.var(C.Check.size(ctx))
      do S.Kernel.Program<Mu.Context>:
        tyv: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, ty))
        unit: Unit <- R.Rules.binder_quantity("branch binder", "field", bx, bq, q)
        Mu.bind_fields(rest, more, C.Check.bind(bx, q, tyv, ctx), Con{value, env}, Con{value, values})
    case Nil{} Con{binder, more}: S.Kernel.Fail{F.Error.Missing_branch{"constructor field length mismatch"}}
    case Con{field, rest} Nil{}: S.Kernel.Fail{F.Error.Missing_branch{"constructor field length mismatch"}}

def Mu.eval_terms(terms: List<&2, F.Term.t>, +ctx: C.Check.ctx, +env: List<&2, F.Value.t>) -> S.Kernel.Program<List<&2, F.Value.t>>:
  match terms:
    case Nil{}: S.Kernel.Done{Nil{}}
    case Con{term, rest}:
      do S.Kernel.Program<List<&2, F.Value.t>>:
        value: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), env, term))
        more: List<&2, F.Value.t> <- Mu.eval_terms(rest, ctx, env)
        return Con{value, more}

def Mu.branch(+ctx: C.Check.ctx, +mode: F.Quantity.t, +name: String, family: F.Positivity.family, motive: F.Term.motive,
  params: List<&2, F.Value.t>, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +c: String) -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +ctor: F.Positivity.ctor <- S.Kernel.option(F.Positivity.ctor, Mu.ctor_of(c, family), F.Error.Unbound{c ++ " is not a constructor of " ++ name})
    +leg: F.Term.leg <- S.Kernel.option(F.Term.leg, E.Eval.branch(branches, F.Value.VACtor{c}), F.Error.Missing_branch{"the elimination of " ++ name ++ " has no branch at " ++ c})
    +want: Nat = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, Mu.ctor_args(ctor))
    +got: Nat = List.length(&2, F.Pair2<F.Quantity.t, String>, R.Rules.leg_binders(leg))
    one: Unit <- S.Kernel.guard(Nat.is_eq(want, got), F.Error.Missing_branch{"the branch at " ++ c ++ " binds " ++ Nat.show(got) ++ " fields and " ++ c ++ " takes " ++ Nat.show(want)})
    +state: Mu.Context <- Mu.bind_fields(Mu.ctor_args(ctor), R.Rules.leg_binders(leg), ctx, params, Nil{})
    +indices: List<&2, F.Value.t> <- Mu.eval_terms(Mu.ctor_indices(ctor), ctx, Mu.context_env(state))
    target: F.Value.t <- Mu.result(ctx, motive, indices, F.Value.VIn{F.Shape.make_inductive(F.Value.t, name, indices), F.Value.VACtor{c}, List.reverse(&2, F.Value.t, Mu.context_values(state))})
    uses: F.Quantity.usage <- S.Check.check_uses(Mu.context_ctx(state), F.Quantity.runtime(mode), R.Rules.leg_body(leg), target)
    K.Check.close(Mu.context_ctx(state), C.Check.size(ctx), mode, uses, False{})

def Mu.branches(names: List<&2, String>, +ctx: C.Check.ctx, +mode: F.Quantity.t, +name: String, +family: F.Positivity.family,
  +motive: F.Term.motive, +params: List<&2, F.Value.t>, +branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>) -> S.Kernel.Program<F.Quantity.usage>:
  match names:
    case Nil{}: S.Kernel.Done{F.Quantity.unreachable}
    case Con{c, rest}:
      do S.Kernel.Program<F.Quantity.usage>:
        uses: F.Quantity.usage <- Mu.branch(ctx, mode, name, family, motive, params, branches, c)
        more: F.Quantity.usage <- Mu.branches(rest, ctx, mode, name, family, motive, params, branches)
        return F.Quantity.alternative(uses, more)

def Mu.former_level(former: R.Rules.Former) -> Maybe<&2, F.Level.t>:
  R.Rules.Former{whole, shape, diagram, level} = former
  level

def Mu.elim_shape(view: F.Pair2<String, List<&2, F.Value.t>>, +former: R.Rules.Former, +ctx: C.Check.ctx,
  +mode: F.Quantity.t, +elimination: F.Term.elim, scrutinee_uses: F.Quantity.usage) -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Pair2{+name, +indices} = view
  do S.Kernel.Program<S.Kernel.Inferred>:
    +family: F.Positivity.family <- S.Kernel.lift(F.Positivity.family, Mu.family(ctx, name))
    +motive: F.Term.motive <- Mu.motive_of(name, family, indices, elimination)
    +params: List<&2, F.Value.t> <- Mu.param_env(ctx, R.Rules.former_diagram(former))
    level: F.Level.t <- Mu.motive_level(ctx, name, family, motive, R.Rules.former_diagram(former), Mu.former_level(former), params)
    a: Unit <- Mu.large(name, family, level)
    +names: List<&2, String> <- Mu.ctor_names(name, family)
    b: Unit <- Mu.cover(name, names, R.Rules.elim_branches(elimination))
    uses: F.Quantity.usage <- Mu.branches(names, ctx, mode, name, family, motive, params, R.Rules.elim_branches(elimination))
    scrutinee: F.Value.t <- K.Check.eval(ctx, R.Rules.elim_scrutinee(elimination))
    result: F.Value.t <- Mu.result(ctx, motive, indices, scrutinee)
    return F.Pair2{result, F.Quantity.sequence(scrutinee_uses, F.Quantity.scale(mode, uses))}

def Mu.elim(+ctx: C.Check.ctx, +mode: F.Quantity.t, +elimination: F.Term.elim) -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    +inferred: S.Kernel.Inferred <- R.Rules.infer_scrutinee(ctx, mode, elimination)
    +former: R.Rules.Former <- R.Rules.former(ctx, U.Kernel.fst(F.Value.t, F.Quantity.usage, inferred), True{}, "the scrutinee is not a left former")
    view: F.Pair2<String, List<&2, F.Value.t>> <- S.Kernel.option(F.Pair2<String, List<&2, F.Value.t>>,
      Mu.view(F.Value.t, R.Rules.former_shape(former)), F.Error.Mismatch{P.Rules.wrong_pack})
    Mu.elim_shape(view, former, ctx, mode, elimination, U.Kernel.snd(F.Value.t, F.Quantity.usage, inferred))
