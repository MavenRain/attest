import Base
import ./foundation.bend as F
import ./kernel_context.bend as C
import ./kernel_program.bend as S
import ./kernel_check.bend as K
import ./kernel_mu.bend as M
import ./kernel_order.bend as O
import ./kernel_util.bend as U

def Check.missing_body(name: String) -> F.Error.t:
  F.Error.Cannot_infer{"the definition " ++ name ++ " has no body"}

def Check.decl_name(decl: C.Check.decl) -> String:
  C.Check.Decl{name, kind, ty, body} = decl
  name

def Check.declaration_entry(ctx: C.Check.ctx, name: String, kind: C.Check.kind, ty: F.Term.t,
  body: Maybe<&2, F.Term.t>, expected: F.Value.t) -> S.Kernel.Program<F.Global.entry>:
  match kind:
    case C.Check.Postulate{}:
      S.Kernel.Done{F.Global.Axiom{F.Global.AxiomEntry{ty}}}
    case C.Check.Definition{}:
      do S.Kernel.Program<F.Global.entry>:
        +term: F.Term.t <- S.Kernel.option(F.Term.t, body, Check.missing_body(name))
        uses: F.Quantity.usage <- S.Check.check_uses(ctx, F.Quantity.Many{}, term, expected)
        return F.Global.Def{F.Global.DefEntry{ty, term, True{}, None{}, False{}}}

def Check.declaration(+ctx: C.Check.ctx, decl: C.Check.decl) -> S.Kernel.Program<F.Global.entry>:
  C.Check.Decl{name, kind, +ty, body} = decl
  do S.Kernel.Program<F.Global.entry>:
    level: F.Level.t <- S.Check.infer_univ(ctx, ty)
    expected: F.Value.t <- K.Check.eval(ctx, ty)
    Check.declaration_entry(ctx, name, kind, ty, body, expected)

def Check.check_decl(globals: F.Global.t, budget: C.Budget.t, decl: C.Check.decl) -> S.Kernel.Program<F.Global.entry>:
  Check.declaration(C.Check.make(globals, budget), decl)

def Check.decls_go(decls: List<&2, C.Check.decl>, +globals: F.Global.t, +budget: C.Budget.t) -> S.Kernel.Program<List<&2, F.Pair2<String, F.Global.entry>>>:
  match decls:
    case Nil{}:
      S.Kernel.Done{[]}
    case Con{+decl, rest}:
      do S.Kernel.Program<List<&2, F.Pair2<String, F.Global.entry>>>:
        +entry: F.Global.entry <- Check.check_decl(globals, budget, decl)
        rows: List<&2, F.Pair2<String, F.Global.entry>> <- Check.decls_go(rest, F.Global.add(Check.decl_name(decl), entry, globals), budget)
        return Con{F.Pair2{Check.decl_name(decl), entry}, rows}

def Check.check_decls(globals: F.Global.t, budget: C.Budget.t, decls: List<&2, C.Check.decl>) -> S.Kernel.Program<List<&2, F.Pair2<String, F.Global.entry>>>:
  Check.decls_go(decls, globals, budget)

def Check.telescope_go(telescope: F.Positivity.telescope, +ctx: C.Check.ctx) -> S.Kernel.Program<C.Check.ctx>:
  match telescope:
    case Nil{}:
      S.Kernel.Done{ctx}
    case Con{field, rest}:
      F.Triple3{q, name, +ty} = field
      do S.Kernel.Program<C.Check.ctx>:
        level: F.Level.t <- S.Check.infer_univ(ctx, ty)
        value: F.Value.t <- K.Check.eval(ctx, ty)
        Check.telescope_go(rest, C.Check.bind(name, q, value, ctx))

def Check.check_telescope(ctx: C.Check.ctx, telescope: F.Positivity.telescope) -> S.Kernel.Program<C.Check.ctx>:
  Check.telescope_go(telescope, ctx)

def Check.index_rules(ctx: C.Check.ctx, +name: String, +level: F.Level.t, field: F.Triple3<F.Quantity.t, String, F.Term.t>) -> S.Kernel.Program<Unit>:
  F.Triple3{+q, +binder, ty} = field
  do S.Kernel.Program<Unit>:
    quantity: Unit <- S.Kernel.guard(F.Quantity.equal(q, F.Quantity.Zero{}), F.Error.Index_not_zero{"the index " ++ binder ++ " of " ++ name ++ " is at quantity " ++ F.Quantity.to_string(q) ++ " and every index binder is at 0"})
    +inferred: F.Level.t <- S.Check.infer_univ(ctx, ty)
    S.Kernel.guard(Bool.or(F.Level.equal(level, F.Level.zero), F.Level.le(inferred, level)),
      F.Error.Index_above_universe{"the index " ++ binder ++ " of " ++ name ++ " lives at " ++ F.Level.to_string(inferred) ++ " and " ++ name ++ " is declared at " ++ F.Level.to_string(level)})

def Check.index_telescope_go(telescope: F.Positivity.telescope, +ctx: C.Check.ctx, +name: String, +level: F.Level.t) -> S.Kernel.Program<C.Check.ctx>:
  match telescope:
    case Nil{}:
      S.Kernel.Done{ctx}
    case Con{+field, rest}:
      do S.Kernel.Program<C.Check.ctx>:
        rule: Unit <- Check.index_rules(ctx, name, level, field)
        next: C.Check.ctx <- Check.check_telescope(ctx, [field])
        Check.index_telescope_go(rest, next, name, level)

def Check.check_index_telescope(ctx: C.Check.ctx, name: String, level: F.Level.t, telescope: F.Positivity.telescope) -> S.Kernel.Program<C.Check.ctx>:
  Check.index_telescope_go(telescope, ctx, name, level)

def Check.declare_family(+globals: F.Global.t, budget: C.Budget.t, decl: C.Check.family_decl) -> S.Kernel.Program<F.Global.t>:
  C.Check.FamilyDecl{+name, +params, +indices, +level} = decl
  do S.Kernel.Program<F.Global.t>:
    fresh: Unit <- S.Kernel.guard(Bool.not(Maybe.is_some(&2, F.Positivity.family, F.Global.find_family(name, globals))),
      F.Error.Mismatch{"the family " ++ name ++ " is already declared"})
    pctx: C.Check.ctx <- Check.check_telescope(C.Check.make(globals, budget), params)
    ictx: C.Check.ctx <- Check.check_index_telescope(pctx, name, level, indices)
    return F.Global.add_family(name, F.Positivity.Family{name, params, indices, level, F.Positivity.Provisional{}, [], False{}}, globals)

def Check.parameter_at(+index: Nat, term: F.Term.t) -> Bool:
  match term:
    case F.Term.Var{value}:
      Nat.is_eq(value, index)
    case F.Term.Ann{body, ty}:
      Check.parameter_at(index, body)
    case F.Term.Univ{level}:
      False{}
    case F.Term.Lan{shape, diagram}:
      False{}
    case F.Term.Ran{shape, diagram}:
      False{}
    case F.Term.In{shape, addr, args}:
      False{}
    case F.Term.Elim{elimination}:
      False{}
    case F.Term.Sec{shape, legs}:
      False{}
    case F.Term.Out{shape, addr, head}:
      False{}
    case F.Term.Let{name, ty, value, body}:
      False{}
    case F.Term.Global{name}:
      False{}
    case F.Term.Lit{literal}:
      False{}
    case F.Term.Auto{}:
      False{}

def Check.any_parameter(+index: Nat, terms: List<&2, F.Term.t>) -> Bool:
  match terms:
    case Nil{}:
      False{}
    case Con{term, rest}:
      Bool.or(Check.parameter_at(index, term), Check.any_parameter(index, rest))

def Check.parameters_at(terms: List<&2, F.Term.t>, +offset: Nat) -> Bool:
  match terms:
    case Nil{}:
      True{}
    case Con{term, rest}:
      Bool.and(Check.parameter_at(Nat.sub(offset, 1n), term), Check.parameters_at(rest, Nat.sub(offset, 1n)))

def Check.check_fields(fields: F.Positivity.telescope, +ctx: C.Check.ctx, +level: F.Level.t, +name: String, +indices: List<&2, F.Term.t>, +depth: Nat) -> S.Kernel.Program<C.Check.ctx>:
  match fields:
    case Nil{}:
      S.Kernel.Done{ctx}
    case Con{+field, rest}:
      F.Triple3{q, binder, ty} = field
      do S.Kernel.Program<C.Check.ctx>:
        inferred: F.Level.t <- S.Check.infer_univ(ctx, ty)
        allowed: Unit <- S.Kernel.guard(Bool.or(F.Level.le(inferred, level),
          Bool.and(F.Level.equal(level, F.Level.zero), Bool.and(F.Quantity.equal(q, F.Quantity.Zero{}), Check.any_parameter(Nat.sub(depth, 1n), indices)))),
          F.Error.Universe{"a field of " ++ name ++ " exceeds its family universe"})
        next: C.Check.ctx <- Check.check_telescope(ctx, [field])
        Check.check_fields(rest, next, level, name, indices, Nat.sub(depth, 1n))

def Check.check_ctor(ctx: C.Check.ctx, family: F.Positivity.family, +group: List<&2, String>, decl: C.Check.ctor_decl) -> S.Kernel.Program<F.Positivity.ctor>:
  F.Positivity.Family{+family_name, +params, +indices, level, status, ctors, positive} = family
  C.Check.CtorDecl{+name, +args, +result_params, +result_indices} = decl
  +depth = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, args)
  +np = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, params)
  +ni = List.length(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, indices)
  do S.Kernel.Program<F.Positivity.ctor>:
    +actx: C.Check.ctx <- Check.check_fields(args, ctx, level, name, result_indices, depth)
    positive: Unit <- S.Kernel.lift(Unit, O.Positivity.ctor_fields(group, args))
    preserved: Unit <- S.Kernel.guard(Bool.and(Nat.is_eq(List.length(&2, F.Term.t, result_params), np),
      Check.parameters_at(result_params, (depth + np : Nat))), F.Error.Mismatch{"the constructor " ++ name ++ " must preserve its family parameters"})
    penv: F.Pair2<List<&2, F.Value.t>, F.Quantity.usage> <- M.Mu.telescope(actx, F.Quantity.Zero{}, "the parameters of " ++ name, params, result_params, [])
    arity: Unit <- S.Kernel.guard(Nat.is_eq(List.length(&2, F.Term.t, result_indices), ni), F.Error.Mismatch{name ++ " gives " ++ F.Text.nat(List.length(&2, F.Term.t, result_indices)) ++ " result indices and " ++ family_name ++ " takes " ++ F.Text.nat(ni)})
    ienv: F.Pair2<List<&2, F.Value.t>, F.Quantity.usage> <- M.Mu.telescope(actx, F.Quantity.Zero{}, "the result indices of " ++ name, indices, result_indices, U.Kernel.fst(List<&2, F.Value.t>, F.Quantity.usage, penv))
    return F.Positivity.Ctor{name, args, result_indices, (np + depth : Nat), O.Positivity.self_rec(group, args)}

def Check.provisional(name: String, status: F.Positivity.ctor_status) -> S.Kernel.Program<Unit>:
  match status:
    case F.Positivity.Provisional{}:
      S.Kernel.Done{Unit{}}
    case F.Positivity.Builtin{}:
      S.Kernel.Fail{F.Error.Mismatch{"the constructors of " ++ name ++ " are already installed"}}
    case F.Positivity.Complete{names}:
      S.Kernel.Fail{F.Error.Mismatch{"the constructors of " ++ name ++ " are already installed"}}

def Check.ctor_names(decls: List<&2, C.Check.ctor_decl>) -> List<&2, String>:
  match decls:
    case Nil{}:
      []
    case Con{decl, rest}:
      C.Check.CtorDecl{name, args, params, indices} = decl
      Con{name, Check.ctor_names(rest)}

def Check.check_ctors(+ctx: C.Check.ctx, +family: F.Positivity.family, +group: List<&2, String>, decls: List<&2, C.Check.ctor_decl>) -> S.Kernel.Program<List<&2, F.Positivity.ctor>>:
  match decls:
    case Nil{}:
      S.Kernel.Done{[]}
    case Con{decl, rest}:
      do S.Kernel.Program<List<&2, F.Positivity.ctor>>:
        ctor: F.Positivity.ctor <- Check.check_ctor(ctx, family, group, decl)
        ctors: List<&2, F.Positivity.ctor> <- Check.check_ctors(ctx, family, group, rest)
        return Con{ctor, ctors}

def Check.define_found(+globals: F.Global.t, budget: C.Budget.t, group: List<&2, String>, +name: String, +decls: List<&2, C.Check.ctor_decl>, +family: F.Positivity.family) -> S.Kernel.Program<F.Global.t>:
  F.Positivity.Family{family_name, +params, indices, level, status, old_ctors, positive} = family
  do S.Kernel.Program<F.Global.t>:
    provisional: Unit <- Check.provisional(name, status)
    pctx: C.Check.ctx <- Check.check_telescope(C.Check.make(globals, budget), params)
    ctors: List<&2, F.Positivity.ctor> <- Check.check_ctors(pctx, family, group, decls)
    return F.Global.add_family(name, F.Positivity.Family{family_name, params, indices, level, F.Positivity.Complete{Check.ctor_names(decls)}, ctors, True{}}, globals)

def Check.define_ctors(+globals: F.Global.t, budget: C.Budget.t, group: List<&2, String>, +name: String, decls: List<&2, C.Check.ctor_decl>) -> S.Kernel.Program<F.Global.t>:
  do S.Kernel.Program<F.Global.t>:
    family: F.Positivity.family <- S.Kernel.option(F.Positivity.family, F.Global.find_family(name, globals), F.Error.Unbound{"the family " ++ name ++ " is not declared"})
    Check.define_found(globals, budget, group, name, decls, family)
