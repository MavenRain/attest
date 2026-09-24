import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_primitives.bend as R
import ./kernel_context.bend as C
import ./kernel_program.bend as S
import ./kernel_eval.bend as E
import ./kernel_pp.bend as T

def Check.pp_result(result: Result<&2, &2, F.Error.t, F.Term.t>, names: List<&2, String>) -> String:
  match result:
    case Fail{error}: "a value that does not read back"
    case Done{term}: T.Pp.term(names, term)

def Check.pp_value(+ctx: C.Check.ctx, value: F.Value.t) -> String:
  Check.pp_result(E.Eval.quote(C.Check.global(ctx), C.Check.size(ctx), value), C.Check.names_of(ctx))

def Check.eval(+ctx: C.Check.ctx, term: F.Term.t) -> S.Kernel.Program<F.Value.t>:
  S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), C.Check.environment(ctx), term))

def Check.whnf(ctx: C.Check.ctx, value: F.Value.t) -> S.Kernel.Program<F.Value.t>:
  S.Kernel.lift(F.Value.t, E.Eval.whnf(C.Check.global(ctx), value))

def Check.open(ctx: C.Check.ctx, closure: F.Value.closure, args: List<&2, F.Value.t>) -> S.Kernel.Program<F.Value.t>:
  S.Kernel.lift(F.Value.t, E.Eval.open_closure(C.Check.global(ctx), closure, args))

def Check.close_test(affine: Bool, level: Nat, uses: F.Quantity.usage) -> Bool:
  match affine:
    case True{}: F.Quantity.at_most_once(level, uses)
    case False{}: F.Quantity.exactly_once(level, uses)

def Check.close_message(affine: Bool, name: String) -> String:
  match affine:
    case True{}: "the linear alias " ++ name ++ " may be used at most once"
    case False{}: "the linear binder " ++ name ++ " must be used exactly once on every runtime path"

def Check.close_one(recent: Bool, runtime_linear: Bool, +affine: Bool, name: String, +level: Nat, +uses: F.Quantity.usage)
  -> Result<&2, &2, F.Error.t, F.Quantity.usage>:
  match recent:
    case False{}: Done{uses}
    case True{}:
      do Result<&2, &2, F.Error.t, F.Quantity.usage>:
        unit: Unit <- U.Kernel.guard(Bool.or(Bool.not(runtime_linear), Check.close_test(affine, level, uses)),
          F.Error.Quantity{Check.close_message(affine, name)})
        return F.Quantity.remove(level, uses)

def Check.close_locals(locals: List<&2, F.Triple3<String, F.Quantity.t, F.Value.t>>, +level: Nat,
  +cutoff: Nat, +mode: F.Quantity.t, +affine: Bool, uses: F.Quantity.usage)
  -> Result<&2, &2, F.Error.t, F.Quantity.usage>:
  match locals:
    case Nil{}: Done{uses}
    case Con{local, rest}:
      F.Triple3{name, q, ty} = local
      do Result<&2, &2, F.Error.t, F.Quantity.usage>:
        free: F.Quantity.usage <- Check.close_one(Nat.is_ge((level - 1n : Nat), cutoff),
          Bool.and(Bool.not(F.Quantity.equal(mode, F.Quantity.Zero{})), F.Quantity.equal(q, F.Quantity.One{})),
          affine, name, (level - 1n : Nat), uses)
        Check.close_locals(rest, (level - 1n : Nat), cutoff, mode, affine, free)

def Check.close(ctx: C.Check.ctx, cutoff: Nat, mode: F.Quantity.t, uses: F.Quantity.usage, affine: Bool)
  -> S.Kernel.Program<F.Quantity.usage>:
  C.Check.Ctx{globals, env, locals, size, budget} = ctx
  S.Kernel.lift(F.Quantity.usage, Check.close_locals(locals, size, cutoff, mode, affine, uses))

def Check.head_local(valid: Bool, locals: List<&2, F.Triple3<String, F.Quantity.t, F.Value.t>>, size: Nat, level: Nat)
  -> S.Kernel.Program<F.Value.t>:
  match valid:
    case False{}: S.Kernel.Fail{F.Error.Unbound{"a local level is outside the context"}}
    case True{}:
      do S.Kernel.Program<F.Value.t>:
        local: F.Triple3<String, F.Quantity.t, F.Value.t> <- S.Kernel.option(F.Triple3<String, F.Quantity.t, F.Value.t>,
          List.get(&2, F.Triple3<String, F.Quantity.t, F.Value.t>, locals, ((size - level : Nat) - 1n : Nat)),
          F.Error.Unbound{"a local level is outside the context"})
        return U.Kernel.third(String, F.Quantity.t, F.Value.t, local)

def Check.head_ty(ctx: C.Check.ctx, head: F.Value.head) -> S.Kernel.Program<F.Value.t>:
  C.Check.Ctx{+globals, env, locals, +size, budget} = ctx
  match head:
    case F.Value.HLocal{+level}: Check.head_local(Nat.is_lt(level, size), locals, size, level)
    case F.Value.HGlobal{+name}:
      do S.Kernel.Program<F.Value.t>:
        entry: F.Global.entry <- S.Kernel.option(F.Global.entry, F.Global.find(name, globals), F.Error.Unbound{name})
        S.Kernel.lift(F.Value.t, E.Eval.eval(globals, Nil{}, F.Global.entry_ty(entry)))

def Check.infer_univ_node(+ctx: C.Check.ctx, term: F.Term.t) -> S.Kernel.Program<F.Level.t>:
  do S.Kernel.Program<F.Level.t>:
    inferred: S.Kernel.Inferred <- S.Check.infer_uses(ctx, F.Quantity.Zero{}, term)
    +weak: F.Value.t <- Check.whnf(ctx, U.Kernel.fst(F.Value.t, F.Quantity.usage, inferred))
    S.Kernel.option(F.Level.t, F.Value.as_univ(weak), F.Error.Universe{"a term used as a type is not a universe:  " ++ Check.pp_value(ctx, weak)})

def Check.ensure(+ctx: C.Check.ctx, +got: F.Value.t, +expected: F.Value.t) -> S.Kernel.Program<Unit>:
  do S.Kernel.Program<Unit>:
    equal: Bool <- S.Conv.conv_type(ctx, got, expected)
    S.Kernel.guard(equal, F.Error.Mismatch{"the term has type " ++ Check.pp_value(ctx, got) ++ " and the expected type is " ++ Check.pp_value(ctx, expected)})

def Check.linear(locals: List<&2, F.Triple3<String, F.Quantity.t, F.Value.t>>, +level: Nat, +uses: F.Quantity.usage) -> Bool:
  match locals:
    case Nil{}: False{}
    case Con{local, rest}:
      F.Triple3{name, q, ty} = local
      Bool.or(Bool.and(F.Quantity.equal(q, F.Quantity.One{}), F.Quantity.used((level - 1n : Nat), uses)),
        Check.linear(rest, (level - 1n : Nat), uses))

def Check.is_linear(ctx: C.Check.ctx, uses: F.Quantity.usage) -> Bool:
  C.Check.Ctx{globals, env, locals, size, budget} = ctx
  Check.linear(locals, size, uses)

def Check.alias_quantity(erased: Bool, linear: Bool) -> F.Quantity.t:
  match erased:
    case True{}: F.Quantity.Zero{}
    case False{}:
      match linear:
        case True{}: F.Quantity.One{}
        case False{}: F.Quantity.Many{}

def Check.let_finish(+ctx: C.Check.ctx, +mode: F.Quantity.t, x: String, ty: F.Value.t,
  +def_uses: F.Quantity.usage, value: F.Value.t, body: C.Check.ctx -> S.Kernel.Program<S.Kernel.Inferred>)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  +linear = Check.is_linear(ctx, def_uses)
  q = Check.alias_quantity(F.Quantity.equal(mode, F.Quantity.Zero{}), linear)
  +inner = C.Check.define(x, q, ty, value, ctx)
  do S.Kernel.Program<S.Kernel.Inferred>:
    +result: S.Kernel.Inferred <- body(inner)
    free: F.Quantity.usage <- Check.close(inner, C.Check.size(ctx), mode, U.Kernel.snd(F.Value.t, F.Quantity.usage, result), linear)
    return F.Pair2{U.Kernel.fst(F.Value.t, F.Quantity.usage, result), F.Quantity.sequence(F.Quantity.scale(mode, def_uses), free)}

def Check.let_body(+ctx: C.Check.ctx, +mode: F.Quantity.t, x: String, +ty: F.Term.t, +definition: F.Term.t,
  body: C.Check.ctx -> S.Kernel.Program<S.Kernel.Inferred>) -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    level: F.Level.t <- S.Check.infer_univ(ctx, ty)
    +tyv: F.Value.t <- Check.eval(ctx, ty)
    uses: F.Quantity.usage <- S.Check.check_uses(ctx, F.Quantity.runtime(mode), definition, tyv)
    value: F.Value.t <- Check.eval(ctx, definition)
    Check.let_finish(ctx, mode, x, tyv, uses, value, body)

def Check.infer_var(local: F.Triple3<String, F.Quantity.t, F.Value.t>, +mode: F.Quantity.t, level: Nat)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Triple3{name, q, ty} = local
  do S.Kernel.Program<S.Kernel.Inferred>:
    unit: Unit <- S.Kernel.guard(C.Check.readable(mode, q), F.Error.Quantity{"the erased binder " ++ name ++ " is read in a runtime position"})
    return F.Pair2{ty, F.Quantity.occurrence(level, mode)}

def Check.infer_index(ctx: C.Check.ctx, mode: F.Quantity.t, +index: Nat) -> S.Kernel.Program<S.Kernel.Inferred>:
  C.Check.Ctx{globals, env, locals, size, budget} = ctx
  do S.Kernel.Program<S.Kernel.Inferred>:
    local: F.Triple3<String, F.Quantity.t, F.Value.t> <- S.Kernel.option(F.Triple3<String, F.Quantity.t, F.Value.t>,
      List.get(&2, F.Triple3<String, F.Quantity.t, F.Value.t>, locals, index),
      F.Error.Unbound{"de Bruijn index " ++ Nat.show(index) ++ " is outside the context"})
    Check.infer_var(local, mode, ((size - index : Nat) - 1n : Nat))

def Check.infer_nat(ctx: C.Check.ctx, sign: Cmp) -> S.Kernel.Program<S.Kernel.Inferred>:
  match sign:
    case LT{}: S.Kernel.Fail{F.Error.Mismatch{"a Nat literal must be nonnegative"}}
    case EQ{}:
      do S.Kernel.Program<S.Kernel.Inferred>:
        ty: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), Nil{}, R.Prim.nat_ty))
        return F.Pair2{ty, F.Quantity.empty}
    case GT{}:
      do S.Kernel.Program<S.Kernel.Inferred>:
        ty: F.Value.t <- S.Kernel.lift(F.Value.t, E.Eval.eval(C.Check.global(ctx), Nil{}, R.Prim.nat_ty))
        return F.Pair2{ty, F.Quantity.empty}

def Check.infer_node(+ctx: C.Check.ctx, +mode: F.Quantity.t, term: F.Term.t) -> S.Kernel.Program<S.Kernel.Inferred>:
  match term:
    case F.Term.Var{index}: Check.infer_index(ctx, mode, index)
    case F.Term.Univ{level}: S.Kernel.Done{F.Pair2{F.Value.VUniv{F.Level.succ(level)}, F.Quantity.empty}}
    case F.Term.Lan{shape, diagram}:
      do S.Kernel.Program<S.Kernel.Inferred>:
        level: F.Level.t <- S.Rules.form(ctx, shape, diagram, None{}, True{})
        return F.Pair2{F.Value.VUniv{level}, F.Quantity.empty}
    case F.Term.Ran{shape, diagram}:
      do S.Kernel.Program<S.Kernel.Inferred>:
        level: F.Level.t <- S.Rules.form(ctx, shape, diagram, None{}, False{})
        return F.Pair2{F.Value.VUniv{level}, F.Quantity.empty}
    case F.Term.Out{shape, addr, scrutinee}: S.Rules.out(ctx, mode, shape, addr, scrutinee)
    case F.Term.Elim{elimination}: S.Rules.elim(ctx, mode, elimination, None{})
    case F.Term.Let{name, ty, definition, body}:
      Check.let_body(ctx, mode, name, ty, definition, inner => S.Check.infer_uses(inner, mode, body))
    case F.Term.Ann{term, +ty}:
      do S.Kernel.Program<S.Kernel.Inferred>:
        level: F.Level.t <- S.Check.infer_univ(ctx, ty)
        +tyv: F.Value.t <- Check.eval(ctx, ty)
        uses: F.Quantity.usage <- S.Check.check_uses(ctx, mode, term, tyv)
        return F.Pair2{tyv, uses}
    case F.Term.Global{name}:
      do S.Kernel.Program<S.Kernel.Inferred>:
        ty: F.Value.t <- Check.head_ty(ctx, F.Value.HGlobal{name})
        return F.Pair2{ty, F.Quantity.empty}
    case F.Term.Lit{literal}:
      match literal:
        case F.Literal.LInt{n}: Check.infer_nat(ctx, F.Bignum.sign(n))
        case F.Literal.LString{s}: S.Kernel.Fail{F.Error.Not_yet{"string types arrive at M1"}}
    case F.Term.In{shape, addr, args}: S.Kernel.Fail{C.Check.no_infer("an injection")}
    case F.Term.Sec{shape, legs}: S.Kernel.Fail{C.Check.no_infer("a section")}
    case F.Term.Auto{}: S.Kernel.Fail{F.Error.Not_yet{R.Rules.auto_word}}

def Check.check_former(+ctx: C.Check.ctx, shape: F.Shape.t<F.Term.t>, diagram: F.Term.t, expected: F.Value.t, left: Bool)
  -> S.Kernel.Program<F.Quantity.usage>:
  do S.Kernel.Program<F.Quantity.usage>:
    +weak: F.Value.t <- Check.whnf(ctx, expected)
    +wanted: F.Level.t <- S.Kernel.option(F.Level.t, F.Value.as_univ(weak),
      F.Error.Universe{"a type former is checked against a type that is not a universe:  " ++ Check.pp_value(ctx, weak)})
    +level: F.Level.t <- S.Rules.form(ctx, shape, diagram, Some{wanted}, left)
    unit: Unit <- S.Kernel.guard(F.Level.equal(level, wanted), F.Error.Universe{"the former lives at " ++ F.Level.to_string(level) ++ " and the expected universe is " ++ F.Level.to_string(wanted)})
    return F.Quantity.empty

def Check.check_inferred(+ctx: C.Check.ctx, result: S.Kernel.Inferred, expected: F.Value.t) -> S.Kernel.Program<F.Quantity.usage>:
  F.Pair2{got, uses} = result
  do S.Kernel.Program<F.Quantity.usage>:
    unit: Unit <- Check.ensure(ctx, got, expected)
    return uses

def Check.check_let(+mode: F.Quantity.t, body: F.Term.t, +expected: F.Value.t, inner: C.Check.ctx) -> S.Kernel.Program<S.Kernel.Inferred>:
  do S.Kernel.Program<S.Kernel.Inferred>:
    uses: F.Quantity.usage <- S.Check.check_uses(inner, mode, body, expected)
    return F.Pair2{expected, uses}

def Check.check_node(+ctx: C.Check.ctx, +mode: F.Quantity.t, +term: F.Term.t, +expected: F.Value.t) -> S.Kernel.Program<F.Quantity.usage>:
  match term:
    case F.Term.Sec{shape, legs}: S.Rules.intro_sec(ctx, mode, shape, legs, expected)
    case F.Term.In{shape, addr, args}: S.Rules.intro_in(ctx, mode, shape, addr, args, expected)
    case F.Term.Elim{elimination}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Rules.elim(ctx, mode, elimination, Some{expected})
        Check.check_inferred(ctx, result, expected)
    case F.Term.Lan{shape, diagram}: Check.check_former(ctx, shape, diagram, expected, True{})
    case F.Term.Ran{shape, diagram}: Check.check_former(ctx, shape, diagram, expected, False{})
    case F.Term.Let{name, ty, definition, body}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- Check.let_body(ctx, mode, name, ty, definition,
          inner => Check.check_let(mode, body, expected, inner))
        return U.Kernel.snd(F.Value.t, F.Quantity.usage, result)
    case F.Term.Var{index}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, term)
        Check.check_inferred(ctx, result, expected)
    case F.Term.Univ{level}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, term)
        Check.check_inferred(ctx, result, expected)
    case F.Term.Out{shape, addr, scrutinee}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, term)
        Check.check_inferred(ctx, result, expected)
    case F.Term.Ann{term, ty}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, F.Term.Ann{term, ty})
        Check.check_inferred(ctx, result, expected)
    case F.Term.Global{name}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, term)
        Check.check_inferred(ctx, result, expected)
    case F.Term.Lit{literal}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, term)
        Check.check_inferred(ctx, result, expected)
    case F.Term.Auto{}:
      do S.Kernel.Program<F.Quantity.usage>:
        result: S.Kernel.Inferred <- S.Check.infer_uses(ctx, mode, term)
        Check.check_inferred(ctx, result, expected)
