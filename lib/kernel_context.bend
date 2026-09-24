import Base
import ./foundation.bend as F
import ./kernel_util.bend as U

# A budget is a driver-owned polling state. Stateful checking returns the
# remaining state; the unlimited default does not impose an evaluation bound.
type Budget.t is Data:
  Budget.Unlimited{}
  Budget.Steps{remaining: Nat}

def Budget.unlimited() -> Budget.t:
  Budget.Unlimited{}

def Budget.poll(budget: Budget.t) -> F.Pair2<Bool, Budget.t>:
  match budget:
    case Budget.Unlimited{}:
      F.Pair2{False{}, Budget.Unlimited{}}
    case Budget.Steps{remaining}:
      match remaining:
        case Zero{}:
          F.Pair2{True{}, Budget.Steps{0n}}
        case Succ{pred}:
          F.Pair2{False{}, Budget.Steps{pred}}

type Check.ctx is Data:
  Check.Ctx{globals: F.Global.t, env: List<&2, F.Value.t>,
    locals: List<&2, F.Triple3<String, F.Quantity.t, F.Value.t>>, size: Nat, budget: Budget.t}

type Check.kind is Data:
  Check.Definition{}
  Check.Postulate{}

type Check.decl is Data:
  Check.Decl{d_name: String, d_kind: Check.kind, d_ty: F.Term.t, d_body: Maybe<&2, F.Term.t>}

type Check.family_decl is Data:
  Check.FamilyDecl{fam_name: String, fam_params: F.Positivity.telescope, fam_indices: F.Positivity.telescope, fam_level: F.Level.t}

type Check.ctor_decl is Data:
  Check.CtorDecl{ct_name: String, ct_args: F.Positivity.telescope, ct_res_params: List<&2, F.Term.t>, ct_res_idx: List<&2, F.Term.t>}

def Check.make(globals: F.Global.t, budget: Budget.t) -> Check.ctx:
  Check.Ctx{globals, Nil{}, Nil{}, 0n, budget}

def Check.bind(x: String, q: F.Quantity.t, ty: F.Value.t, ctx: Check.ctx) -> Check.ctx:
  Check.Ctx{globals, env, locals, +size, budget} = ctx
  Check.Ctx{globals, Con{F.Value.var(size), env}, Con{F.Triple3{x, q, ty}, locals}, (size + 1n : Nat), budget}

def Check.define(x: String, q: F.Quantity.t, ty: F.Value.t, value: F.Value.t, ctx: Check.ctx) -> Check.ctx:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  Check.Ctx{globals, Con{value, env}, Con{F.Triple3{x, q, ty}, locals}, (size + 1n : Nat), budget}

def Check.global(ctx: Check.ctx) -> F.Global.t:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  globals

def Check.environment(ctx: Check.ctx) -> List<&2, F.Value.t>:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  env

def Check.size(ctx: Check.ctx) -> Nat:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  size

def Check.budget(ctx: Check.ctx) -> Budget.t:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  budget

def Check.with_budget(ctx: Check.ctx, next: Budget.t) -> Check.ctx:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  Check.Ctx{globals, env, locals, size, next}

def Check.local_names(locals: List<&2, F.Triple3<String, F.Quantity.t, F.Value.t>>) -> List<&2, String>:
  match locals:
    case Nil{}: Nil{}
    case Con{local, rest}:
      F.Triple3{name, q, ty} = local
      Con{name, Check.local_names(rest)}

def Check.names_of(ctx: Check.ctx) -> List<&2, String>:
  Check.Ctx{globals, env, locals, size, budget} = ctx
  Check.local_names(locals)

def Check.readable(mode: F.Quantity.t, q: F.Quantity.t) -> Bool:
  Bool.or(F.Quantity.equal(mode, F.Quantity.Zero{}), Bool.not(F.Quantity.equal(q, F.Quantity.Zero{})))

def Check.no_infer(what: String) -> F.Error.t:
  F.Error.Cannot_infer{what ++ " has no type of its own;  it needs an expected type"}
