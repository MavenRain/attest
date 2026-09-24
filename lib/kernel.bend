import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_primitives.bend as P
import ./kernel_context.bend as C
import ./kernel_program.bend as S
import ./kernel_check.bend as K
import ./kernel_rules.bend as R
import ./kernel_mu.bend as M
import ./kernel_conv.bend as V
import ./kernel_eval.bend as E
import ./kernel_pp.bend as T
import ./kernel_declarations.bend as D

def Kernel.mu_form(left: Bool, ctx: C.Check.ctx, name: String, indices: List<&2, F.Term.t>, diagram: F.Term.t) -> S.Kernel.Program<F.Level.t>:
  match left:
    case True{}: M.Mu.form(ctx, name, indices, diagram)
    case False{}: S.Kernel.Fail{F.Error.Not_yet{"a right former at a mu shape arrives at M2"}}

def Kernel.form(+shape: F.Shape.t<F.Term.t>, +ctx: C.Check.ctx, +diagram: F.Term.t, +expected: Maybe<&2, F.Level.t>, +left: Bool)
  -> S.Kernel.Program<F.Level.t>:
  F.Shape.fold(F.Term.t, Unit, S.Kernel.Program<F.Level.t>, shape, Unit{},
    q => name => domain => unit => (
      R.Rules.pi_levels(ctx, q, name, domain, diagram, left)
    ),
    width => unit => (
      R.Rules.coll_form(ctx, width, diagram, expected)
    ),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      Kernel.mu_form(left, ctx, name, indices, diagram)
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Kernel.intro_in(+shape: F.Shape.t<F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t, +addr: F.Term.addr,
  +args: List<&2, F.Term.t>, +expected: F.Value.t) -> S.Kernel.Program<F.Quantity.usage>:
  F.Shape.fold(F.Term.t, Unit, S.Kernel.Program<F.Quantity.usage>, shape, Unit{},
    q => name => domain => unit => (
      R.Rules.pi_intro_in(ctx, mode, addr, args, expected)
    ),
    width => unit => (
      R.Rules.coll_intro_in(ctx, mode, addr, args, expected)
    ),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      M.Mu.intro(ctx, mode, addr, args, expected)
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Kernel.intro_sec(+shape: F.Shape.t<F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t, +legs: List<&2, F.Term.leg>, +expected: F.Value.t)
  -> S.Kernel.Program<F.Quantity.usage>:
  F.Shape.fold(F.Term.t, Unit, S.Kernel.Program<F.Quantity.usage>, shape, Unit{},
    q => name => domain => unit => (
      R.Rules.pi_intro_sec(ctx, mode, legs, expected)
    ),
    width => unit => (
      R.Rules.coll_intro_sec(ctx, mode, width, legs, expected)
    ),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{"a right former at a mu shape arrives at M2"}}
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Kernel.elim_shape(+shape: F.Shape.t<F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t, +elimination: F.Term.elim, +expected: Maybe<&2, F.Value.t>)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Shape.fold(F.Term.t, Unit, S.Kernel.Program<S.Kernel.Inferred>, shape, Unit{},
    q => name => domain => unit => (
      R.Rules.pi_elim(ctx, mode, elimination, expected)
    ),
    width => unit => (
      R.Rules.coll_elim(ctx, mode, elimination, expected)
    ),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      M.Mu.elim(ctx, mode, elimination)
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))
def Kernel.elim(ctx: C.Check.ctx, mode: F.Quantity.t, +elimination: F.Term.elim, expected: Maybe<&2, F.Value.t>)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
  Kernel.elim_shape(shape, ctx, mode, elimination, expected)

def Kernel.out(+shape: F.Shape.t<F.Term.t>, +ctx: C.Check.ctx, +mode: F.Quantity.t, +addr: F.Term.addr, +head: F.Term.t)
  -> S.Kernel.Program<S.Kernel.Inferred>:
  F.Shape.fold(F.Term.t, Unit, S.Kernel.Program<S.Kernel.Inferred>, shape, Unit{},
    q => name => domain => unit => (
      R.Rules.pi_out(ctx, mode, addr, head)
    ),
    width => unit => (
      R.Rules.coll_out(ctx, mode, addr, head)
    ),
    a => b => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{"a right former at a mu shape arrives at M2"}}
    ),
    name => indices => unit => (
      S.Kernel.Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Kernel.infer_action(-A: Data, exhausted: Bool, ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t,
  next: S.Kernel.Inferred -> S.Kernel.Program<A>) -> S.Kernel.Program<A>:
  match exhausted:
    case True{}: S.Kernel.Fail{F.Error.Budget_exhausted{"the check budget is exhausted"}}
    case False{}: S.Kernel.Program.bind(S.Kernel.Inferred, A, K.Check.infer_node(ctx, mode, term), next)

# Request expansion follows the original call order. The remaining budget is
# carried through every continuation, including caught universe-check errors.
# Only termination of this unbounded interpreter bypasses Bend's check.
@unsafe def Kernel.run(-A: Data, program: S.Kernel.Program<A>, budget: C.Budget.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>:
  match program:
    case S.Kernel.Done{value}: F.Pair2{Done{value}, budget}
    case S.Kernel.Fail{error}: F.Pair2{Fail{error}, budget}
    case S.Kernel.Infer{ctx, mode, term, next}:
      +polled = C.Budget.poll(budget)
      Kernel.run(A, Kernel.infer_action(A, U.Kernel.fst(Bool, C.Budget.t, polled), ctx, mode, term, next), U.Kernel.snd(Bool, C.Budget.t, polled))
    case S.Kernel.Check{ctx, mode, term, expected, next}:
      Kernel.run(A, S.Kernel.Program.bind(F.Quantity.usage, A, K.Check.check_node(ctx, mode, term, expected), next), budget)
    case S.Kernel.Universe{ctx, term, next}:
      Kernel.run(A, S.Kernel.Program.bind(F.Level.t, A, K.Check.infer_univ_node(ctx, term), next), budget)
    case S.Kernel.TryUniverse{ctx, term, next}:
      +reply = Kernel.run(F.Level.t, K.Check.infer_univ_node(ctx, term), budget)
      Kernel.run(A, next(U.Kernel.result_option(F.Level.t, U.Kernel.fst(Result<&2, &2, F.Error.t, F.Level.t>, C.Budget.t, reply))),
        U.Kernel.snd(Result<&2, &2, F.Error.t, F.Level.t>, C.Budget.t, reply))
    case S.Kernel.Convert{ctx, ty, a, b, next}:
      Kernel.run(A, S.Kernel.Program.bind(Bool, A, V.Conv.conv_node(ctx, ty, a, b), next), budget)
    case S.Kernel.Structural{ctx, a, b, next}:
      Kernel.run(A, S.Kernel.Program.bind(Bool, A, V.Conv.structural_node(ctx, a, b), next), budget)
    case S.Kernel.Form{ctx, shape, diagram, expected, left, next}:
      Kernel.run(A, S.Kernel.Program.bind(F.Level.t, A, Kernel.form(shape, ctx, diagram, expected, left), next), budget)
    case S.Kernel.IntroIn{ctx, mode, shape, addr, args, expected, next}:
      Kernel.run(A, S.Kernel.Program.bind(F.Quantity.usage, A, Kernel.intro_in(shape, ctx, mode, addr, args, expected), next), budget)
    case S.Kernel.IntroSec{ctx, mode, shape, legs, expected, next}:
      Kernel.run(A, S.Kernel.Program.bind(F.Quantity.usage, A, Kernel.intro_sec(shape, ctx, mode, legs, expected), next), budget)
    case S.Kernel.Eliminate{ctx, mode, elimination, expected, next}:
      Kernel.run(A, S.Kernel.Program.bind(S.Kernel.Inferred, A, Kernel.elim(ctx, mode, elimination, expected), next), budget)
    case S.Kernel.Out{ctx, mode, shape, addr, head, next}:
      Kernel.run(A, S.Kernel.Program.bind(S.Kernel.Inferred, A, Kernel.out(shape, ctx, mode, addr, head), next), budget)

def Kernel.map_reply(-A: Data, -B: Data, reply: F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>, f: A -> B)
  -> F.Pair2<Result<&2, &2, F.Error.t, B>, C.Budget.t>:
  F.Pair2{result, budget} = reply
  F.Pair2{Result.map(&2, &2, F.Error.t, A, B, f, result), budget}

def Check.infer_uses_stateful(+ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, S.Kernel.Inferred>, C.Budget.t>:
  Kernel.run(S.Kernel.Inferred, S.Check.infer_uses(ctx, mode, term), C.Check.budget(ctx))
def Check.infer_stateful(ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t>:
  Kernel.map_reply(S.Kernel.Inferred, F.Value.t, Check.infer_uses_stateful(ctx, F.Quantity.runtime(mode), term), value => U.Kernel.fst(F.Value.t, F.Quantity.usage, value))
def Check.check_stateful(+ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t, expected: F.Value.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>:
  Kernel.map_reply(F.Quantity.usage, Unit, Kernel.run(F.Quantity.usage, S.Check.check_uses(ctx, F.Quantity.runtime(mode), term, expected), C.Check.budget(ctx)), uses => Unit{})
def Check.infer_univ_stateful(+ctx: C.Check.ctx, term: F.Term.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, F.Level.t>, C.Budget.t>:
  Kernel.run(F.Level.t, S.Check.infer_univ(ctx, term), C.Check.budget(ctx))
def Check.conv_type_stateful(+ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, Bool>, C.Budget.t>:
  Kernel.run(Bool, S.Conv.conv_type(ctx, a, b), C.Check.budget(ctx))
def Conv.conv_stateful(+ctx: C.Check.ctx, ty: F.Value.t, a: F.Value.t, b: F.Value.t)
  -> F.Pair2<Result<&2, &2, F.Error.t, Bool>, C.Budget.t>:
  Kernel.run(Bool, S.Conv.conv(ctx, ty, a, b), C.Check.budget(ctx))

def Check.infer(ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t, Check.infer_stateful(ctx, mode, term))
def Check.check(ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t, expected: F.Value.t) -> Result<&2, &2, F.Error.t, Unit>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, Unit>, C.Budget.t, Check.check_stateful(ctx, mode, term, expected))
def Check.infer_univ(ctx: C.Check.ctx, term: F.Term.t) -> Result<&2, &2, F.Error.t, F.Level.t>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, F.Level.t>, C.Budget.t, Check.infer_univ_stateful(ctx, term))
def Check.infer_term(globals: F.Global.t, term: F.Term.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  Check.infer(C.Check.make(globals, C.Budget.unlimited), F.Quantity.Many{}, term)
def Check.check_term(globals: F.Global.t, term: F.Term.t, expected: F.Value.t) -> Result<&2, &2, F.Error.t, Unit>:
  Check.check(C.Check.make(globals, C.Budget.unlimited), F.Quantity.Many{}, term, expected)
def Conv.conv_type(ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t) -> Result<&2, &2, F.Error.t, Bool>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, Bool>, C.Budget.t, Check.conv_type_stateful(ctx, a, b))
def Conv.conv(ctx: C.Check.ctx, ty: F.Value.t, a: F.Value.t, b: F.Value.t) -> Result<&2, &2, F.Error.t, Bool>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, Bool>, C.Budget.t, Conv.conv_stateful(ctx, ty, a, b))

def Rules.coll_legs_of(+ctx: C.Check.ctx, diagram: F.Value.closure) -> Result<&2, &2, F.Error.t, List<&2, F.Value.vleg>>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, List<&2, F.Value.vleg>>, C.Budget.t,
    Kernel.run(List<&2, F.Value.vleg>, R.Rules.coll_legs_of(ctx, diagram), C.Check.budget(ctx)))
def Rules.coll_leg_ty(+ctx: C.Check.ctx, legs: List<&2, F.Value.vleg>, k: Nat) -> Result<&2, &2, F.Error.t, F.Value.t>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t,
    Kernel.run(F.Value.t, R.Rules.coll_leg_ty(ctx, legs, k), C.Check.budget(ctx)))

def Check.check_decl_stateful(globals: F.Global.t, +budget: C.Budget.t, declaration: C.Check.decl)
  -> F.Pair2<Result<&2, &2, F.Error.t, F.Global.entry>, C.Budget.t>:
  Kernel.run(F.Global.entry, D.Check.check_decl(globals, budget, declaration), budget)
def Check.check_decls_stateful(globals: F.Global.t, +budget: C.Budget.t, declarations: List<&2, C.Check.decl>)
  -> F.Pair2<Result<&2, &2, F.Error.t, List<&2, F.Pair2<String, F.Global.entry>>>, C.Budget.t>:
  Kernel.run(List<&2, F.Pair2<String, F.Global.entry>>, D.Check.check_decls(globals, budget, declarations), budget)
def Check.declare_family_stateful(globals: F.Global.t, +budget: C.Budget.t, declaration: C.Check.family_decl)
  -> F.Pair2<Result<&2, &2, F.Error.t, F.Global.t>, C.Budget.t>:
  Kernel.run(F.Global.t, D.Check.declare_family(globals, budget, declaration), budget)
def Check.define_ctors_stateful(globals: F.Global.t, +budget: C.Budget.t, group: List<&2, String>, name: String, ctors: List<&2, C.Check.ctor_decl>)
  -> F.Pair2<Result<&2, &2, F.Error.t, F.Global.t>, C.Budget.t>:
  Kernel.run(F.Global.t, D.Check.define_ctors(globals, budget, group, name, ctors), budget)

def Check.check_decls(globals: F.Global.t, declarations: List<&2, C.Check.decl>)
  -> Result<&2, &2, F.Error.t, List<&2, F.Pair2<String, F.Global.entry>>>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, List<&2, F.Pair2<String, F.Global.entry>>>, C.Budget.t,
    Check.check_decls_stateful(globals, C.Budget.unlimited, declarations))
def Check.declare_family(globals: F.Global.t, declaration: C.Check.family_decl) -> Result<&2, &2, F.Error.t, F.Global.t>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, F.Global.t>, C.Budget.t, Check.declare_family_stateful(globals, C.Budget.unlimited, declaration))
def Check.define_ctors(globals: F.Global.t, group: List<&2, String>, name: String, ctors: List<&2, C.Check.ctor_decl>) -> Result<&2, &2, F.Error.t, F.Global.t>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, F.Global.t>, C.Budget.t, Check.define_ctors_stateful(globals, C.Budget.unlimited, group, name, ctors))
