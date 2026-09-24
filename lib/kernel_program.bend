import Base
import ./foundation.bend as F
import ./kernel_context.bend as C

def Kernel.Inferred() -> Data:
  F.Pair2<F.Value.t, F.Quantity.usage>

# Typed requests break the source's mutual recursion without changing which
# operation runs next. A continuation is affine and is resumed exactly once.
type Kernel.Program<-A: Data> is Type:
  Kernel.Done{value: A}
  Kernel.Fail{error: F.Error.t}
  Kernel.Infer{ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t, next: Kernel.Inferred -> Kernel.Program<A>}
  Kernel.Check{ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t, expected: F.Value.t, next: F.Quantity.usage -> Kernel.Program<A>}
  Kernel.Universe{ctx: C.Check.ctx, term: F.Term.t, next: F.Level.t -> Kernel.Program<A>}
  Kernel.TryUniverse{ctx: C.Check.ctx, term: F.Term.t, next: Maybe<&2, F.Level.t> -> Kernel.Program<A>}
  Kernel.Convert{ctx: C.Check.ctx, ty: F.Value.t, a: F.Value.t, b: F.Value.t, next: Bool -> Kernel.Program<A>}
  Kernel.Structural{ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t, next: Bool -> Kernel.Program<A>}
  Kernel.Form{ctx: C.Check.ctx, shape: F.Shape.t<F.Term.t>, diagram: F.Term.t, expected: Maybe<&2, F.Level.t>, left: Bool, next: F.Level.t -> Kernel.Program<A>}
  Kernel.IntroIn{ctx: C.Check.ctx, mode: F.Quantity.t, shape: F.Shape.t<F.Term.t>, addr: F.Term.addr,
    args: List<&2, F.Term.t>, expected: F.Value.t, next: F.Quantity.usage -> Kernel.Program<A>}
  Kernel.IntroSec{ctx: C.Check.ctx, mode: F.Quantity.t, shape: F.Shape.t<F.Term.t>, legs: List<&2, F.Term.leg>,
    expected: F.Value.t, next: F.Quantity.usage -> Kernel.Program<A>}
  Kernel.Eliminate{ctx: C.Check.ctx, mode: F.Quantity.t, elimination: F.Term.elim, expected: Maybe<&2, F.Value.t>, next: Kernel.Inferred -> Kernel.Program<A>}
  Kernel.Out{ctx: C.Check.ctx, mode: F.Quantity.t, shape: F.Shape.t<F.Term.t>, addr: F.Term.addr,
    head: F.Term.t, next: Kernel.Inferred -> Kernel.Program<A>}

def Kernel.Program.pure(-A: Data, value: A) -> Kernel.Program<A>:
  Kernel.Done{value}

# Binding resumes a continuation which can construct another request. This
# is finite for source checks, but is outside Bend's syntactic subterm rule.
# Only termination is unchecked; types and affine usage remain checked.
@unsafe def Kernel.Program.bind(-A: Data, -B: Data, program: Kernel.Program<A>, f: A -> Kernel.Program<B>) -> Kernel.Program<B>:
  match program:
    case Kernel.Done{value}: f(value)
    case Kernel.Fail{error}: Kernel.Fail{error}
    case Kernel.Infer{ctx, mode, term, next}:
      Kernel.Infer{ctx, mode, term, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Check{ctx, mode, term, expected, next}:
      Kernel.Check{ctx, mode, term, expected, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Universe{ctx, term, next}:
      Kernel.Universe{ctx, term, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.TryUniverse{ctx, term, next}:
      Kernel.TryUniverse{ctx, term, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Convert{ctx, ty, a, b, next}:
      Kernel.Convert{ctx, ty, a, b, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Structural{ctx, a, b, next}:
      Kernel.Structural{ctx, a, b, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Form{ctx, shape, diagram, expected, left, next}:
      Kernel.Form{ctx, shape, diagram, expected, left, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.IntroIn{ctx, mode, shape, addr, args, expected, next}:
      Kernel.IntroIn{ctx, mode, shape, addr, args, expected, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.IntroSec{ctx, mode, shape, legs, expected, next}:
      Kernel.IntroSec{ctx, mode, shape, legs, expected, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Eliminate{ctx, mode, elimination, expected, next}:
      Kernel.Eliminate{ctx, mode, elimination, expected, value => Kernel.Program.bind(A, B, next(value), f)}
    case Kernel.Out{ctx, mode, shape, addr, head, next}:
      Kernel.Out{ctx, mode, shape, addr, head, value => Kernel.Program.bind(A, B, next(value), f)}

def Kernel.lift(-A: Data, result: Result<&2, &2, F.Error.t, A>) -> Kernel.Program<A>:
  match result:
    case Fail{error}: Kernel.Fail{error}
    case Done{value}: Kernel.Done{value}

def Kernel.option(-A: Data, value: Maybe<&2, A>, error: F.Error.t) -> Kernel.Program<A>:
  match value:
    case None{}: Kernel.Fail{error}
    case Some{x}: Kernel.Done{x}

def Kernel.guard(ok: Bool, error: F.Error.t) -> Kernel.Program<Unit>:
  match ok:
    case True{}: Kernel.Done{Unit{}}
    case False{}: Kernel.Fail{error}

def Check.infer_uses(ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t) -> Kernel.Program<Kernel.Inferred>:
  Kernel.Infer{ctx, mode, term, value => Kernel.Done{value}}

def Check.check_uses(ctx: C.Check.ctx, mode: F.Quantity.t, term: F.Term.t, expected: F.Value.t) -> Kernel.Program<F.Quantity.usage>:
  Kernel.Check{ctx, mode, term, expected, value => Kernel.Done{value}}

def Check.infer_univ(ctx: C.Check.ctx, term: F.Term.t) -> Kernel.Program<F.Level.t>:
  Kernel.Universe{ctx, term, value => Kernel.Done{value}}

def Check.try_univ(ctx: C.Check.ctx, term: F.Term.t) -> Kernel.Program<Maybe<&2, F.Level.t>>:
  Kernel.TryUniverse{ctx, term, value => Kernel.Done{value}}

def Conv.conv(ctx: C.Check.ctx, ty: F.Value.t, a: F.Value.t, b: F.Value.t) -> Kernel.Program<Bool>:
  Kernel.Convert{ctx, ty, a, b, value => Kernel.Done{value}}

def Conv.conv_type(ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t) -> Kernel.Program<Bool>:
  Conv.conv(ctx, F.Value.VUniv{F.Level.zero}, a, b)

def Conv.structural(ctx: C.Check.ctx, a: F.Value.t, b: F.Value.t) -> Kernel.Program<Bool>:
  Kernel.Structural{ctx, a, b, value => Kernel.Done{value}}

def Rules.form(ctx: C.Check.ctx, shape: F.Shape.t<F.Term.t>, diagram: F.Term.t, expected: Maybe<&2, F.Level.t>, left: Bool)
  -> Kernel.Program<F.Level.t>:
  Kernel.Form{ctx, shape, diagram, expected, left, value => Kernel.Done{value}}

def Rules.intro_in(ctx: C.Check.ctx, mode: F.Quantity.t, shape: F.Shape.t<F.Term.t>, addr: F.Term.addr,
  args: List<&2, F.Term.t>, expected: F.Value.t) -> Kernel.Program<F.Quantity.usage>:
  Kernel.IntroIn{ctx, mode, shape, addr, args, expected, value => Kernel.Done{value}}

def Rules.intro_sec(ctx: C.Check.ctx, mode: F.Quantity.t, shape: F.Shape.t<F.Term.t>, legs: List<&2, F.Term.leg>, expected: F.Value.t)
  -> Kernel.Program<F.Quantity.usage>:
  Kernel.IntroSec{ctx, mode, shape, legs, expected, value => Kernel.Done{value}}

def Rules.elim(ctx: C.Check.ctx, mode: F.Quantity.t, elimination: F.Term.elim, expected: Maybe<&2, F.Value.t>)
  -> Kernel.Program<Kernel.Inferred>:
  Kernel.Eliminate{ctx, mode, elimination, expected, value => Kernel.Done{value}}

def Rules.out(ctx: C.Check.ctx, mode: F.Quantity.t, shape: F.Shape.t<F.Term.t>, addr: F.Term.addr, head: F.Term.t)
  -> Kernel.Program<Kernel.Inferred>:
  Kernel.Out{ctx, mode, shape, addr, head, value => Kernel.Done{value}}
