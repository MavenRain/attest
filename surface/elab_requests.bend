import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import syntax.bend as S

# Requests separate recursive elaboration from its typed sugar rules.
# Kernel requests are interpreted with the runner's current budget.
type Elab.Program<-A: Data> is Type:
  Elab.Done{value: A}
  Elab.Fail{error: F.Error.t}
  Elab.Term{ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>, term: S.Syntax.t, next: F.Term.t -> Elab.Program<A>}
  Elab.Infer{ctx: C.Check.ctx, term: F.Term.t, next: F.Value.t -> Elab.Program<A>}
  Elab.Universe{ctx: C.Check.ctx, term: F.Term.t, next: F.Level.t -> Elab.Program<A>}
  Elab.Convert{ctx: C.Check.ctx, actual: F.Value.t, expected: F.Value.t, next: Bool -> Elab.Program<A>}

def Elab.Program.pure(-A: Data, value: A) -> Elab.Program<A>:
  Elab.Done{value}

# A continuation can produce another request, beyond syntactic subterm recursion.
@unsafe
def Elab.Program.bind(-A: Data, -B: Data, program: Elab.Program<A>, f: A -> Elab.Program<B>) -> Elab.Program<B>:
  match program:
    case Elab.Done{value}: f(value)
    case Elab.Fail{error}: Elab.Fail{error}
    case Elab.Term{ctx, expected, term, next}: Elab.Term{ctx, expected, term, value => Elab.Program.bind(A, B, next(value), f)}
    case Elab.Infer{ctx, term, next}: Elab.Infer{ctx, term, value => Elab.Program.bind(A, B, next(value), f)}
    case Elab.Universe{ctx, term, next}: Elab.Universe{ctx, term, value => Elab.Program.bind(A, B, next(value), f)}
    case Elab.Convert{ctx, actual, expected, next}: Elab.Convert{ctx, actual, expected, value => Elab.Program.bind(A, B, next(value), f)}

def Elab.lift(-A: Data, result: Result<&2, &2, F.Error.t, A>) -> Elab.Program<A>:
  match result:
    case Fail{error}: Elab.Fail{error}
    case Done{value}: Elab.Done{value}

def Elab.option(-A: Data, value: Maybe<&2, A>, error: F.Error.t) -> Elab.Program<A>:
  match value:
    case None{}: Elab.Fail{error}
    case Some{value}: Elab.Done{value}

def Elab.guard(ok: Bool, error: F.Error.t) -> Elab.Program<Unit>:
  match ok:
    case True{}: Elab.Done{Unit{}}
    case False{}: Elab.Fail{error}

def Elab.term(ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>, term: S.Syntax.t) -> Elab.Program<F.Term.t>:
  Elab.Term{ctx, expected, term, value => Elab.Done{value}}

def Elab.infer(ctx: C.Check.ctx, term: F.Term.t) -> Elab.Program<F.Value.t>:
  Elab.Infer{ctx, term, value => Elab.Done{value}}

def Elab.infer_univ(ctx: C.Check.ctx, term: F.Term.t) -> Elab.Program<F.Level.t>:
  Elab.Universe{ctx, term, value => Elab.Done{value}}

def Elab.conv_type(ctx: C.Check.ctx, actual: F.Value.t, expected: F.Value.t) -> Elab.Program<Bool>:
  Elab.Convert{ctx, actual, expected, value => Elab.Done{value}}

def Elab.fst(-A: Data, -B: Data, pair: F.Pair2<A, B>) -> A:
  F.Pair2{fst, snd} = pair
  fst

def Elab.snd(-A: Data, -B: Data, pair: F.Pair2<A, B>) -> B:
  F.Pair2{fst, snd} = pair
  snd

def Elab.first(-A: Data, -B: Data, -D: Data, triple: F.Triple3<A, B, D>) -> A:
  F.Triple3{first, second, third} = triple
  first

def Elab.second(-A: Data, -B: Data, -D: Data, triple: F.Triple3<A, B, D>) -> B:
  F.Triple3{first, second, third} = triple
  second

def Elab.third(-A: Data, -B: Data, -D: Data, triple: F.Triple3<A, B, D>) -> D:
  F.Triple3{first, second, third} = triple
  third

@unsafe
def Elab.map(~A: Data, ~B: Data, ~f: C.Check.ctx -> A -> Elab.Program<B>, xs: List<&2, A>, +ctx: C.Check.ctx) -> Elab.Program<List<&2, B>>:
  match xs:
    case Nil{}: Elab.Done{Nil{}}
    case Con{head, tail}:
      do Elab.Program<List<&2, B>>:
        value : B <- f(ctx, head)
        values : List<&2, B> <- Elab.map(A, B, f, tail, ctx)
        return Con{value, values}
