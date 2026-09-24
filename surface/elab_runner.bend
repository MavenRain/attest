import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel.bend as K
import syntax.bend as S
import elab_requests.bend as R
import elab_state.bend as X
import elab_term.bend as T

type Elab.Job<-A: Data> is Type:
  Elab.Running{program: R.Elab.Program<A>, budget: C.Budget.t}
  Elab.ValueResult{result: F.Pair2<Result<&2, &2, F.Error.t, F.Value.t>, C.Budget.t>, next: F.Value.t -> R.Elab.Program<A>}
  Elab.LevelResult{result: F.Pair2<Result<&2, &2, F.Error.t, F.Level.t>, C.Budget.t>, next: F.Level.t -> R.Elab.Program<A>}
  Elab.BoolResult{result: F.Pair2<Result<&2, &2, F.Error.t, Bool>, C.Budget.t>, next: Bool -> R.Elab.Program<A>}

# The source elaborator is unbounded and mutually recursive. This interpreter
# executes its typed requests and preserves budget updates on failures as well.
@unsafe
def Elab.run(-A: Data, job: Elab.Job<A>) -> F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>:
  match job:
    case Elab.Running{program, +budget}:
      match program:
        case R.Elab.Done{value}: F.Pair2{Done{value}, budget}
        case R.Elab.Fail{error}: F.Pair2{Fail{error}, budget}
        case R.Elab.Term{ctx, expected, term, next}: Elab.run(A, Elab.Running{R.Elab.Program.bind(F.Term.t, A, T.Elab.expand(term, ctx, expected), next), budget})
        case R.Elab.Infer{ctx, term, next}: Elab.run(A, Elab.ValueResult{K.Check.infer_stateful(C.Check.with_budget(ctx, budget), F.Quantity.Zero{}, term), next})
        case R.Elab.Universe{ctx, term, next}: Elab.run(A, Elab.LevelResult{K.Check.infer_univ_stateful(C.Check.with_budget(ctx, budget), term), next})
        case R.Elab.Convert{ctx, actual, expected, next}: Elab.run(A, Elab.BoolResult{K.Check.conv_type_stateful(C.Check.with_budget(ctx, budget), actual, expected), next})
    case Elab.ValueResult{result, next}:
      match result:
        case F.Pair2{Fail{error}, budget}: F.Pair2{Fail{error}, budget}
        case F.Pair2{Done{value}, budget}: Elab.run(A, Elab.Running{next(value), budget})
    case Elab.LevelResult{result, next}:
      match result:
        case F.Pair2{Fail{error}, budget}: F.Pair2{Fail{error}, budget}
        case F.Pair2{Done{value}, budget}: Elab.run(A, Elab.Running{next(value), budget})
    case Elab.BoolResult{result, next}:
      match result:
        case F.Pair2{Fail{error}, budget}: F.Pair2{Fail{error}, budget}
        case F.Pair2{Done{value}, budget}: Elab.run(A, Elab.Running{next(value), budget})

def Elab.action(-A: Data, program: R.Elab.Program<A>) -> X.Elab.State<A>:
  X.Elab.State{budget => Elab.run(A, Elab.Running{program, budget})}

def Elab.elab_stateful(+ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>, term: S.Syntax.t) -> F.Pair2<Result<&2, &2, F.Error.t, F.Term.t>, C.Budget.t>:
  Elab.run(F.Term.t, Elab.Running{R.Elab.term(ctx, expected, term), C.Check.budget(ctx)})

def Elab.elab(ctx: C.Check.ctx, expected: Maybe<&2, F.Value.t>, term: S.Syntax.t) -> Result<&2, &2, F.Error.t, F.Term.t>:
  X.Elab.result(F.Term.t, Elab.elab_stateful(ctx, expected, term))
