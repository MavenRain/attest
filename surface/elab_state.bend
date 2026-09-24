import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C

type Elab.State<-A: Data> is Type:
  Elab.State{run: C.Budget.t -> F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>}

def Elab.execute(-A: Data, state: Elab.State<A>, budget: C.Budget.t) -> F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>:
  Elab.State{run} = state
  run(budget)

def Elab.bind_result(-A: Data, -B: Data, result: F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>, next: A -> Elab.State<B>) -> F.Pair2<Result<&2, &2, F.Error.t, B>, C.Budget.t>:
  match result:
    case F.Pair2{Fail{error}, budget}: F.Pair2{Fail{error}, budget}
    case F.Pair2{Done{value}, budget}: Elab.execute(B, next(value), budget)

def Elab.State.pure(-A: Data, value: A) -> Elab.State<A>:
  Elab.State{budget => F.Pair2{Done{value}, budget}}

def Elab.State.bind(-A: Data, -B: Data, state: Elab.State<A>, next: A -> Elab.State<B>) -> Elab.State<B>:
  Elab.State{budget => Elab.bind_result(A, B, Elab.execute(A, state, budget), next)}

def Elab.lift(-A: Data, result: Result<&2, &2, F.Error.t, A>) -> Elab.State<A>:
  Elab.State{budget => F.Pair2{result, budget}}

def Elab.option(-A: Data, value: Maybe<&2, A>, error: F.Error.t) -> Elab.State<A>:
  match value:
    case None{}: Elab.lift(A, Fail{error})
    case Some{value}: Elab.State.pure(A, value)

def Elab.fail(-A: Data, error: F.Error.t) -> Elab.State<A>:
  Elab.lift(A, Fail{error})

def Elab.result(-A: Data, result: F.Pair2<Result<&2, &2, F.Error.t, A>, C.Budget.t>) -> Result<&2, &2, F.Error.t, A>:
  F.Pair2{value, budget} = result
  value
