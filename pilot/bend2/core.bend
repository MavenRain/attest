import Base

# The finite bound and environment length are checked, not runtime defaults.
law Bound:
  for n: Nat
  for i: Nat
  Data

def Bound(n, i):
  match n:
    case 0n:
      Empty
    case 1n+p:
      match i:
        case 0n:
          Unit
        case 1n+j:
          Bound(p, j)

law Env:
  for n: Nat
  Data

type Env.Cell<-n: Nat> is Data:
  Cell{head: U32, tail: Env(n)}

def Env(n):
  match n:
    case 0n:
      Unit
    case 1n+p:
      Env.Cell<p>

type Term<-n: Nat> is Data:
  Lit{value: U32}
  Var{index: Nat, bound: Bound(n, index)}
  Let{value: Term<n>, body: Term<1n+n>}
  Ann{body: Term<n>}

type Job is Data:
  Eval{n: Nat, term: Term<n>, env: Env(n)}
  Return{value: U32}

type Kont is Data:
  Halt{}
  Bind{n: Nat, body: Term<1n+n>, env: Env(n), next: Kont}

type Outcome is Data:
  Done{value: U32}
  Exhausted{}

def lookup(n: Nat, env: Env(n), i: Nat, bound: Bound(n, i)) -> U32:
  match n:
    case 0n:
      match bound:
    case 1n+p:
      Cell{head, tail} = env
      match i:
        case 0n:
          head
        case 1n+j:
          lookup(p, tail, j, bound)

# One structurally recursive machine replaces the evaluator's callback cycle.
# Fuel exhaustion is explicit and cannot manufacture a successful result.
def run(fuel: Nat, job: Job, stack: Kont) -> Outcome:
  match fuel:
    case 0n:
      Exhausted{}
    case 1n+remaining:
      match job:
        case Eval{+n, term, +env}:
          match term:
            case Lit{value}:
              run(remaining, Return{value}, stack)
            case Var{index, bound}:
              run(remaining, Return{lookup(n, env, index, bound)}, stack)
            case Let{value, body}:
              run(remaining, Eval{n, value, env}, Bind{n, body, env, stack})
            case Ann{body}:
              run(remaining, Eval{n, body, env}, stack)
        case Return{value}:
          match stack:
            case Halt{}:
              Done{value}
            case Bind{n, body, env, next}:
              run(remaining, Eval{1n+n, body, Cell{value, env}}, next)

law lookup_head:
  for +n: Nat
  for +head: U32
  for +tail: Env(n)
  {lookup(1n+n, Cell{head, tail}, 0n, Unit{}) == head : U32}

def lookup_head(n, head, tail):
  {==}

law closed_var_impossible:
  for index: Nat
  for impossible: Bound(0n, index)
  Empty

def closed_var_impossible(index, impossible):
  match impossible:

law lookup_tail:
  for +n: Nat
  for +head: U32
  for +tail: Env(n)
  for +index: Nat
  for +bound: Bound(n, index)
  {lookup(1n+n, Cell{head, tail}, 1n+index, bound) == lookup(n, tail, index, bound) : U32}

def lookup_tail(n, head, tail, index, bound):
  {==}

law let_bound_value:
  for +value: U32
  {run(5n, Eval{0n, Let{Lit{value}, Var{0n, Unit{}}}, Unit{}}, Halt{}) == Done{value} : Outcome}

def let_bound_value(value):
  {==}
