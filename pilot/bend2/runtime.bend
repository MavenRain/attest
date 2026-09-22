import Base
import ./core.bend as Core

def terminal(n: Nat, seed: U32) -> Core.Term<n>:
  match n:
    case 0n:
      Core.Lit{seed}
    case 1n+p:
      Core.Var{0n, Unit{}}

def make(depth: Nat, +n: Nat, +seed: U32) -> Core.Term<n>:
  match depth:
    case 0n:
      terminal(n, seed)
    case 1n+p:
      Core.Let{Core.Lit{seed}, Core.Ann{make(p, 1n+n, (seed + 1 : U32))}}

type Totals is Data:
  Totals{checksum: U32, failures: U32}

def tally(result: Core.Outcome) -> Totals:
  match result:
    case Core.Done{value}:
      Totals{value, 0}
    case Core.Exhausted{}:
      Totals{0, 1}

def combine(a: Totals, b: Totals) -> Totals:
  match a:
    case Totals{sum_a, bad_a}:
      match b:
        case Totals{sum_b, bad_b}:
          Totals{(sum_a + sum_b : U32), (bad_a + bad_b : U32)}

def batch(count: Nat, +depth: Nat, +seed: U32, acc: Totals) -> Totals:
  match count:
    case 0n:
      acc
    case 1n+p:
      batch(p, depth, (seed + 1 : U32), combine(acc,
        tally(Core.run(512n, Core.Eval{0n, make(depth, 0n, seed), Unit{}}, Core.Halt{}))))

def seed_value(value: Maybe<&2, U32>) -> U32:
  match value:
    case None{}:
      0
    case Some{seed}:
      seed

def read_seed(args: List<String>) -> U32:
  match args:
    case Nil{}:
      7
    case Con{arg, rest}:
      seed_value(U32.read(arg))

def display(answer: Totals) -> IO(Unit):
  match answer:
    case Totals{checksum, failures}:
      IO.print(U32.show(checksum) ++ " " ++ U32.show(failures))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    display(batch(2500n, 24n, read_seed(args), Totals{0, 0}))
