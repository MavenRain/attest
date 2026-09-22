import Base
import ./core.bend as Core

def main() -> Core.Outcome:
  Core.run(9n, Core.Eval{0n,
    Core.Let{Core.Lit{7}, Core.Let{Core.Lit{9}, Core.Var{1n, Unit{}}}}, Unit{}}, Core.Halt{})
