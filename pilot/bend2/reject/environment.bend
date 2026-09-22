import Base
import ../core.bend as Core

# The environment must have exactly the term's scope length.
def main() -> Core.Job:
  Core.Eval{0n, Core.Lit{7}, Core.Cell{7, Unit{}}}
