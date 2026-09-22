import Base
import ../core.bend as Core

# A single let adds one binder, so index one is still out of bounds.
def main() -> Core.Term<0n>:
  Core.Let{Core.Lit{7}, Core.Var{1n, Unit{}}}
