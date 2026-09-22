import Base
import ../core.bend as Core

# A closed scope cannot supply evidence for any variable index.
def main() -> Core.Term<0n>:
  Core.Var{0n, Unit{}}
