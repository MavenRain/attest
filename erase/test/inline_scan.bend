import Base
import ../../lib/foundation.bend as F
import ../inline.bend as I

def main() -> List<&2, Bool>:
  +bound : F.Term.t = F.Term.Ran{F.Shape.SPi{F.Quantity.Zero{}, "x", F.Term.Global{"A"}}, F.Term.Var{0n}}
  +free : F.Term.t = F.Term.Ran{F.Shape.SPi{F.Quantity.Zero{}, "x", F.Term.Global{"A"}}, F.Term.Var{1n}}
  +let_alias : F.Term.t = F.Term.Let{"q", F.Term.Global{"P"}, F.Term.Var{0n}, F.Term.Var{0n}}
  +scrut : F.Term.t = F.Term.Elim{F.Term.Elimination{F.Shape.SColl{0n}, F.Term.Var{0n}, F.Quantity.Zero{}, None{}, Nil{}}}
  +motive : F.Term.t = F.Term.Elim{F.Term.Elimination{F.Shape.SColl{0n}, F.Term.Global{"x"}, F.Quantity.Zero{}, Some{F.Term.Motive{None{}, ["index"], "self", F.Term.Var{2n}}}, Nil{}}}
  [I.Inline.closed(0n, bound),
   Bool.not(I.Inline.closed(0n, free)),
   I.Inline.closed(1n, free),
   I.Inline.occurs(0n, free),
   Bool.not(I.Inline.occurs(0n, bound)),
   I.Inline.typed(0n, F.Term.Ann{F.Term.Global{"x"}, F.Term.Var{0n}}),
   Bool.not(I.Inline.typed(0n, F.Term.Ann{F.Term.Var{0n}, F.Term.Global{"A"}})),
   I.Inline.typed(0n, let_alias),
   I.Inline.occurs(0n, scrut),
   Bool.not(I.Inline.typed(0n, scrut)),
   I.Inline.typed(0n, motive),
   Bool.not(I.Inline.closed(0n, motive)),
   I.Inline.closed(1n, motive),
   I.Inline.typed(0n, F.Term.In{F.Shape.SMu{"Family", [F.Term.Var{0n}]}, F.Term.ACtor{"C"}, Nil{}}),
   Bool.not(I.Inline.closed(0n, F.Term.Sec{F.Shape.SColl{1n}, [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "x"}], F.Term.Var{1n}}]})),
   I.Inline.closed(0n, F.Term.Sec{F.Shape.SColl{1n}, [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "x"}], F.Term.Var{0n}}]})]
