import AttestTwin

inductive Unary : Type where
  | zero : Unary
  | succ (pred : Unary) : Unary

def checked : Unary := Unary.succ (Unary.succ Unary.zero)
