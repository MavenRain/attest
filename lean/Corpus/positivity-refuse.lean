import AttestTwin

def seed : Nat := 0
-- REFUSE: Bad
inductive Bad : Type where
  | mk : (Bad → Nat) → Bad
