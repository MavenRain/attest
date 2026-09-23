import AttestTwin

def seed : Nat := 0
-- REFUSE: rejected
def rejected (v : Nat ⊕ Nat) : Nat :=
  Sum.elim (fun x => x) (fun _y => Nat) v
