import AttestTwin

def checked (v : Nat ⊕ Nat) : Nat := Sum.elim (fun x => x) (fun y => y) v
