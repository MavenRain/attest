import AttestTwin

def seed : Nat := 0
-- REFUSE: rejected
def rejected : Sigma (fun _ : Nat => Nat) := ⟨1, Nat⟩
