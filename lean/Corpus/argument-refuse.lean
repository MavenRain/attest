import AttestTwin

def keep (x : Nat) : Nat := x
-- REFUSE: rejected
def rejected : Nat := keep Nat
