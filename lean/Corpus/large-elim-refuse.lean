import AttestTwin

inductive Choice : Prop where
  | first : Choice
  | second : Choice
-- REFUSE: rejected
def rejected (p : Choice) : Type :=
  Choice.rec (motive := fun _ => Type) PUnit PUnit p
