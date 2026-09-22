import AttestTwin

namespace AccFixture

axiom R : Nat → Nat → Prop

noncomputable def step (x : Nat) (accessible : AttestTwin.Accessible R x) : Nat :=
  AttestTwin.accStep accessible

end AccFixture
