namespace AttestTwin

inductive Equal : Prop where
  | refl (unit : True) : Equal

def LayoutOf (proof : Equal) : Type :=
  Equal.rec (motive := fun _proof => Type) (fun _unit => PUnit) proof

inductive Accessible (R : Nat → Nat → Prop) : Nat → Prop where
  | intro (x : Nat) (next : (y : Nat) → R y x → Accessible R y) : Accessible R x

noncomputable def accStep {R : Nat → Nat → Prop} {x : Nat}
    (accessible : Accessible R x) : Nat :=
  Accessible.rec (motive := fun _index _proof => Nat)
    (fun _index _next _ih => 0) accessible

end AttestTwin
