import AttestTwin

inductive Equal : Prop where
  | refl : Equal
theorem proof : Equal := .refl
def checked : Type := Equal.rec (motive := fun _ => Type) PUnit proof
