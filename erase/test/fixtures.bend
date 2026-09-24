import Base

def Fixture.let_proof() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef Layout : Type 0 := let p : Equal := refl in case p as q in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.scrutinee_proof() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef Layout : Type 0 := case (refl : Equal) as p in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.payload_open_proof() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Function : Type 0 := (0 n : Nat) -> Nat -> Nat\ndef keep : Function := fun (0 n : Nat) (x : Nat) => let p : (0 y : Equal n) -> Equal 0 := ((fun (0 y : Equal n) => refl 0) : (0 y : Equal n) -> Equal 0) in x\n"

def Fixture.lambda_proof() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Layout : Type 0 := let f : (0 n : Nat) -> Equal n := fun (0 n : Nat) => refl n in case f 0 as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.binder_proof() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Layout : Type 0 := case ((let q : Nat := 0 in case (refl q : Equal q) as r in Equal k return Equal k with | refl 0 j => refl j) : Equal 0) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.redeclared_proof() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef Layout : Type 0 := case (refl : Equal) as p in Equal return Type 0 with | refl => Nat\ndef Layout : Type 0 := case (refl : Equal) as p in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.duplicate_payload() -> String:
  "mu One : Prop with\n| tt : One\n\nmu Fam : (0 a : One) -> (0 b : One) -> Type 0 with\n| mk : (0 a : One) -> (0 b : One) -> Fam a b\n\naxiom use : (x : Fam (tt : One) (tt : One)) -> Nat\n"

def Fixture.local_proof() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Layout : (0 n : Nat) -> Type 0 := fun (0 n : Nat) => case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.local_dependent() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => case (refl A x : Equal A x) as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.local_let() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Layout : Type 0 := let n : Nat := 0 in case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_let_alias() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : Type 0 := let A : Type 0 := Nat in case (refl A 0 : Equal A 0) as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_diagram() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom Function : (0 n : Nat) -> (case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()) -> Nat\ndef keep : (x : Nat) -> Nat := fun (x : Nat) => x\n"

def Fixture.local_proof_let_value() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : (0 m : Nat) -> Type 0 := fun (0 m : Nat) => let p : Equal Nat m := refl Nat m in case (refl (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) 0 : Equal (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) 0) as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.local_proof_let_type() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let A : Type 0 := case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case (refl A 0 : Equal A 0) as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_let_alias() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let p2 : Equal Nat 0 := p in let A : Type 0 := case p2 as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case (refl A 0 : Equal A 0) as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_let_family() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let T : (n : Nat) -> Type 0 := fun (n : Nat) => case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case (refl (T 0) 0 : Equal (T 0) 0) as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_let_universe() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef U : Type 1 := Type 0\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let A : U := case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case (refl A 0 : Equal A 0) as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_runtime_call() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\ndef Layout : Type 0 := case (refl : Equal) as p in Equal return Type 0 with | refl => prod ()\ndef keep : (f : Nat -> Layout) -> Nat * Layout := fun (f : Nat -> Layout) => (7, f 0)\n"

def Fixture.branch_local_proof() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\nmu Box : Type 0 with\n| box : (0 n : Nat) -> Box\n\ndef Layout : (b : Box) -> Type 0 := fun (b : Box) => case b as value in Box return Type 0 with | box 0 n => case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout (box 0)) -> Layout (box 0) := fun (x : Layout (box 0)) => x\n"

def Fixture.let_proof_opaque() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\naxiom p : Equal\ndef Layout : Type 0 := case p as q in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.scrutinee_proof_opaque() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\naxiom proof : Equal\ndef Layout : Type 0 := case proof as p in Equal return Type 0 with | refl => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.lambda_proof_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom f : (0 n : Nat) -> Equal n\ndef Layout : Type 0 := case f 0 as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.binder_proof_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom proof : Equal 0\ndef Layout : Type 0 := case proof as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom proof : (0 n : Nat) -> Equal n\ndef Layout : (0 n : Nat) -> Type 0 := fun (0 n : Nat) => case proof n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.local_dependent_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom proof : (0 A : Type 0) -> (0 x : A) -> Equal A x\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => case proof A x as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.local_let_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom proof : (0 n : Nat) -> Equal n\ndef Layout : Type 0 := let n : Nat := 0 in case proof n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_let_alias_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom proof : Equal Nat 0\ndef Layout : Type 0 := let A : Type 0 := Nat in case proof as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_diagram_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom proof : (0 n : Nat) -> Equal n\naxiom Function : (0 n : Nat) -> (case proof n as p in Equal k return Type 0 with | refl 0 j => prod ()) -> Nat\ndef keep : (x : Nat) -> Nat := fun (x : Nat) => x\n"

def Fixture.local_proof_let_value_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom proof : Equal Nat 0\ndef Layout : (0 m : Nat) -> Type 0 := fun (0 m : Nat) => let p : Equal Nat m := refl Nat m in case proof as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.local_proof_let_type_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom proof : Equal Nat 0\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let A : Type 0 := case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case proof as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_let_alias_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom proof : Equal Nat 0\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let p2 : Equal Nat 0 := p in let A : Type 0 := case p2 as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case proof as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_let_family_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom proof : Equal Nat 0\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let T : (n : Nat) -> Type 0 := fun (n : Nat) => case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case proof as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_proof_let_universe_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef U : Type 1 := Type 0\naxiom proof : Equal Nat 0\ndef Layout : Type 0 := let p : Equal Nat 0 := refl Nat 0 in let A : U := case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat in case proof as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout) -> Layout := fun (x : Layout) => x\n"

def Fixture.local_runtime_call_opaque() -> String:
  "mu Equal : Prop with\n| refl : Equal\n\naxiom proof : Equal\ndef Layout : Type 0 := case proof as p in Equal return Type 0 with | refl => prod ()\ndef keep : (f : Nat -> Layout) -> Nat * Layout := fun (f : Nat -> Layout) => (7, f 0)\n"

def Fixture.branch_local_proof_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\nmu Box : Type 0 with\n| box : (0 n : Nat) -> Box\n\naxiom proof : (0 n : Nat) -> Equal n\ndef Layout : (b : Box) -> Type 0 := fun (b : Box) => case b as value in Box return Type 0 with | box 0 n => case proof n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout (box 0)) -> Layout (box 0) := fun (x : Layout (box 0)) => x\n"

def Fixture.source_local_type() -> String:
  "mu Equal : Prop with | refl : Equal\ndef P : (0 n : Nat) -> Prop := fun (0 n : Nat) => Equal\ndef Function : Type 0 := (0 n : Nat) -> Nat -> Nat\ndef keep : Function := fun (0 n : Nat) (x : Nat) =>\nlet p : P n := (refl : P n) in x"

def Fixture.source_local_universe() -> String:
  "def U : Type 0 := prod ()\nmu Equal : (0 x : U) -> Prop with | refl : (0 x : U) -> Equal x\ndef keep : (x : U) -> U := fun (x : U) => let p : Equal x := (refl x : Equal x) in x"

def Fixture.source_local_proof_let() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\ndef Layout : (0 m : Nat) -> Type 0 := fun (0 m : Nat) => let p : Equal Nat m := refl Nat m in let k : (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) := 0 in case (refl (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) 0 : Equal (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) 0) as r in Equal E w return Type 0 with | refl 0 F 0 u => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x"

def Fixture.source_local_payload() -> String:
  "mu Equal : (0 n : Nat) -> Prop with | refl : (0 n : Nat) -> Equal n\ndef keep : (0 n : Nat) -> Nat -> Nat := fun (0 n : Nat) (x : Nat) =>\nlet p : (0 y : Equal n) -> Equal 0 := (fun (0 y : Equal n) => refl 0) in x"

def Fixture.source_local_hypothesis() -> String:
  "mu Same : (0 a : Nat) -> (0 b : Nat) -> Prop with | same : (0 a : Nat) -> Same a a\naxiom expected : (0 h : Same 0 1) -> Same 0 1\ndef drop : (0 e : Same 0 1) -> Nat := fun (0 e : Same 0 1) => 0\ndef g : (0 h : Same 0 1) -> Nat := fun (0 h : Same 0 1) => drop (h : Same 0 1)"
