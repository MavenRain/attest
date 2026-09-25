import Base

def Fixture.motive_index() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\nmu Box : (0 n : Nat) -> Type 0 with\n| box : (0 n : Nat) -> Box n\n\ndef keep : (0 n : Nat) -> (b : Box n) -> Nat := fun (0 n : Nat) => fun (b : Box n) => case b as value in Box k return (let p : Equal k := (refl k : Equal k) in Nat) with | box 0 j => 7\n"

def Fixture.motive_index_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\nmu Box : (0 n : Nat) -> Type 0 with\n| box : (0 n : Nat) -> Box n\naxiom proof : (0 n : Nat) -> Equal n\n\ndef keep : (0 n : Nat) -> (b : Box n) -> Nat := fun (0 n : Nat) => fun (b : Box n) => case b as value in Box k return (let p : Equal k := proof k in Nat) with | box 0 j => 7\n"

def Fixture.motive_self() -> String:
  "mu Box : (0 n : Nat) -> Type 0 with\n| box : (0 n : Nat) -> Box n\nmu Same : (0 n : Nat) -> (0 b : Box n) -> Prop with\n| same : (0 n : Nat) -> (0 b : Box n) -> Same n b\n\ndef keep : (0 n : Nat) -> (b : Box n) -> Nat := fun (0 n : Nat) => fun (b : Box n) => case b as value in Box k return (let p : Same k value := (same k value : Same k value) in Nat) with | box 0 j => 7\n"

def Fixture.motive_self_opaque() -> String:
  "mu Box : (0 n : Nat) -> Type 0 with\n| box : (0 n : Nat) -> Box n\nmu Same : (0 n : Nat) -> (0 b : Box n) -> Prop with\n| same : (0 n : Nat) -> (0 b : Box n) -> Same n b\naxiom proof : (0 n : Nat) -> (0 b : Box n) -> Same n b\n\ndef keep : (0 n : Nat) -> (b : Box n) -> Nat := fun (0 n : Nat) => fun (b : Box n) => case b as value in Box k return (let p : Same k value := proof k value in Nat) with | box 0 j => 7\n"

def Fixture.motive_dependent() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\nmu Pack : (0 A : Type 0) -> (0 x : A) -> Type 1 with\n| pack : (0 A : Type 0) -> (0 x : A) -> Pack A x\n\ndef keep : (0 A : Type 0) -> (0 x : A) -> (b : Pack A x) -> Nat := fun (0 A : Type 0) => fun (0 x : A) => fun (b : Pack A x) => case b as value in Pack B y return (let p : Equal B y := (refl B y : Equal B y) in Nat) with | pack 0 C 0 z => 7\n"

def Fixture.motive_dependent_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\nmu Pack : (0 A : Type 0) -> (0 x : A) -> Type 1 with\n| pack : (0 A : Type 0) -> (0 x : A) -> Pack A x\naxiom proof : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef keep : (0 A : Type 0) -> (0 x : A) -> (b : Pack A x) -> Nat := fun (0 A : Type 0) => fun (0 x : A) => fun (b : Pack A x) => case b as value in Pack B y return (let p : Equal B y := proof B y in Nat) with | pack 0 C 0 z => 7\n"

def Fixture.motive_parameter() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\nmu Pack (0 A : Type 0) : (0 x : A) -> Type 0 with\n| pack : (0 x : A) -> Pack A x\n\ndef keep : (0 A : Type 0) -> (0 x : A) -> (b : Pack A x) -> Nat := fun (0 A : Type 0) => fun (0 x : A) => fun (b : Pack A x) => case b as value in Pack y return (let p : Equal A y := (refl A y : Equal A y) in Nat) with | pack 0 z => 7\n"

def Fixture.motive_parameter_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\nmu Pack (0 A : Type 0) : (0 x : A) -> Type 0 with\n| pack : (0 x : A) -> Pack A x\naxiom proof : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef keep : (0 A : Type 0) -> (0 x : A) -> (b : Pack A x) -> Nat := fun (0 A : Type 0) => fun (0 x : A) => fun (b : Pack A x) => case b as value in Pack y return (let p : Equal A y := proof A y in Nat) with | pack 0 z => 7\n"

def Fixture.motive_parameter_indices() -> String:
  "mu Pair (0 A : Type 0) : (0 x : A) -> (0 y : A) -> Type 0 with\n| pair : (0 x : A) -> (0 y : A) -> Pair A x y\nmu Same : (0 A : Type 0) -> (0 x : A) -> (0 y : A) -> (0 b : Pair A x y) -> Prop with\n| same : (0 A : Type 0) -> (0 x : A) -> (0 y : A) -> (0 b : Pair A x y) -> Same A x y b\n\ndef keep : (0 A : Type 0) -> (0 x : A) -> (b : Pair A x x) -> Nat := fun (0 A : Type 0) => fun (0 x : A) => fun (b : Pair A x x) => case b as value in Pair u v return (let p : Same A u v value := (same A u v value : Same A u v value) in Nat) with | pair 0 s 0 t => 7\n"

def Fixture.motive_parameter_indices_opaque() -> String:
  "mu Pair (0 A : Type 0) : (0 x : A) -> (0 y : A) -> Type 0 with\n| pair : (0 x : A) -> (0 y : A) -> Pair A x y\nmu Same : (0 A : Type 0) -> (0 x : A) -> (0 y : A) -> (0 b : Pair A x y) -> Prop with\n| same : (0 A : Type 0) -> (0 x : A) -> (0 y : A) -> (0 b : Pair A x y) -> Same A x y b\naxiom proof : (0 A : Type 0) -> (0 x : A) -> (0 y : A) -> (0 b : Pair A x y) -> Same A x y b\n\ndef keep : (0 A : Type 0) -> (0 x : A) -> (b : Pair A x x) -> Nat := fun (0 A : Type 0) => fun (0 x : A) => fun (b : Pair A x x) => case b as value in Pair u v return (let p : Same A u v value := proof A u v value in Nat) with | pair 0 s 0 t => 7\n"

