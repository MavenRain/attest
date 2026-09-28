import Base

def Fixture.motive_annotation_dependent() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef MakeInput : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 A : Type 0) -> sum (A, A)\ndef Input : Type 1 := (MakeInput Nat : Type 1)\naxiom input : Input\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_annotation_dependent_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef MakeInput : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 A : Type 0) -> sum (A, A)\ndef Input : Type 1 := (MakeInput Nat : Type 1)\naxiom input : Input\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_annotation_curried() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef MakeInput : (0 N : Type 0) -> (0 M : Type 0) -> Type 0 := fun (0 N : Type 0) (0 M : Type 0) => N -> M -> sum (M, M)\ndef Input : Type 0 := ((MakeInput Nat : (0 M : Type 0) -> Type 0) Nat : Type 0)\naxiom input : Input\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_annotation_curried_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef MakeInput : (0 N : Type 0) -> (0 M : Type 0) -> Type 0 := fun (0 N : Type 0) (0 M : Type 0) => N -> M -> sum (M, M)\ndef Input : Type 0 := ((MakeInput Nat : (0 M : Type 0) -> Type 0) Nat : Type 0)\naxiom input : Input\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := proof self in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_beta_dependent() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef MakeInput : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 A : Type 0) -> sum (A, A)\ndef Input : Type 1 := MakeInput Nat\naxiom input : Input\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_beta_dependent_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef MakeInput : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 A : Type 0) -> sum (A, A)\ndef Input : Type 1 := MakeInput Nat\naxiom input : Input\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_beta_curried() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef MakeInput : (0 N : Type 0) -> (0 M : Type 0) -> Type 0 := fun (0 N : Type 0) (0 M : Type 0) => N -> M -> sum (M, M)\ndef Input : Type 0 := MakeInput Nat Nat\naxiom input : Input\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_beta_curried_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef MakeInput : (0 N : Type 0) -> (0 M : Type 0) -> Type 0 := fun (0 N : Type 0) (0 M : Type 0) => N -> M -> sum (M, M)\ndef Input : Type 0 := MakeInput Nat Nat\naxiom input : Input\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := proof self in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"


def Fixture.motive_let_dependent() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef Input : Type 1 := let T : Type 1 := (0 A : Type 0) -> sum (A, A) in T\naxiom input : Input\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_let_dependent_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef Input : Type 1 := let T : Type 1 := (0 A : Type 0) -> sum (A, A) in T\naxiom input : Input\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_let_curried() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef Output : Type 0 := let N : Type 0 := Nat in N -> sum (N, N)\ndef Input : Type 0 := let T : Type 0 := Nat -> Output in T\naxiom input : Input\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_let_curried_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef Output : Type 0 := let N : Type 0 := Nat in N -> sum (N, N)\ndef Input : Type 0 := let T : Type 0 := Nat -> Output in T\naxiom input : Input\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := proof self in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_application_global() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom input : Nat -> sum (Nat, Nat)\n\ndef keep : Nat := case (input 3) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_application_global_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom input : Nat -> sum (Nat, Nat)\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (input 3) as self return (let p : Same self := proof self in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_application_dependent() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom input : (0 A : Type 0) -> sum (A, A)\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_application_dependent_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom input : (0 A : Type 0) -> sum (A, A)\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_application_local() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (f : Nat -> sum (A, A)) -> Nat := fun (0 A : Type 0) => fun (f : Nat -> sum (A, A)) => case (f 3) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_application_local_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (f : Nat -> sum (A, A)) -> Nat := fun (0 A : Type 0) => fun (f : Nat -> sum (A, A)) => case (f 3) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_application_curried() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom input : (0 A : Type 0) -> A -> sum (A, A)\n\ndef keep : (0 A : Type 0) -> (x : A) -> Nat := fun (0 A : Type 0) => fun (x : A) => case (input A x) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_application_curried_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom input : (0 A : Type 0) -> A -> sum (A, A)\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (x : A) -> Nat := fun (0 A : Type 0) => fun (x : A) => case (input A x) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_plain_annotated() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (inj 0 of 2 7 : sum (Nat, Nat)) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_annotated_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (inj 0 of 2 7 : sum (Nat, Nat)) as self return (let p : Same self := proof self in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_dependent() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (v : sum (A, A)) -> Nat := fun (0 A : Type 0) => fun (v : sum (A, A)) => case v as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (x : A) => 7 | 1 (y : A) => 8\n"

def Fixture.motive_plain_dependent_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (v : sum (A, A)) -> Nat := fun (0 A : Type 0) => fun (v : sum (A, A)) => case v as self return (let p : Same A self := proof A self in Nat) with | 0 (x : A) => 7 | 1 (y : A) => 8\n"

def Fixture.motive_plain_global() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom input : sum (Nat, Nat)\n\ndef keep : Nat := case input as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_global_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom input : sum (Nat, Nat)\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case input as self return (let p : Same self := proof self in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_let() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := let v : sum (Nat, Nat) := inj 1 of 2 8 in case v as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_let_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := let v : sum (Nat, Nat) := inj 1 of 2 8 in case v as self return (let p : Same self := proof self in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_local() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : (v : sum (Nat, Nat)) -> Nat := fun (v : sum (Nat, Nat)) => case v as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

def Fixture.motive_plain_local_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : (v : sum (Nat, Nat)) -> Nat := fun (v : sum (Nat, Nat)) => case v as self return (let p : Same self := proof self in Nat) with | 0 (x : Nat) => 7 | 1 (y : Nat) => 8\n"

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

def Fixture.motive_alias_global() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef Input : Type 0 := Nat -> sum (Nat, Nat)\ndef InputAlias : Type 0 := Input\naxiom input : InputAlias\n\ndef keep : Nat := case (input 3) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_alias_global_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef Input : Type 0 := Nat -> sum (Nat, Nat)\ndef InputAlias : Type 0 := Input\naxiom input : InputAlias\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (input 3) as self return (let p : Same self := proof self in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_alias_dependent() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef Input : Type 1 := (0 A : Type 0) -> sum (A, A)\naxiom input : Input\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_alias_dependent_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\ndef Input : Type 1 := (0 A : Type 0) -> sum (A, A)\naxiom input : Input\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> Nat := fun (0 A : Type 0) => case (input A) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_alias_local() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (f : Nat -> sum (A, A)) -> Nat := fun (0 A : Type 0) => fun (f : Nat -> sum (A, A)) => let Input : Type 0 := Nat -> sum (A, A) in let Alias : Type 0 := Input in let g : Alias := f in case (g 3) as self return (let p : Same A self := (same A self : Same A self) in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_alias_local_opaque() -> String:
  "mu Same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Prop with\n| same : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\naxiom proof : (0 A : Type 0) -> (0 value : sum (A, A)) -> Same A value\n\ndef keep : (0 A : Type 0) -> (f : Nat -> sum (A, A)) -> Nat := fun (0 A : Type 0) => fun (f : Nat -> sum (A, A)) => let Input : Type 0 := Nat -> sum (A, A) in let Alias : Type 0 := Input in let g : Alias := f in case (g 3) as self return (let p : Same A self := proof A self in Nat) with | 0 (left : A) => 7 | 1 (right : A) => 8\n"

def Fixture.motive_alias_curried() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef Output : Type 0 := Nat -> sum (Nat, Nat)\ndef Input : Type 0 := Nat -> Output\naxiom input : Input\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := (same self : Same self) in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"

def Fixture.motive_alias_curried_opaque() -> String:
  "mu Same : (0 value : sum (Nat, Nat)) -> Prop with\n| same : (0 value : sum (Nat, Nat)) -> Same value\ndef Output : Type 0 := Nat -> sum (Nat, Nat)\ndef Input : Type 0 := Nat -> Output\naxiom input : Input\naxiom proof : (0 value : sum (Nat, Nat)) -> Same value\n\ndef keep : Nat := case (input 3 4) as self return (let p : Same self := proof self in Nat) with | 0 (left : Nat) => 7 | 1 (right : Nat) => 8\n"
