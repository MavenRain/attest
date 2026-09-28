import Base

def Fixture.lambda_annotation_global() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 n : N) -> Type 0\ndef MakeAlias : (0 N : Type 0) -> Type 1 := MakeFn\ndef Fn : Type 1 := (MakeAlias Nat : Type 1)\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_annotation_global_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom sealed : (0 n : Nat) -> Equal n\ndef MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 n : N) -> Type 0\ndef MakeAlias : (0 N : Type 0) -> Type 1 := MakeFn\ndef Fn : Type 1 := (MakeAlias Nat : Type 1)\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case sealed n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_annotation_dependent() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef MakeFn : (0 A : Type 0) -> Type 1 := fun (0 A : Type 0) => (0 x : A) -> Type 0\ndef Fn : Type 1 := (0 A : Type 0) -> (MakeFn A : Type 1)\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case (refl A x : Equal A x) as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_annotation_dependent_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 x : A) -> Equal A x\ndef MakeFn : (0 A : Type 0) -> Type 1 := fun (0 A : Type 0) => (0 x : A) -> Type 0\ndef Fn : Type 1 := (0 A : Type 0) -> (MakeFn A : Type 1)\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case sealed A x as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_annotation_local() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 y : N) -> Type 0 in let Fn : Type 1 := (MakeFn A : Type 1) in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case (refl A y : Equal A y) as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_annotation_local_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 y : A) -> Equal A y\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 y : N) -> Type 0 in let Fn : Type 1 := (MakeFn A : Type 1) in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case sealed A y as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_annotation_curried() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\ndef MakeFn : (0 N : Type 0) -> (0 M : Type 0) -> Type 1 := fun (0 N : Type 0) (0 M : Type 0) => (0 x : N) -> (0 y : M) -> Type 0\ndef Fn : Type 1 := ((MakeFn Nat : (0 M : Type 0) -> Type 1) Nat : Type 1)\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case (refl x y : Equal x y) as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"

def Fixture.lambda_annotation_curried_opaque() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\naxiom sealed : (0 x : Nat) -> (0 y : Nat) -> Equal x y\ndef MakeFn : (0 N : Type 0) -> (0 M : Type 0) -> Type 1 := fun (0 N : Type 0) (0 M : Type 0) => (0 x : N) -> (0 y : M) -> Type 0\ndef Fn : Type 1 := ((MakeFn Nat : (0 M : Type 0) -> Type 1) Nat : Type 1)\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case sealed x y as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"

def Fixture.lambda_beta_global() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 n : N) -> Type 0\ndef MakeAlias : (0 N : Type 0) -> Type 1 := MakeFn\ndef Fn : Type 1 := MakeAlias Nat\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_beta_global_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom sealed : (0 n : Nat) -> Equal n\ndef MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 n : N) -> Type 0\ndef MakeAlias : (0 N : Type 0) -> Type 1 := MakeFn\ndef Fn : Type 1 := MakeAlias Nat\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case sealed n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_beta_dependent() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef MakeFn : (0 A : Type 0) -> Type 1 := fun (0 A : Type 0) => (0 x : A) -> Type 0\ndef Fn : Type 1 := (0 A : Type 0) -> MakeFn A\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case (refl A x : Equal A x) as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_beta_dependent_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 x : A) -> Equal A x\ndef MakeFn : (0 A : Type 0) -> Type 1 := fun (0 A : Type 0) => (0 x : A) -> Type 0\ndef Fn : Type 1 := (0 A : Type 0) -> MakeFn A\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case sealed A x as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_beta_local() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 y : N) -> Type 0 in let Fn : Type 1 := MakeFn A in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case (refl A y : Equal A y) as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_beta_local_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 y : A) -> Equal A y\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let MakeFn : (0 N : Type 0) -> Type 1 := fun (0 N : Type 0) => (0 y : N) -> Type 0 in let Fn : Type 1 := MakeFn A in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case sealed A y as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_beta_curried() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\ndef MakeFn : (0 N : Type 0) -> (0 M : Type 0) -> Type 1 := fun (0 N : Type 0) (0 M : Type 0) => (0 x : N) -> (0 y : M) -> Type 0\ndef Fn : Type 1 := MakeFn Nat Nat\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case (refl x y : Equal x y) as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"

def Fixture.lambda_beta_curried_opaque() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\naxiom sealed : (0 x : Nat) -> (0 y : Nat) -> Equal x y\ndef MakeFn : (0 N : Type 0) -> (0 M : Type 0) -> Type 1 := fun (0 N : Type 0) (0 M : Type 0) => (0 x : N) -> (0 y : M) -> Type 0\ndef Fn : Type 1 := MakeFn Nat Nat\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case sealed x y as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"


def Fixture.lambda_let_global() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Fn : Type 1 := let T : Type 1 := (0 n : Nat) -> Type 0 in T\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_let_global_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom sealed : (0 n : Nat) -> Equal n\ndef Fn : Type 1 := let T : Type 1 := (0 n : Nat) -> Type 0 in T\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case sealed n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_let_dependent() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Fn : Type 1 := let T : Type 1 := (0 A : Type 0) -> (0 x : A) -> Type 0 in T\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case (refl A x : Equal A x) as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_let_dependent_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 x : A) -> Equal A x\ndef Fn : Type 1 := let T : Type 1 := (0 A : Type 0) -> (0 x : A) -> Type 0 in T\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case sealed A x as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_let_local() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let Fn : Type 1 := let T : Type 1 := (0 y : A) -> Type 0 in let U : Type 1 := T in U in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case (refl A y : Equal A y) as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_let_local_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 y : A) -> Equal A y\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let Fn : Type 1 := let T : Type 1 := (0 y : A) -> Type 0 in let U : Type 1 := T in U in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case sealed A y as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_let_curried() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\ndef Tail : Type 1 := let N : Type 0 := Nat in (0 y : N) -> Type 0\ndef Fn : Type 1 := let T : Type 1 := (0 x : Nat) -> Tail in T\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case (refl x y : Equal x y) as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"

def Fixture.lambda_let_curried_opaque() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\naxiom sealed : (0 x : Nat) -> (0 y : Nat) -> Equal x y\ndef Tail : Type 1 := let N : Type 0 := Nat in (0 y : N) -> Type 0\ndef Fn : Type 1 := let T : Type 1 := (0 x : Nat) -> Tail in T\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case sealed x y as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"

def Fixture.lambda_alias_global() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\ndef Fn : Type 1 := (0 n : Nat) -> Type 0\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case (refl n : Equal n) as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_alias_global_opaque() -> String:
  "mu Equal : (0 n : Nat) -> Prop with\n| refl : (0 n : Nat) -> Equal n\n\naxiom sealed : (0 n : Nat) -> Equal n\ndef Fn : Type 1 := (0 n : Nat) -> Type 0\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 n : Nat) => case sealed n as p in Equal k return Type 0 with | refl 0 j => prod ()\ndef keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x\n"

def Fixture.lambda_alias_dependent() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Fn : Type 1 := (0 A : Type 0) -> (0 x : A) -> Type 0\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case (refl A x : Equal A x) as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_alias_dependent_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 x : A) -> Equal A x\ndef Fn : Type 1 := (0 A : Type 0) -> (0 x : A) -> Type 0\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 A : Type 0) (0 x : A) => case sealed A x as p in Equal B y return Type 0 with | refl 0 C 0 z => prod ()\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_alias_local() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let Fn : Type 1 := (0 y : A) -> Type 0 in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case (refl A y : Equal A y) as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_alias_local_opaque() -> String:
  "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n| refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\naxiom sealed : (0 A : Type 0) -> (0 y : A) -> Equal A y\ndef Layout : (0 A : Type 0) -> (0 x : A) -> Type 0 := fun (0 A : Type 0) (0 x : A) => let Fn : Type 1 := (0 y : A) -> Type 0 in let Alias : Type 1 := Fn in let choose : Alias := fun (0 y : A) => case sealed A y as p in Equal B z return Type 0 with | refl 0 C 0 w => prod () in choose x\ndef keep : (x : Layout Nat 0) -> Layout Nat 0 := fun (x : Layout Nat 0) => x\n"

def Fixture.lambda_alias_curried() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\ndef Tail : Type 1 := (0 y : Nat) -> Type 0\ndef Fn : Type 1 := (0 x : Nat) -> Tail\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case (refl x y : Equal x y) as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"

def Fixture.lambda_alias_curried_opaque() -> String:
  "mu Equal : (0 x : Nat) -> (0 y : Nat) -> Prop with\n| refl : (0 x : Nat) -> (0 y : Nat) -> Equal x y\n\naxiom sealed : (0 x : Nat) -> (0 y : Nat) -> Equal x y\ndef Tail : Type 1 := (0 y : Nat) -> Type 0\ndef Fn : Type 1 := (0 x : Nat) -> Tail\ndef Alias : Type 1 := Fn\ndef Layout : Alias := fun (0 x : Nat) (0 y : Nat) => case sealed x y as p in Equal a b return Type 0 with | refl 0 c 0 d => prod ()\ndef keep : (x : Layout 0 1) -> Layout 0 1 := fun (x : Layout 0 1) => x\n"
