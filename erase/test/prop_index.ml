open Kanon_kernel

(** Stage B's erased Prop indices and their retained rejection boundaries. *)

type expected = Accept | Refuse of string

let cases : (string * string * expected) list =
  [
    ("nat-index",
     "mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> At n\n\
      def witness : At 4 := at 4",
     Accept);
    ("high-universe-index",
     "mu At : (0 A : Type 1) -> Prop with\n\
      | at : (0 A : Type 1) -> At A\n\
      def witness : At (Type 0) := at (Type 0)",
     Accept);
    ("dependent-indices",
     "mu At : (0 A : Type 0) -> (0 x : A) -> Prop with\n\
      | at : (0 A : Type 0) -> (0 x : A) -> At A x\n\
      def witness : At Nat 4 := at Nat 4",
     Accept);
    ("reordered-indices",
     "mu At : (0 n : Nat) -> (0 m : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> (0 m : Nat) -> At m n\n\
      def witness : At 3 4 := at 4 3",
     Accept);
    ("annotated-index",
     "mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> At (n : Nat)\n\
      def witness : At 4 := at 4",
     Accept);
    ("accessibility-family",
     "axiom R : Nat -> Nat -> Prop\n\
      mu Acc : (0 x : Nat) -> Prop with\n\
      | intro : (0 x : Nat) -> (0 next : (0 y : Nat) -> R y x -> Acc y) -> Acc x\n\
      axiom next : (0 y : Nat) -> R y 0 -> Acc y\n\
      def accessible : Acc 0 := intro 0 next",
     Accept);
    ("indexed-singleton-elimination",
     "mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At n\n\
      def step : (p : At 4) -> Nat := fun (p : At 4) =>\n\
      case p as q in At n return Nat with | at 0 n => 0",
     Accept);
    ("erased-index-read",
     "mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At n\n\
      def step : (p : At 4) -> Nat := fun (p : At 4) =>\n\
      case p as q in At n return Nat with | at 0 n => n",
     Refuse "quantity: the erased binder n is read in a runtime position");
    ("annotated-index-type",
     "mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At (n : Type 0)",
     Refuse "mismatch: the term has type Nat and the expected type is Type 1");
    ("result-index-type",
     "mu At : (0 A : Type 0) -> Prop with | at : (0 n : Nat) -> At n",
     Refuse "mismatch: the term has type Nat and the expected type is Type 1");
    ("runtime-index",
     "mu At : (n : Nat) -> Prop with | at : At 0",
     Refuse "index not zero:");
    ("type-index-bound",
     "mu At : (0 A : Type 0) -> Type 0 with | at : At Nat",
     Refuse "index above universe:");
    ("type-field-bound",
     "mu Box : Type 0 with | box : (0 A : Type 0) -> Box",
     Refuse "universe: a field of box exceeds its family universe");
    ("unindexed-proof-field",
     "mu Box : Prop with | box : (0 n : Nat) -> Box",
     Refuse "universe: a field of box exceeds its family universe");
    ("runtime-proof-field",
     "mu At : (0 n : Nat) -> Prop with | at : (n : Nat) -> At n",
     Refuse "universe: a field of at exceeds its family universe");
    ("constant-result-index",
     "mu At : (0 n : Nat) -> Prop with | at : (0 n : Nat) -> At 0",
     Refuse "universe: a field of at exceeds its family universe");
    ("computed-result-index",
     "mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> At (let m : Nat := n in m)",
     Refuse "universe: a field of at exceeds its family universe");
    ("unindexed-first-field",
     "mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 hidden : Nat) -> (0 n : Nat) -> At n",
     Refuse "universe: a field of at exceeds its family universe");
    ("unindexed-last-field",
     "mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> (0 hidden : Nat) -> At n",
     Refuse "universe: a field of at exceeds its family universe");
    ("ill-typed-index",
     "mu At : (0 n : 0) -> Prop with | at : At 0",
     Refuse "universe: a term used as a type is not a universe");
    ("index-twice",
     "mu At : (0 n : Nat) -> (0 m : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> At n n",
     Accept);
    ("index-in-later-field",
     "axiom P : Nat -> Prop\n\
      mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> (0 p : P n) -> At n",
     Accept);
    ("prop-typed-index",
     "axiom P : Prop\n\
      mu At : (0 p : P) -> Prop with\n\
      | at : (0 p : P) -> At p",
     Accept);
    ("parameter-index",
     "mu At (0 A : Type 0) : (0 x : A) -> Prop with\n\
      | at : (0 x : A) -> At A x",
     Accept);
    ("computed-application-index",
     "axiom f : Nat -> Nat\n\
      mu At : (0 n : Nat) -> Prop with\n\
      | at : (0 n : Nat) -> At (f n)",
     Refuse "universe: a field of at exceeds its family universe");
    ("type-1-index-bound",
     "mu At : (0 A : Type 1) -> Type 1 with | at : At Nat",
     Refuse "index above universe: the index A of At lives at 3 and At is declared at 2");
    ("parameter-hidden-field",
     "mu At (0 A : Type 0) : (0 x : A) -> Prop with\n\
      | at : (0 hidden : A) -> (0 x : A) -> At A x",
     Refuse "universe: a field of at exceeds its family universe");
    ("recursive-big-later-field",
     "axiom R : Nat -> Nat -> Prop\n\
      mu Acc : (0 x : Nat) -> Prop with\n\
      | intro : (0 x : Nat) -> (0 next : (0 y : Nat) -> R y x -> Acc y) -> (0 big : Nat) -> Acc x",
     Refuse "universe: a field of intro exceeds its family universe");
  ]

let run ((name, source, expected) : string * string * expected) : bool =
  let result = Kanon_surface.Elab.check_in Global.initial source in
  let passed, detail =
    match expected with
    | Accept ->
        Result.fold
          ~ok:(fun _checked -> (true, "accepted"))
          ~error:(fun error -> (false, Error.to_string error))
          result
    | Refuse prefix ->
        Result.fold
          ~ok:(fun _checked -> (false, "unexpected acceptance"))
          ~error:(fun error ->
            let detail = Error.to_string error in
            (String.starts_with ~prefix detail, detail))
          result
  in
  Printf.printf "PROP-INDEX row=%s %s %s\n" name
    (if passed then "OK" else "FAIL") detail;
  passed

let () =
  let results = List.map run cases in
  let passed = List.length (List.filter Fun.id results) in
  let total = List.length cases in
  Printf.printf "PROP-INDEX pass=%d total=%d %s\n" passed total
    (if Int.equal passed total then "OK" else "FAIL");
  if not (Int.equal passed total) then exit 1
