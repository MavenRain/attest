open Kanon_kernel

let ( let* ) = Result.bind
let explain result = Result.map_error Error.to_string result
let require message condition = if condition then Ok () else Error message
let checked source = Kanon_surface.Elab.check_in Global.initial source |> explain
let prefix = "__attest_inline_proof_"
let postulate index = prefix ^ string_of_int index

let fixture name =
  let* source = Sys_io.read_file ("fixtures/erasure/" ^ name ^ ".att") in
  checked source

let is_axiom entry =
  Option.fold ~none:false
    ~some:(fun entry ->
      match entry with
      | Global.Axiom _ -> true
      | Global.Def _ | Global.Prim _ -> false) entry

(* The declaration notices name erased rows; the runtime program follows. *)
let runtime_lines rows =
  Erase.print rows |> String.split_on_char '\n'
  |> List.filter (fun line -> not (String.starts_with ~prefix:"erased " line))

let neutral_layout globals =
  let* value = Eval.eval_global globals "Layout" |> explain in
  let* value = Eval.whnf globals value |> explain in
  require "inline proof selected a layout" (Option.is_some (Value.as_neutral value))

let inherited () =
  let* globals, _rows = fixture "let-proof" in
  let* prepared, rows = Attest_erase.Opaque.prepare globals [] |> explain in
  let* () = require "internal declarations escaped" (List.is_empty rows) in
  neutral_layout prepared

let poisoned name =
  let* globals, _rows = fixture name in
  let* layout = Global.find_def "Layout" globals |> Option.to_result ~none:"missing Layout" in
  let* body =
    match layout.Global.def with
    | Term.Let (x, ty, _proof, body) ->
        Ok (Term.Let (x, ty, Term.Global "missing_inline_body", body))
    | Term.Elim e ->
        (match e.Term.e_scrut with
         | Term.Ann (_proof, ty) ->
             Ok (Term.Elim { e with Term.e_scrut =
                   Term.Ann (Term.Global "missing_inline_body", ty) })
         | Term.Var _ | Term.Univ _ | Term.Lan _ | Term.Ran _ | Term.In _
         | Term.Elim _ | Term.Sec _ | Term.Out _ | Term.Let _ | Term.Global _
         | Term.Lit _ | Term.Auto -> Error "fixture lost its annotated scrutinee")
    | Term.Var _ | Term.Univ _ | Term.Lan _ | Term.Ran _ | Term.In _
    | Term.Sec _ | Term.Out _ | Term.Ann _ | Term.Global _ | Term.Lit _ | Term.Auto ->
        Error "fixture lost its inline proof"
  in
  let entry = Global.Def { layout with Global.def = body } in
  (* Keep classification independent of types that unfold the poisoned layout. *)
  let globals = { globals with Global.entries = Global.StringMap.remove "keep" globals.Global.entries } in
  let globals = Global.add "Layout" entry globals in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals [ ("Layout", entry) ] |> explain in
  neutral_layout prepared

let collision () =
  let* globals, rows = fixture "scrutinee-proof" in
  let name = postulate 0 in
  let entry = Global.Axiom { Global.ax_ty = Prim.nat_ty } in
  let globals = Global.add name entry globals in
  let* prepared, rewritten = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = require "fresh proof shadowed an existing name" (Global.find name prepared = Some entry) in
  let* layout = Global.find_def "Layout" prepared |> Option.to_result ~none:"missing Layout" in
  let* () = require "fresh proof referenced an existing name"
      (not (Term.exists_name ~include_families:true [name] layout.Global.def)) in
  let* () = require "declaration rows changed" (List.map fst rows = List.map fst rewritten) in
  neutral_layout prepared

let family_collision () =
  let* globals, rows = fixture "scrutinee-proof" in
  let* family = Global.find_family "Equal" globals |> Option.to_result ~none:"missing Equal" in
  let name = postulate 0 in
  let globals = Global.add_family name { family with Positivity.f_name = name } globals in
  let* prepared, rewritten = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = require "fresh proof collided with a family" (Option.is_none (Global.find name prepared)) in
  let* () = require "fresh proof skipped the next name" (is_axiom (Global.find (postulate 1) prepared)) in
  let* layout = Global.find_def "Layout" prepared |> Option.to_result ~none:"missing Layout" in
  let* () = require "fresh proof referenced a family name"
      (not (Term.exists_name ~include_families:true [name] layout.Global.def)) in
  let* () = require "declaration rows changed" (List.map fst rows = List.map fst rewritten) in
  neutral_layout prepared

let runtime () =
  let* globals, rows = checked "def value : Nat := let n : Nat := 7 in n" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* before = Eval.eval_global globals "value" |> explain in
  let* after = Eval.eval_global prepared "value" |> explain in
  let* () = require "runtime let changed" (before = after) in
  let* before = Erase.program globals rows |> explain in
  let* after = Attest_erase.Opaque.program globals rows |> explain in
  require "runtime output changed" (Erase.print before = Erase.print after)

(* A proof open only through a binder stays inline: no postulate is allocated
   and the runtime program is the carried one. *)
let stays_inline message globals rows =
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* keep = Global.find_def "keep" prepared |> Option.to_result ~none:"missing keep" in
  let* () = require "no postulate leaked" (Option.is_none (Global.find (postulate 0) prepared)) in
  let* () = require "keep is postulate-free"
      (not (Term.exists_name ~include_families:true [ postulate 0 ] keep.Global.def)) in
  let* before = Erase.program globals rows |> explain in
  let* after = Attest_erase.Opaque.program globals rows |> explain in
  require message (Erase.print before = Erase.print after)

let local_type () =
  let* globals, rows = checked
      "mu Equal : Prop with | refl : Equal\n\
       def P : (0 n : Nat) -> Prop := fun (0 n : Nat) => Equal\n\
       def keep : (0 n : Nat) -> Nat -> Nat := fun (0 n : Nat) (x : Nat) =>\n\
         let p : P n := (refl : P n) in x" in
  stays_inline "type-only local escaped its binder" globals rows

let shape_payload () =
  let* globals, rows = fixture "payload-open-proof" in
  stays_inline "payload-open proof escaped its binder" globals rows

let row_consistency () =
  let* globals, rows = fixture "let-proof" in
  let* prepared, rewritten = Attest_erase.Opaque.prepare globals rows |> explain in
  require "stale declaration reinserted"
    (List.for_all (fun (name, entry) -> Global.find name prepared = Some entry) rewritten)

(* The body proof carries binders; the sealed twin postulates it by hand. *)
let same_runtime name =
  let* globals, rows = fixture name in
  let* twin, twin_rows = fixture (name ^ "-opaque") in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = neutral_layout prepared in
  let* body = Attest_erase.Opaque.program globals rows |> explain in
  let* sealed = Attest_erase.Opaque.program twin twin_rows |> explain in
  require (name ^ " runtime differs from its sealed twin") (runtime_lines body = runtime_lines sealed)

let binders () =
  let* () = same_runtime "lambda-proof" in
  same_runtime "binder-proof"

let motive () =
  let* globals, rows = fixture "binder-proof" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* layout = Global.find_def "Layout" prepared |> Option.to_result ~none:"missing Layout" in
  let* name =
    match layout.Global.def with
    | Term.Elim { Term.e_scrut = Term.Global name; _ } when String.starts_with ~prefix name -> Ok name
    | Term.Elim _ | Term.Var _ | Term.Univ _ | Term.Lan _ | Term.Ran _ | Term.In _
    | Term.Sec _ | Term.Out _ | Term.Let _ | Term.Ann _ | Term.Global _ | Term.Lit _ | Term.Auto ->
        Error "motive-bearing proof was not replaced as a whole"
  in
  require "motive-bearing proof lacks its postulate" (is_axiom (Global.find name prepared))

let redeclared () =
  let* globals, rows = fixture "redeclared-proof" in
  let* prepared, rewritten = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = require "declaration rows changed" (List.map fst rows = List.map fst rewritten) in
  let* () = require "row entry differs from its environment"
      (List.for_all (fun (name, entry) -> Global.find name prepared = Some entry) rewritten) in
  neutral_layout prepared

let payload_postulates () =
  let* globals, rows = fixture "duplicate-payload" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* use = Global.find "use" prepared |> Option.to_result ~none:"missing use" in
  let* ty =
    match use with
    | Global.Axiom axiom -> Ok axiom.Global.ax_ty
    | Global.Def _ | Global.Prim _ -> Error "use is not an axiom"
  in
  let indices = List.init 8 Fun.id in
  let present = List.filter (fun i -> is_axiom (Global.find (postulate i) prepared)) indices in
  let referenced =
    List.filter (fun i -> Term.exists_name ~include_families:true [ postulate i ] ty) indices in
  let* () = require "payload postulate orphaned or missing" (present = referenced) in
  require "equal payload proofs do not share one postulate" (present = [ 0 ])

let () =
  let cases = [ ("let-body", fun () -> poisoned "let-proof");
                ("scrutinee-body", fun () -> poisoned "scrutinee-proof");
                ("inherited", inherited); ("name-collision", collision);
                ("family-collision", family_collision); ("runtime", runtime);
                ("local-type", local_type); ("rows", row_consistency);
                ("binders", binders); ("motive", motive); ("shape-payload", shape_payload);
                ("redeclared", redeclared); ("payload-postulates", payload_postulates) ] in
  let failures = List.filter_map (fun (name, run) ->
      Result.fold ~ok:(fun () -> Printf.printf "INLINE-ERASE row=%s OK\n" name; None)
        ~error:(fun reason -> Some ("INLINE-ERASE row=" ^ name ^ " FAIL " ^ reason)) (run ())) cases in
  List.iter prerr_endline failures;
  Printf.printf "INLINE-ERASE pass=%d total=%d %s\n"
    (List.length cases - List.length failures) (List.length cases)
    (if List.is_empty failures then "OK" else "FAIL");
  exit (if List.is_empty failures then 0 else 1)
