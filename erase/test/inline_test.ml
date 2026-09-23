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

(* An indirectly typed lambda has no syntactic telescope for this pass. *)
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
       def Function : Type 0 := (0 n : Nat) -> Nat -> Nat\n\
       def keep : Function := fun (0 n : Nat) (x : Nat) =>\n\
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
  let* globals, rows = fixture "lambda-proof" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* layout = Global.find_def "Layout" prepared |> Option.to_result ~none:"missing Layout" in
  let* () =
    match layout.Global.def with
    | Term.Let (_, _, Term.Global name, _) when String.starts_with ~prefix name -> Ok ()
    | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto
    | Term.Lan _ | Term.Ran _ | Term.In _ | Term.Sec _ | Term.Out _
    | Term.Elim _ | Term.Let _ | Term.Ann _ -> Error "closed proof lambda was not sealed as a whole"
  in
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

let check_postulates prepared =
  let checker = Check.make prepared Budget.unlimited in
  let generated = Global.StringMap.bindings prepared.Global.entries
      |> List.filter (fun (name, _entry) -> String.starts_with ~prefix name) in
  let* () = require "local proof has no postulate" (not (List.is_empty generated)) in
  List.fold_left (fun result (_name, entry) ->
      let* () = result in
      let* () = require "local postulate has a body" (is_axiom (Some entry)) in
      let* universe = Check.infer_univ checker (Global.entry_ty entry) |> explain in
      require "local postulate is not a closed proposition" (Level.equal universe Level.zero))
    (Ok ()) generated

let recheck prepared name =
  let* definition = Global.find_def name prepared |> Option.to_result ~none:("missing " ^ name) in
  let* ty = Eval.eval prepared [] definition.Global.ty |> explain in
  Check.check (Check.make prepared Budget.unlimited) Quantity.One definition.Global.def ty |> explain

type host = Host_def of string | Host_axiom of string

(* Every host that holds a rewritten local proof is checked again. *)
let recheck_host prepared host =
  match host with
  | Host_def name -> recheck prepared name
  | Host_axiom name ->
      let* axiom = Global.find_axiom name prepared |> Option.to_result ~none:("missing " ^ name) in
      let* _universe = Check.infer_univ (Check.make prepared Budget.unlimited)
          axiom.Global.ax_ty |> explain in
      Ok ()

let local_runtime hosts name =
  let* globals, rows = fixture name in
  let* twin, twin_rows = fixture (name ^ "-opaque") in
  let* prepared, rewritten = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = check_postulates prepared in
  let* () = require "local declaration rows differ"
      (List.for_all (fun (name, entry) -> Global.find name prepared = Some entry) rewritten) in
  let* () = recheck prepared "keep" in
  let* () = List.fold_left (fun result host ->
      let* () = result in
      recheck_host prepared host) (Ok ()) hosts in
  let* body = Attest_erase.Opaque.program globals rows |> explain in
  let* sealed = Attest_erase.Opaque.program twin twin_rows |> explain in
  require (name ^ " runtime differs from its sealed twin") (runtime_lines body = runtime_lines sealed)

let local_dependent () =
  let* () = local_runtime [ Host_def "Layout" ] "local-dependent" in
  let* globals, rows = fixture "local-dependent" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  recheck prepared "Layout"

let local_inherited () =
  let* globals, _rows = fixture "local-dependent" in
  let* prepared, rows = Attest_erase.Opaque.prepare globals [] |> explain in
  let* () = require "local postulates escaped into declaration rows" (List.is_empty rows) in
  let* () = check_postulates prepared in
  recheck prepared "Layout"

let local_poison () =
  let* globals, _rows = fixture "local-dependent" in
  let* layout = Global.find_def "Layout" globals |> Option.to_result ~none:"missing Layout" in
  let rec poison = function
    | Term.Sec (s, [ leg ]) ->
        let* body = poison leg.Term.l_body in
        Ok (Term.Sec (s, [ { leg with Term.l_body = body } ]))
    | Term.Elim e ->
        (match e.Term.e_scrut with
         | Term.Ann (_body, ty) ->
             Ok (Term.Elim { e with Term.e_scrut = Term.Ann (Term.Global "missing_local_body", ty) })
         | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto
         | Term.Lan _ | Term.Ran _ | Term.In _ | Term.Sec _ | Term.Out _
         | Term.Elim _ | Term.Let _ -> Error "local proof lost its annotation")
    | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto
    | Term.Lan _ | Term.Ran _ | Term.In _ | Term.Sec _ | Term.Out _
    | Term.Let _ | Term.Ann _ -> Error "local fixture lost its proof"
  in
  let* body = poison layout.Global.def in
  let entry = Global.Def { layout with Global.def = body } in
  let globals = { globals with Global.entries = Global.StringMap.remove "keep" globals.Global.entries } in
  let globals = Global.add "Layout" entry globals in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals [ ("Layout", entry) ] |> explain in
  let* () = check_postulates prepared in
  recheck prepared "Layout"

let local_universe () =
  let* globals, rows = checked
      "def U : Type 0 := prod ()\n\
       mu Equal : (0 x : U) -> Prop with | refl : (0 x : U) -> Equal x\n\
       def keep : (x : U) -> U := fun (x : U) => let p : Equal x := (refl x : Equal x) in x" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = check_postulates prepared in
  let* axiom = Global.find_axiom (postulate 0) prepared |> Option.to_result ~none:"missing local postulate" in
  let* () = require "local domain lost its declared universe"
      (Term.exists_name ~include_families:false [ "U" ] axiom.Global.ax_ty) in
  (* The postulate must seal the local proof, not the runtime body of keep. *)
  let* () = require "local postulate does not state the local proof"
      (Term.exists_name ~include_families:true [ "Equal" ] axiom.Global.ax_ty) in
  recheck prepared "keep"

(* A local proof type and a later let type reduce a proof let by a large
   elimination. The proof let keeps its value, the later let still checks,
   and the local proof is sealed over the let definition. *)
let local_proof_let () =
  let* globals, rows = checked
      "mu Equal : (0 A : Type 0) -> (0 x : A) -> Prop with\n\
       | refl : (0 A : Type 0) -> (0 x : A) -> Equal A x\n\
       def Layout : (0 m : Nat) -> Type 0 := fun (0 m : Nat) => let p : Equal Nat m := refl Nat m in \
       let k : (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) := 0 in \
       case (refl (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) 0 : \
       Equal (case p as q in Equal B y return Type 0 with | refl 0 C 0 z => Nat) 0) as r in \
       Equal E w return Type 0 with | refl 0 F 0 u => prod ()\n\
       def keep : (x : Layout 0) -> Layout 0 := fun (x : Layout 0) => x" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* original = Global.find_def "Layout" globals |> Option.to_result ~none:"missing Layout" in
  let* layout = Global.find_def "Layout" prepared |> Option.to_result ~none:"missing Layout" in
  let* () = check_postulates prepared in
  let* () = require "local proof over a proof let was not sealed"
      (layout.Global.def <> original.Global.def) in
  let* () = recheck prepared "Layout" in
  recheck prepared "keep"

let local_payload () =
  let* globals, rows = checked
      "mu Equal : (0 n : Nat) -> Prop with | refl : (0 n : Nat) -> Equal n\n\
       def keep : (0 n : Nat) -> Nat -> Nat := fun (0 n : Nat) (x : Nat) =>\n\
         let p : (0 y : Equal n) -> Equal 0 := (fun (0 y : Equal n) => refl 0) in x" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = check_postulates prepared in
  recheck prepared "keep"

(* A proof with a closed type whose value reads a local hypothesis must keep
   the hypothesis as a parameter: a root postulate would claim Same 0 1. *)
let local_hypothesis () =
  let* globals, rows = checked
      "mu Same : (0 a : Nat) -> (0 b : Nat) -> Prop with | same : (0 a : Nat) -> Same a a\n\
       axiom expected : (0 h : Same 0 1) -> Same 0 1\n\
       def drop : (0 e : Same 0 1) -> Nat := fun (0 e : Same 0 1) => 0\n\
       def g : (0 h : Same 0 1) -> Nat := fun (0 h : Same 0 1) => drop (h : Same 0 1)" in
  let* prepared, _rows = Attest_erase.Opaque.prepare globals rows |> explain in
  let* () = check_postulates prepared in
  let* axiom = Global.find_axiom (postulate 0) prepared
    |> Option.to_result ~none:"missing local postulate" in
  let* expected = Global.find_axiom "expected" prepared |> Option.to_result ~none:"missing expected" in
  let checker = Check.make prepared Budget.unlimited in
  let* sealed = Eval.eval prepared [] axiom.Global.ax_ty |> explain in
  let* wanted = Eval.eval prepared [] expected.Global.ax_ty |> explain in
  let* () = Check.check checker Quantity.Zero (Term.Global "expected") sealed |> explain
    |> Result.map_error (fun reason -> "local hypothesis left the postulate type: " ^ reason) in
  let* () = Check.check checker Quantity.Zero (Term.Global (postulate 0)) wanted |> explain in
  recheck prepared "g"

let branch_scope () =
  let* globals, rows = fixture "branch-local-proof" in
  stays_inline "branch local was confused with an outer binder" globals rows

let () =
  let cases = [ ("let-body", fun () -> poisoned "let-proof");
                ("scrutinee-body", fun () -> poisoned "scrutinee-proof");
                ("inherited", inherited); ("name-collision", collision);
                ("family-collision", family_collision); ("runtime", runtime);
                ("local-type", local_type); ("rows", row_consistency);
                ("binders", binders); ("motive", motive); ("shape-payload", shape_payload);
                ("redeclared", redeclared); ("payload-postulates", payload_postulates);
                ("local-index", fun () -> local_runtime [ Host_def "Layout" ] "local-proof");
                ("local-dependent", local_dependent); ("local-let", fun () -> local_runtime [ Host_def "Layout" ] "local-let");
                ("local-let-alias", fun () -> local_runtime [ Host_def "Layout" ] "local-let-alias");
                ("local-diagram", fun () -> local_runtime [ Host_axiom "Function" ] "local-diagram");
                ("local-inherited", local_inherited); ("local-poison", local_poison);
                ("local-universe", local_universe); ("local-proof-let", local_proof_let);
                ("local-proof-let-value", fun () -> local_runtime [ Host_def "Layout" ] "local-proof-let-value");
                ("local-proof-let-type", fun () -> local_runtime [ Host_def "Layout" ] "local-proof-let-type");
                ("local-proof-let-alias", fun () -> local_runtime [ Host_def "Layout" ] "local-proof-let-alias");
                ("local-proof-let-family", fun () -> local_runtime [ Host_def "Layout" ] "local-proof-let-family");
                ("local-proof-let-universe", fun () -> local_runtime [ Host_def "Layout" ] "local-proof-let-universe");
                ("local-payload", local_payload);
                ("local-runtime-call", fun () -> local_runtime [ Host_def "Layout" ] "local-runtime-call");
                ("local-hypothesis", local_hypothesis);
                ("branch-scope", branch_scope) ] in
  let failures = List.filter_map (fun (name, run) ->
      Result.fold ~ok:(fun () -> Printf.printf "INLINE-ERASE row=%s OK\n" name; None)
        ~error:(fun reason -> Some ("INLINE-ERASE row=" ^ name ^ " FAIL " ^ reason)) (run ())) cases in
  List.iter prerr_endline failures;
  Printf.printf "INLINE-ERASE pass=%d total=%d %s\n"
    (List.length cases - List.length failures) (List.length cases)
    (if List.is_empty failures then "OK" else "FAIL");
  exit (if List.is_empty failures then 0 else 1)
