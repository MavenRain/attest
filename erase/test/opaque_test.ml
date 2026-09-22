open Kanon_kernel

let ( let* ) = Result.bind

let checked (name : string) :
    (Global.t * (string * Global.entry) list, string) result =
  let* source = Sys_io.read_file ("fixtures/erasure/" ^ name ^ ".att") in
  Kanon_surface.Elab.check_in Global.initial source |> Result.map_error Error.to_string

let require (label : string) (condition : bool) : (unit, string) result =
  if condition then Ok () else Error label

let guarded (name : string) : (unit, string) result =
  let* globals, rows = checked name in
  let* opaque, sealed =
    Attest_erase.Opaque.prepare globals rows |> Result.map_error Error.to_string
  in
  let* () = require "source proof missing" (Option.is_some (Global.find_def "proof" globals)) in
  let* () = require "proof body retained" (Option.is_some (Global.find_axiom "proof" opaque)) in
  let* () = require "runtime type was sealed" (Option.is_some (Global.find_def "Layout" opaque)) in
  let* () = require "family table lost" (Option.is_some (Global.find_family "Equal" opaque)) in
  let* () = require "declaration rows lost" (List.length rows = List.length sealed) in
  let* proof = Eval.eval_global opaque "proof" |> Result.map_error Error.to_string in
  let* normal = Eval.whnf opaque proof |> Result.map_error Error.to_string in
  let* () = require "opaque evaluator unfolded proof"
      (Value.as_neutral normal = Some (Value.HGlobal "proof", [])) in
  let* from_scope, _empty =
    Attest_erase.Opaque.prepare globals [] |> Result.map_error Error.to_string
  in
  require "inherited proof retained" (Option.is_some (Global.find_axiom "proof" from_scope))

let runtime_preserved () : (unit, string) result =
  let* globals, rows =
    Kanon_surface.Elab.check_in Global.initial "def value : Nat := 7"
    |> Result.map_error Error.to_string
  in
  let* opaque, _rows =
    Attest_erase.Opaque.prepare globals rows |> Result.map_error Error.to_string
  in
  let* before = Eval.eval_global globals "value" |> Result.map_error Error.to_string in
  let* after = Eval.eval_global opaque "value" |> Result.map_error Error.to_string in
  require "runtime computation changed" (before = after)

let classification_failure () : (unit, string) result =
  let* globals, rows = checked "f2-a" in
  let* definition = Global.find_def "proof" globals
    |> Option.to_result ~none:"missing proof" in
  let bad = Global.Def { definition with Global.ty = Term.Global "missing_type" } in
  let globals = Global.add "proof" bad globals in
  Attest_erase.Opaque.prepare globals rows
  |> Result.fold ~ok:(fun _prepared -> Error "classification error was swallowed")
       ~error:(fun _reason -> Ok ())

let no_body_evaluation () : (unit, string) result =
  let* globals, _rows = checked "f2-a" in
  let* definition = Global.find_def "proof" globals
    |> Option.to_result ~none:"missing proof" in
  let trap = Global.Def { definition with Global.def = Term.Global "missing_body" } in
  (* Isolate the proof and its family from types depending on the poisoned body. *)
  let globals = { globals with Global.entries = Global.initial.Global.entries } in
  let globals = Global.add "proof" trap globals in
  let* opaque, _rows =
    Attest_erase.Opaque.prepare globals [ ("proof", trap) ]
    |> Result.map_error Error.to_string
  in
  let* value = Eval.eval_global opaque "proof" |> Result.map_error Error.to_string in
  require "proof body evaluated" (Value.as_neutral value = Some (Value.HGlobal "proof", []))

let () =
  let cases =
    [ ("global", fun () -> guarded "f2-a");
      ("alias", fun () -> guarded "proof-alias");
      ("function", fun () -> guarded "proof-function");
      ("runtime", runtime_preserved);
      ("classification", classification_failure);
      ("body", no_body_evaluation) ]
  in
  let results = List.map (fun (name, run) -> (name, run ())) cases in
  let failures = List.filter_map
      (fun (name, result) -> Result.fold ~ok:(fun () -> None)
          ~error:(fun message -> Some (name ^ ": " ^ message)) result) results in
  List.iter prerr_endline failures;
  Printf.printf "OPAQUE-ERASE pass=%d fail=%d\n"
    (List.length cases - List.length failures) (List.length failures);
  exit (if List.is_empty failures then 0 else 1)
