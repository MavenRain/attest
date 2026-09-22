(** Checking and erasure, sharing the carried total I/O boundary. *)

type error =
  | Arguments of string list
  | Input of string * string
  | Check of string * Kanon_kernel.Error.t
  | Erase of string * Kanon_kernel.Error.t
  | Counts

type display = Summary | Checked_form | Axioms
type command = Spec_count | Check_file of display * string | Erase_file of string

let usage : string =
  "usage: attest check [--print|--axioms] FILE.att | attest build --erase FILE.att | attest spec-count"

let parse (args : string list) : (command, error) result =
  match args with
  | [ "spec-count" ] -> Ok Spec_count
  | [ "check"; path ] -> Ok (Check_file (Summary, path))
  | [ "check"; "--print"; path ] -> Ok (Check_file (Checked_form, path))
  | [ "check"; "--axioms"; path ] -> Ok (Check_file (Axioms, path))
  | [ "build"; "--erase"; path ] -> Ok (Erase_file path)
  | other -> Error (Arguments other)

let read_file (path : string) : (string, error) result =
  if not (List.exists (Filename.check_suffix path) [ ".att"; ".kan" ]) then
    Error (Input (path, "expected a .att or inherited .kan source"))
  else
    Sys_io.read_file path |> Result.map_error (fun message -> Input (path, message))

let definitions (rows : (string * Kanon_kernel.Global.entry) list) : int =
  List.fold_left
    (fun count ((_name : string), (entry : Kanon_kernel.Global.entry)) ->
      match entry with
      | Kanon_kernel.Global.Def _definition -> count + 1
      | Kanon_kernel.Global.Axiom _axiom -> count
      | Kanon_kernel.Global.Prim _primitive -> count)
    0 rows

let display (mode : display) (path : string)
    (rows : (string * Kanon_kernel.Global.entry) list) : unit =
  match mode with
  | Summary -> Printf.printf "CHECK %s defs=%d ok\n" path (definitions rows)
  | Checked_form ->
      print_string (Kanon_surface.Elab.checked_form rows);
      Printf.printf "CHECK %s defs=%d ok\n" path (definitions rows)
  | Axioms ->
      let names = Kanon_surface.Elab.axiom_names rows in
      List.iter (Printf.printf "AXIOM %s\n") names;
      Printf.printf "AXIOMS %s count=%d\n" path (List.length names)

let run (cmd : command) : (unit, error) result =
  match cmd with
  | Spec_count ->
      print_string (Kanon_kernel.Spec_count.print ());
      if Int.equal (List.length Kanon_kernel.Term.formers) 2
         && Int.equal (List.length Kanon_kernel.Shape.declared) 5
      then Ok ()
      else Error Counts
  | Check_file (mode, path) ->
      Result.bind (read_file path) (fun source ->
        Kanon_surface.Elab.check_text Kanon_kernel.Global.initial source
        |> Result.map_error (fun error -> Check (path, error)))
      |> Result.map (display mode path)
  | Erase_file path ->
      Result.bind (read_file path) (fun source ->
        Kanon_surface.Elab.check_in Kanon_kernel.Global.initial source
        |> Result.map_error (fun error -> Check (path, error)))
      |> Fun.flip Result.bind (fun (globals, rows) ->
             Attest_erase.Opaque.program globals rows
             |> Result.map_error (fun error -> Erase (path, error)))
      |> Result.map (fun rows -> print_string (Kanon_kernel.Erase.print rows))

let report (error : error) : int =
  match error with
  | Arguments _args -> prerr_endline usage; 64
  | Input (path, message) ->
      Printf.eprintf "attest: check: %s: %s\n" path message; 64
  | Check (path, error) ->
      let message = Kanon_kernel.Error.to_string error in
      Printf.printf "CHECK %s FAIL %s\n" path message;
      Printf.eprintf "attest: check: %s\n" message; 1
  | Erase (path, error) ->
      let message = Kanon_kernel.Error.to_string error in
      Printf.eprintf "attest: erase: %s: %s\n" path message; 2
  | Counts -> prerr_endline "attest: spec-count: expected two formers and five shapes"; 1

let () =
  let args =
    match Array.to_list Sys.argv with
    | [] -> []
    | _program :: rest -> rest
  in
  let result = Result.bind (parse args) run in
  exit (Result.fold ~ok:(fun () -> 0) ~error:report result)
