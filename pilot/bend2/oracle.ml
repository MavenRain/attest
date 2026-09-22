open Kanon_kernel

let ( let* ) = Result.bind

let evaluate (path : string) : (unit, string) result =
  let* source = Sys_io.read_file path in
  let* globals, rows =
    Kanon_surface.Elab.check_in Global.initial source |> Result.map_error Error.to_string
  in
  List.fold_left
    (fun result (name, entry) ->
      let* () = result in
      match entry with
      | Global.Axiom _axiom -> Error "oracle input contains a postulate"
      | Global.Prim _primitive -> Error "oracle input contains a primitive declaration"
      | Global.Def definition ->
          let* value = Eval.eval globals [] definition.Global.def |> Result.map_error Error.to_string in
          let* term = Eval.quote globals 0 value |> Result.map_error Error.to_string in
          Printf.printf "%s %s\n" name (Pp.term [] term);
          Ok ())
    (Ok ()) rows

let () =
  let result =
    match Array.to_list Sys.argv with
    | [ _program; path ] -> evaluate path
    | [] | [ _ ] | _ :: _ :: _ :: _ -> Error "usage: oracle FILE.att"
  in
  exit (Result.fold ~ok:(fun () -> 0) ~error:(fun message -> prerr_endline message; 1) result)
