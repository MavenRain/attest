(** The pinned eraser is used only to reproduce the F2 regression. *)
let () =
  let result =
    match Array.to_list Sys.argv with
    | [ _program; path ] ->
        Result.bind (Sys_io.read_file path) (fun source ->
          Kanon_surface.Elab.check_in Kanon_kernel.Global.initial source
          |> Result.map_error Kanon_kernel.Error.to_string)
        |> Fun.flip Result.bind (fun (globals, rows) ->
               Kanon_kernel.Erase.program globals rows
               |> Result.map_error Kanon_kernel.Error.to_string)
        |> Result.map (fun rows -> print_string (Kanon_kernel.Erase.print rows))
    | [] | [ _ ] | _ :: _ :: _ :: _ -> Error "usage: erase_probe FILE"
  in
  exit (Result.fold ~ok:(fun () -> 0)
          ~error:(fun message -> prerr_endline message; 1) result)
