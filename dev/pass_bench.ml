(** Rung 1 measures the two available frontend passes independently. *)
let timed (operation : unit -> 'a) : 'a * float =
  let start = Unix.gettimeofday () in
  let result = operation () in
  result, (Unix.gettimeofday () -. start) *. 1000.

let () =
  let source = In_channel.input_all stdin in
  let parsed, parse_ms = timed (fun () -> Kanon_surface.Parser.parse source) in
  let checked =
    Result.bind parsed (fun declarations ->
      let result, check_ms =
        timed (fun () ->
          Kanon_surface.Elab.elab_program Kanon_kernel.Global.initial declarations)
      in
      Result.map (fun _rows -> check_ms) result)
  in
  checked
  |> Result.fold
       ~ok:(fun check_ms ->
         Printf.printf "parse %.6f\nelaborate-check %.6f\n" parse_ms check_ms)
       ~error:(fun error ->
         prerr_endline (Kanon_kernel.Error.to_string error); exit 1)
