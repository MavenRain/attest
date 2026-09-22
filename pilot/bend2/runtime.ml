let seed : int =
  match Array.to_list Sys.argv with
  | [] | [ _ ] -> 7
  | _program :: value :: _rest ->
      int_of_string_opt value
      |> Option.fold ~none:0 ~some:(fun n -> if n >= 0 && n <= 0xffffffff then n else 0)

let () =
  let answer = Model.batch 2500 24 seed { Model.checksum = 0; failures = 0 } in
  Printf.printf "%d %d\n" answer.Model.checksum answer.Model.failures
