let route source =
  Assay_emit.Contract.lower source
  |> Result.fold ~ok:(fun (name, same) -> Option.is_none name && same == source)
       ~error:(fun _error -> false)

let () =
  let ordinary = "axiom Core : Prop\n--" ^ String.make 1048576 'x' in
  let identifier = String.make 1048576 'a' in
  let keyword_prefix = "contract" ^ String.make 1048576 'a' in
  let before = Gc.allocated_bytes () in
  let accepted = route ordinary && route identifier && route keyword_prefix in
  let bytes = Gc.allocated_bytes () -. before in
  if accepted && bytes < 131072. then
    Printf.printf "CONTRACT-ROUTE core=3 identity=true allocated_bytes=%.0f bound=131072 OK\n" bytes
  else (Printf.eprintf "CONTRACT-ROUTE FAIL identity=%b allocated_bytes=%.0f\n" accepted bytes; exit 1)
