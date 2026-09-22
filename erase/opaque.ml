open Kanon_kernel

let ( let* ) = Result.bind

(** A global has no explicit quantity field in the carried kernel. Its type
    living in Prop is the checked evidence that the global is a proof. This
    classification belongs to the checking boundary, before erasure starts. *)
let proof_names (budget : Budget.t) (globals : Global.t) :
    (string list, Error.t) result =
  Global.StringMap.bindings globals.Global.entries
  |> List.fold_left
       (fun (result : (string list, Error.t) result)
            ((name : string), (entry : Global.entry)) ->
         let* names = result in
         match entry with
         | Global.Axiom _axiom -> Ok names
         | Global.Prim _primitive -> Ok names
         | Global.Def definition ->
             let* universe =
               Check.infer_univ (Check.make globals budget) definition.Global.ty
             in
             if Level.equal universe Level.zero then Ok (name :: names)
             else Ok names)
       (Ok [])

let seal (names : string list) (name : string) (entry : Global.entry) : Global.entry =
  match entry with
  | Global.Axiom _axiom -> entry
  | Global.Prim _primitive -> entry
  | Global.Def definition ->
      if List.mem name names then
        Global.Axiom { Global.ax_ty = definition.Global.ty }
      else entry

let prepare ?(budget : Budget.t = Budget.unlimited) (globals : Global.t)
    (rows : (string * Global.entry) list) :
    (Global.t * (string * Global.entry) list, Error.t) result =
  let* names = proof_names budget globals in
  let entries = Global.StringMap.mapi (seal names) globals.Global.entries in
  let opaque = { globals with Global.entries } in
  let rows = List.map (fun (name, entry) -> (name, seal names name entry)) rows in
  Ok (opaque, rows)

let program ?(budget : Budget.t = Budget.unlimited) (globals : Global.t)
    (rows : (string * Global.entry) list) :
    ((string * Erase.entry) list, Error.t) result =
  let* opaque, rows = prepare ~budget globals rows in
  Erase.program ~budget opaque rows
