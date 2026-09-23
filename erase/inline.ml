open Kanon_kernel

let ( let* ) = Result.bind

(** Closedness includes type syntax, shape payloads and motives. Runtime
    capture analysis omits those positions and cannot establish this. *)
let rec closed (depth : int) (term : Term.t) : bool =
  let shape s = List.for_all (closed depth) (Shape.payload s) in
  match term with
  | Term.Var ix -> ix >= 0 && ix < depth
  | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto -> true
  | Term.Lan (s, diagram) | Term.Ran (s, diagram) ->
      let binders = if Option.is_some (Shape.point_dom s) then 1 else 0 in
      shape s && closed (depth + binders) diagram
  | Term.In (s, address, args) ->
      shape s && closed_addr depth address && List.for_all (closed depth) args
  | Term.Out (s, address, head) ->
      shape s && closed_addr depth address && closed depth head
  | Term.Sec (s, legs) -> shape s && List.for_all (closed_leg depth) legs
  | Term.Elim e ->
      shape e.Term.e_shape && closed depth e.Term.e_scrut
      && Option.fold ~none:true
           ~some:(fun (m : Term.motive) ->
             closed (depth + List.length m.Term.m_idx + 1) m.Term.m_body)
           e.Term.e_motive
      && List.for_all
           (fun (address, leg) -> closed_addr depth address && closed_leg depth leg)
           e.Term.e_branches
  | Term.Let (_, ty, value, body) ->
      closed depth ty && closed depth value && closed (depth + 1) body
  | Term.Ann (value, ty) -> closed depth value && closed depth ty

and closed_addr (depth : int) (address : Term.addr) : bool =
  match address with
  | Term.APt (_, term) -> closed depth term
  | Term.ALeg _ | Term.ACtor _ -> true

and closed_leg (depth : int) (leg : Term.leg) : bool =
  closed (depth + List.length leg.Term.l_binders) leg.Term.l_body

type state = { globals : Global.t; next : int }

let rec map (f : state -> 'a -> ('b * state, Error.t) result) (state : state)
    (items : 'a list) : ('b list * state, Error.t) result =
  match items with
  | [] -> Ok ([], state)
  | item :: rest ->
      let* item, state = f state item in
      let* rest, state = map f state rest in
      Ok (item :: rest, state)

(** Classification reads the original checked environment. A known closed
    type is sufficient: the proof body need not be inspected again. Terms
    requiring an expected type are left to their annotated parent. *)
let proof_type (checker : Check.ctx) (expected : Term.t option) (term : Term.t) :
    (Term.t option, Error.t) result =
  if not (closed 0 term) then Ok None
  else
    let infer () =
      match term with
      | Term.Ann (_, ty) -> Ok (Some ty)
      | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto
      | Term.Lan _ | Term.Ran _ -> Ok None
      | Term.In _ | Term.Sec _ | Term.Out _ | Term.Elim _ | Term.Let _ ->
          Check.infer checker Quantity.Zero term
          |> Result.fold
               ~ok:(fun ty -> Result.map Option.some (Eval.quote checker.Check.globals 0 ty))
               ~error:(fun reason ->
                 match reason with
                 | Error.Cannot_infer _ -> Ok None
                 | Error.Not_yet _ | Error.Parse _ | Error.Carry _ | Error.Unbound _
                 | Error.Mismatch _ | Error.Universe _ | Error.Quantity _
                 | Error.Wrong_leg _ | Error.Missing_branch _ | Error.Overflow _
                 | Error.Budget_exhausted _ | Error.Index_not_zero _
                 | Error.Index_above_universe _ | Error.Termination _ -> Error reason)
    in
    let* ty = Option.fold ~none:infer ~some:(fun ty () -> Ok (Some ty))
        (Option.bind expected (fun ty -> if closed 0 ty then Some ty else None)) () in
    Option.fold ~none:(Ok None)
      ~some:(fun ty ->
        let* level = Check.infer_univ checker ty in
        Ok (if Level.equal level Level.zero then Some ty else None)) ty

let rec fresh (state : state) : string * state =
  let name = "__attest_inline_proof_" ^ string_of_int state.next in
  let state = { state with next = state.next + 1 } in
  if Option.is_some (Global.find name state.globals)
     || Option.is_some (Global.find_family name state.globals)
  then fresh state
  else (name, state)

let rec term (checker : Check.ctx) (state : state) (expected : Term.t option)
    (value : Term.t) : (Term.t * state, Error.t) result =
  let* proof = proof_type checker expected value in
  Option.fold ~none:(fun () -> node checker state value)
    ~some:(fun ty () ->
      let* ty, state = term checker state None ty in
      let name, state = fresh state in
      let globals = Global.add name (Global.Axiom { Global.ax_ty = ty }) state.globals in
      Ok (Term.Global name, { state with globals })) proof ()

and node (checker : Check.ctx) (state : state) (value : Term.t) :
    (Term.t * state, Error.t) result =
  let walk state value = term checker state None value in
  match value with
  | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto -> Ok (value, state)
  | Term.Lan (s, diagram) ->
      let* s, state = shape checker state s in
      let* diagram, state = walk state diagram in
      Ok (Term.Lan (s, diagram), state)
  | Term.Ran (s, diagram) ->
      let* s, state = shape checker state s in
      let* diagram, state = walk state diagram in
      Ok (Term.Ran (s, diagram), state)
  | Term.In (s, a, args) ->
      let* s, state = shape checker state s in
      let* a, state = address checker state a in
      let* args, state = map walk state args in
      Ok (Term.In (s, a, args), state)
  | Term.Out (s, a, head) ->
      let* s, state = shape checker state s in
      let* a, state = address checker state a in
      let* head, state = walk state head in
      Ok (Term.Out (s, a, head), state)
  | Term.Sec (s, legs) ->
      let* s, state = shape checker state s in
      let* legs, state = map (leg checker) state legs in
      Ok (Term.Sec (s, legs), state)
  | Term.Let (name, ty, value, body) ->
      let* value, state = term checker state (Some ty) value in
      let* ty, state = walk state ty in
      let* body, state = walk state body in
      Ok (Term.Let (name, ty, value, body), state)
  | Term.Ann (value, ty) ->
      let* value, state = term checker state (Some ty) value in
      let* ty, state = walk state ty in
      Ok (Term.Ann (value, ty), state)
  | Term.Elim e ->
      let* s, state = shape checker state e.Term.e_shape in
      let* scrut, state = walk state e.Term.e_scrut in
      let* motive, state =
        Option.fold ~none:(Ok (None, state))
          ~some:(fun motive ->
            let* body, state = walk state motive.Term.m_body in
            Ok (Some { motive with Term.m_body = body }, state)) e.Term.e_motive
      in
      let* branches, state = map (branch checker) state e.Term.e_branches in
      Ok (Term.Elim { e with Term.e_shape = s; e_scrut = scrut;
                            e_motive = motive; e_branches = branches }, state)

(* Payload positions are rewritten through Rules.map_shape, so this pass
   names no shape (dev/r0-audit.py). Each distinct payload proof is walked
   once: two structurally equal closed proofs in one shape share one
   postulate, and every allocated postulate is referenced. *)
and shape (checker : Check.ctx) (state : state) (s : Term.t Shape.t) :
    (Term.t Shape.t * state, Error.t) result =
  let* replacements, state =
    List.fold_left
      (fun acc original ->
        let* replacements, state = acc in
        if List.mem_assoc original replacements then Ok (replacements, state)
        else
          let* rewritten, state = term checker state None original in
          Ok ((original, rewritten) :: replacements, state))
      (Ok ([], state)) (Shape.payload s)
  in
  let* rewritten = Rules.map_shape
      (fun original -> List.assoc_opt original replacements
        |> Option.to_result ~none:(Error.Mismatch "shape payload is absent from its traversal")) s in
  Ok (rewritten, state)

and address (checker : Check.ctx) (state : state) (a : Term.addr) :
    (Term.addr * state, Error.t) result =
  match a with
  | Term.APt (q, value) ->
      let* value, state = term checker state None value in
      Ok (Term.APt (q, value), state)
  | Term.ALeg _ | Term.ACtor _ -> Ok (a, state)

and leg (checker : Check.ctx) (state : state) (leg : Term.leg) :
    (Term.leg * state, Error.t) result =
  let* body, state = term checker state None leg.Term.l_body in
  Ok ({ leg with Term.l_body = body }, state)

and branch (checker : Check.ctx) (state : state) ((a, body) : Term.addr * Term.leg) :
    ((Term.addr * Term.leg) * state, Error.t) result =
  let* a, state = address checker state a in
  let* body, state = leg checker state body in
  Ok ((a, body), state)

let entry (checker : Check.ctx) (state : state) (entry : Global.entry) :
    (Global.entry * state, Error.t) result =
  match entry with
  | Global.Prim _ -> Ok (entry, state)
  | Global.Axiom axiom ->
      let* ty, state = term checker state None axiom.Global.ax_ty in
      Ok (Global.Axiom { Global.ax_ty = ty }, state)
  | Global.Def definition ->
      let* body, state = term checker state (Some definition.Global.ty) definition.Global.def in
      let* ty, state = term checker state None definition.Global.ty in
      Ok (Global.Def { definition with Global.ty = ty; def = body }, state)

(** The rows are derived from the rewritten environment by name, so the pass
    accepts every program the checker accepts. A redeclared global yields its
    last entry once per row that names it, as the checked environment does.
    Only the last row of each name is compared with its environment entry:
    earlier rows of a redeclared name are superseded, and a row that skipped
    sealing stays detectable. *)
let prepare (checker : Check.ctx) (globals : Global.t)
    (rows : (string * Global.entry) list) :
    (Global.t * (string * Global.entry) list, Error.t) result =
  let* state =
    Global.StringMap.bindings globals.Global.entries
    |> List.fold_left
         (fun result (name, original) ->
           let* state = result in
           let* rewritten, state = entry checker state original in
           Ok { state with globals = Global.add name rewritten state.globals })
         (Ok { globals; next = 0 })
  in
  let* _seen =
    List.fold_right
      (fun (name, original) acc ->
        let* seen = acc in
        match () with
        | () when List.mem name seen -> Ok seen
        | () when Global.find name globals = Some original -> Ok (name :: seen)
        | () ->
            Error
              (Error.Mismatch ("erasure row differs from its environment: " ^ name)))
      rows (Ok [])
  in
  let* rows = Rules.all_ok
      (List.map (fun (name, _original) ->
         Global.find name state.globals
         |> Option.to_result ~none:(Error.Unbound name)
         |> Result.map (fun entry -> (name, entry))) rows)
  in
  Ok (state.globals, rows)
