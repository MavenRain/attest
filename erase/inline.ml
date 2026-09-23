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

(** Direct subterms, each with the number of binders it sits under. *)
let children (term : Term.t) : (int * Term.t) list =
  let here t = (0, t) in
  let shape s = List.map here (Shape.payload s) in
  let address a =
    match a with
    | Term.APt (_, t) -> [ here t ]
    | Term.ALeg _ | Term.ACtor _ -> []
  in
  let leg (l : Term.leg) = (List.length l.Term.l_binders, l.Term.l_body) in
  match term with
  | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto -> []
  | Term.Lan (s, diagram) | Term.Ran (s, diagram) ->
      shape s @ [ ((if Option.is_some (Shape.point_dom s) then 1 else 0), diagram) ]
  | Term.In (s, a, args) -> shape s @ address a @ List.map here args
  | Term.Out (s, a, head) -> shape s @ address a @ [ here head ]
  | Term.Sec (s, legs) -> shape s @ List.map leg legs
  | Term.Elim e ->
      shape e.Term.e_shape @ [ here e.Term.e_scrut ]
      @ Option.fold ~none:[]
          ~some:(fun (m : Term.motive) -> [ (List.length m.Term.m_idx + 1, m.Term.m_body) ])
          e.Term.e_motive
      @ List.concat_map (fun (a, l) -> address a @ [ leg l ]) e.Term.e_branches
  | Term.Let (_, ty, value, body) -> [ here ty; here value; (1, body) ]
  | Term.Ann (value, ty) -> [ here value; here ty ]

let rec occurs (target : int) (term : Term.t) : bool =
  match term with
  | Term.Var ix -> ix = target
  | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto | Term.Lan _ | Term.Ran _
  | Term.In _ | Term.Out _ | Term.Sec _ | Term.Elim _ | Term.Let _ | Term.Ann _ ->
      List.exists (fun (shift, child) -> occurs (target + shift) child) (children term)

(** The variable occurs in type syntax: an annotation, a let type, the value
    of any let, a motive, a shape payload or a type former. Every let value
    counts, whatever its declared type: a let can bind a type through a
    universe alias or a type family, and a proof let can alias another proof
    let, so a syntactic test on the let type would miss both. No other
    position counts: an elimination scrutinee is not type syntax, so this
    test does not find every type that needs the value. *)
let rec typed (target : int) (term : Term.t) : bool =
  let shape s = List.exists (occurs target) (Shape.payload s) in
  let here =
    match term with
    | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto -> false
    | Term.Lan _ | Term.Ran _ -> occurs target term
    | Term.In (s, _, _) | Term.Out (s, _, _) | Term.Sec (s, _) -> shape s
    | Term.Elim e ->
        shape e.Term.e_shape
        || Option.fold ~none:false
             ~some:(fun (m : Term.motive) ->
               occurs (target + List.length m.Term.m_idx + 1) m.Term.m_body)
             e.Term.e_motive
    | Term.Let (_, ty, value, _) -> occurs target ty || occurs target value
    | Term.Ann (_, ty) -> occurs target ty
  in
  here || List.exists (fun (shift, child) -> typed (target + shift) child) (children term)

type state = { globals : Global.t; next : int }

(** A telescope entry is a bound parameter, or a let definition that stays
    transparent, so a proof type can depend on the let value. *)
type local = Param of string * Term.t | Local of string * Term.t * Term.t

type context = { checker : Check.ctx; domains : local list }

let rec map (f : state -> 'a -> ('b * state, Error.t) result) (state : state)
    (items : 'a list) : ('b list * state, Error.t) result =
  match items with
  | [] -> Ok ([], state)
  | item :: rest ->
      let* item, state = f state item in
      let* rest, state = map f state rest in
      Ok (item :: rest, state)

(** Classification reads the original checked environment. A known scoped
    type is sufficient: the proof body need not be inspected again. Terms
    requiring an expected type are left to their annotated parent. *)
let proof_type (checker : Check.ctx) (expected : Term.t option) (term : Term.t) :
    (Term.t option, Error.t) result =
  if not (closed checker.Check.size term) then Ok None
  else
    let infer () =
      match term with
      | Term.Ann (_, ty) -> Ok (Some ty)
      | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto
      | Term.Lan _ | Term.Ran _ -> Ok None
      | Term.In _ | Term.Sec _ | Term.Out _ | Term.Elim _ | Term.Let _ ->
          (* An inferred local result is normalized and may lose its declared
             universe. Require source type syntax before sealing an open term. *)
          if not (closed 0 term) then Ok None
          else
          Check.infer checker Quantity.Zero term
          |> Result.fold
               ~ok:(fun ty -> Result.map Option.some
                 (Eval.quote checker.Check.globals checker.Check.size ty))
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
        (Option.bind expected
           (fun ty -> if closed checker.Check.size ty then Some ty else None)) () in
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

(** Unknown binders hide the outer context. Closed subterms can still be
    sealed, but their indices must never be read as outer locals. *)
let root (context : context) : context =
  { checker = Check.make context.checker.Check.globals context.checker.Check.budget;
    domains = [] }

(** Retain each domain at the depth where it was bound. The resulting
    telescope is closed, including dependencies between local types.
    Every argument to a proof postulate is erased. A let entry stays a let,
    so its value is visible to the proof type and takes no argument. *)
let abstract (context : context) (ty : Term.t) : Term.t =
  List.fold_left (fun body local ->
      match local with
      | Param (name, domain) -> Rules.arrow Quantity.Zero name domain body
      | Local (name, domain, value) -> Term.Let (name, domain, value, body))
    ty context.domains

let instantiate (context : context) (globals : Global.t) (name : string)
    (ty : Term.t) : (Term.t, Error.t) result =
  let checker = context.checker in
  let apply acc (ix, local) =
    let* head, ty = acc in
    match local with
    | Local _ -> Ok (head, ty)
    | Param _ ->
        let* ty = Eval.whnf globals ty in
        let* s, codomain, _universe = Value.as_ran ty
          |> Option.to_result ~none:(Error.Mismatch "proof postulate lost its telescope") in
        let* s = Rules.map_shape (Eval.quote globals checker.Check.size) s in
        let argument = Value.var (checker.Check.size - ix - 1) in
        let* codomain = Rules.open_closure (Eval.ev globals) codomain [ argument ] in
        Ok (Term.Out (s, Term.APt (Quantity.Zero, Term.Var ix), head), codomain)
  in
  if checker.Check.size = 0 then Ok (Term.Global name)
  else
    let* ty = Eval.eval globals [] ty in
    (* Outermost entry first. Evaluation unfolds a let entry, so it takes no
       argument. *)
    let* head, _ty = List.mapi (fun ix local -> (ix, local)) context.domains
      |> List.rev |> List.fold_left apply (Ok (Term.Global name, ty)) in
    Ok head

let bind_domain (context : context) (name : string) (quantity : Quantity.t)
    (domain : Term.t) : (context, Error.t) result =
  let checker = context.checker in
  if not (closed checker.Check.size domain) then Ok (root context)
  else
    let* value = Eval.eval checker.Check.globals checker.Check.env domain in
    Ok { checker = Check.bind name quantity value checker;
         domains = Param (name, domain) :: context.domains }

let proposition (checker : Check.ctx) (domain : Term.t) : (bool, Error.t) result =
  Result.map (fun level -> Level.equal level Level.zero) (Check.infer_univ checker domain)

(** A let binder keeps its definition, in the checker and in the telescope,
    so a local proof type that needs the let value still checks. *)
let define_let (context : context) (name : string) (domain : Term.t) (value : Term.t) :
    (context, Error.t) result =
  let checker = context.checker in
  if not (closed checker.Check.size domain && closed checker.Check.size value) then
    Ok (root context)
  else
    let* ty = Eval.eval checker.Check.globals checker.Check.env domain in
    let* definition = Eval.eval checker.Check.globals checker.Check.env value in
    Ok { checker = Check.define name Quantity.Zero ty definition checker;
         domains = Local (name, domain, value) :: context.domains }

(** A let of a type keeps its definition. A let of a proposition whose
    variable typed does not find in its body binds a proof: it stays an erased
    parameter, so its body is never inspected again. The node walker gives a
    proof let that typed finds to define_let instead (see needed_proof). *)
let bind_let (context : context) (name : string) (domain : Term.t) (value : Term.t) :
    (context, Error.t) result =
  let checker = context.checker in
  if not (closed checker.Check.size domain && closed checker.Check.size value) then
    Ok (root context)
  else
    let* proof = proposition checker domain in
    if proof then bind_domain context name Quantity.Zero domain
    else define_let context name domain value

(** A type in the body of a proof let can need the let value, for example
    through a large elimination. A sealed value leaves that type stuck. The
    let keeps its value verbatim only when its variable occurs in an
    annotation, a let type, the value of a later let, a motive, a shape
    payload or a type former (see typed). No other position counts: a let
    that a dependent large elimination reads only as its scrutinee is still
    sealed, and erasure then refuses the program when the motive returns a
    type. A later proof let that aliases a kept let is kept by the
    same test, so an alias chain stays transparent at every link. Its body is
    still walked with the let in scope, so a local proof there is sealed over
    the let definition. *)
let needed_proof (context : context) (domain : Term.t) (body : Term.t) :
    (bool, Error.t) result =
  let checker = context.checker in
  if not (closed checker.Check.size domain && typed 0 body) then Ok false
  else
    proposition checker domain

(* The source codomain retains its universe. Normalizing an empty runtime
   product here would turn it into syntax that can also inhabit Prop. *)
let lambda_context (context : context) (expected : Term.t option) (leg : Term.leg) :
    ((context * Term.t) option, Error.t) result =
  Option.fold ~none:(Ok None)
    ~some:(fun ty ->
      match ty with
      | Term.Ran (s, codomain) ->
          (match Rules.as_vpi s, leg.Term.l_binders with
           | Some (q, _name, domain), [ (_bq, name) ] ->
               if not (closed context.checker.Check.size domain) then Ok None
               else
                 let* context = bind_domain context name q domain in
                 Ok (Some (context, codomain))
           | None, _ | Some _, [] | Some _, _ :: _ :: _ -> Ok None)
      | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto
      | Term.Lan _ | Term.In _ | Term.Sec _ | Term.Out _ | Term.Elim _
      | Term.Let _ | Term.Ann _ -> Ok None) expected

let rec term (checker : context) (state : state) (expected : Term.t option)
    (value : Term.t) : (Term.t * state, Error.t) result =
  let* proof = proof_type checker.checker expected value in
  Option.fold ~none:(fun () -> node checker state expected value)
    ~some:(fun ty () ->
      (* A closed type is not enough: a value that reads a local hypothesis
         must abstract over it, or the root postulate is unconditional. *)
      let scope = if closed 0 ty && closed 0 value then root checker else checker in
      let* ty, state = seal_type scope state ty in
      let name, state = fresh state in
      let globals = Global.add name (Global.Axiom { Global.ax_ty = ty }) state.globals in
      let* value = instantiate scope globals name ty in
      Ok (value, { state with globals })) proof ()

(** A postulate type restates its telescope from the root. Each domain and
    let type is walked in the scope where it was bound. The value of a proof
    let stays verbatim: a type that reduces the let would be stuck on a
    sealed value. The checker binds the source terms, whose globals it has. *)
and seal_type (scope : context) (state : state) (ty : Term.t) :
    (Term.t * state, Error.t) result =
  let step acc local =
    let* context, state, entries = acc in
    match local with
    | Param (name, domain) ->
        let* walked, state = term context state None domain in
        let* next = bind_domain context name Quantity.Zero domain in
        Ok (next, state, Param (name, walked) :: entries)
    | Local (name, domain, value) ->
        let* proof = proposition context.checker domain in
        let* sealed, state =
          if proof then Ok (value, state) else term context state (Some domain) value in
        let* walked, state = term context state None domain in
        let* next = define_let context name domain value in
        Ok (next, state, Local (name, walked, sealed) :: entries)
  in
  let* context, state, entries =
    List.fold_left step (Ok (root scope, state, [])) (List.rev scope.domains) in
  let* body, state = term context state None ty in
  Ok (abstract { context with domains = entries } body, state)

and node (checker : context) (state : state) (expected : Term.t option) (value : Term.t) :
    (Term.t * state, Error.t) result =
  let walk state value = term checker state None value in
  match value with
  | Term.Var _ | Term.Global _ | Term.Univ _ | Term.Lit _ | Term.Auto -> Ok (value, state)
  | Term.Lan (s, diagram) ->
      let* context = diagram_context checker s in
      let* s, state = shape checker state s in
      let* diagram, state = term context state None diagram in
      Ok (Term.Lan (s, diagram), state)
  | Term.Ran (s, diagram) ->
      let* context = diagram_context checker s in
      let* s, state = shape checker state s in
      let* diagram, state = term context state None diagram in
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
      let* legs, state = map (lambda checker expected) state legs in
      Ok (Term.Sec (s, legs), state)
  | Term.Let (name, ty, value, body) ->
      let* needed = needed_proof checker ty body in
      if needed then
        let* context = define_let checker name ty value in
        let* ty, state = walk state ty in
        let* body, state = term context state None body in
        Ok (Term.Let (name, ty, value, body), state)
      else
        let* context = bind_let checker name ty value in
        let* value, state = term checker state (Some ty) value in
        let* ty, state = walk state ty in
        let* body, state = term context state None body in
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
            let* body, state = term (root checker) state None motive.Term.m_body in
            Ok (Some { motive with Term.m_body = body }, state)) e.Term.e_motive
      in
      let* branches, state = map (branch checker) state e.Term.e_branches in
      Ok (Term.Elim { e with Term.e_shape = s; e_scrut = scrut;
                            e_motive = motive; e_branches = branches }, state)

and diagram_context (checker : context) (s : Term.t Shape.t) :
    (context, Error.t) result =
  Option.fold ~none:(Ok checker)
    ~some:(fun (q, name, domain) -> bind_domain checker name q domain)
    (Rules.as_vpi s)

and lambda (checker : context) (expected : Term.t option) (state : state)
    (value : Term.leg) : (Term.leg * state, Error.t) result =
  let* context = lambda_context checker expected value in
  Option.fold ~none:(fun () -> leg checker state value)
    ~some:(fun (context, codomain) () ->
      let* body, state = term context state (Some codomain) value.Term.l_body in
      Ok ({ value with Term.l_body = body }, state)) context ()

(* Payload positions are rewritten through Rules.map_shape, so this pass
   names no shape (dev/r0-audit.py). Each distinct payload proof is walked
   once: two structurally equal closed proofs in one shape share one
   postulate, and every allocated postulate is referenced. *)
and shape (checker : context) (state : state) (s : Term.t Shape.t) :
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

and address (checker : context) (state : state) (a : Term.addr) :
    (Term.addr * state, Error.t) result =
  match a with
  | Term.APt (q, value) ->
      let* value, state = term checker state None value in
      Ok (Term.APt (q, value), state)
  | Term.ALeg _ | Term.ACtor _ -> Ok (a, state)

and leg (checker : context) (state : state) (leg : Term.leg) :
    (Term.leg * state, Error.t) result =
  let checker = if leg.Term.l_binders = [] then checker else root checker in
  let* body, state = term checker state None leg.Term.l_body in
  Ok ({ leg with Term.l_body = body }, state)

and branch (checker : context) (state : state) ((a, body) : Term.addr * Term.leg) :
    ((Term.addr * Term.leg) * state, Error.t) result =
  let* a, state = address checker state a in
  let* body, state = leg checker state body in
  Ok ((a, body), state)

let entry (checker : context) (state : state) (entry : Global.entry) :
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
  let checker = { checker; domains = [] } in
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
