type term = Lit of int | Var of int | Let of term * term | Ann of term
type job = Eval of term * int list | Return of int
type kont = Halt | Bind of term * int list * kont
type outcome = Done of int | Exhausted | Invalid_scope

let rec lookup (index : int) (env : int list) : int option =
  match env with
  | [] -> None
  | head :: tail -> if index = 0 then Some head else lookup (index - 1) tail

let rec run (fuel : int) (job : job) (stack : kont) : outcome =
  if fuel <= 0 then Exhausted
  else
    let remaining = fuel - 1 in
    match job with
    | Eval (term, env) ->
        (match term with
         | Lit value -> run remaining (Return value) stack
         | Var index -> lookup index env
             |> Option.fold ~none:Invalid_scope
                  ~some:(fun value -> run remaining (Return value) stack)
         | Let (value, body) ->
             run remaining (Eval (value, env)) (Bind (body, env, stack))
         | Ann body -> run remaining (Eval (body, env)) stack)
    | Return value ->
        (match stack with
         | Halt -> Done value
         | Bind (body, env, next) -> run remaining (Eval (body, value :: env)) next)

let terminal (n : int) (seed : int) : term =
  if n = 0 then Lit seed else Var 0

let rec make (depth : int) (n : int) (seed : int) : term =
  if depth = 0 then terminal n seed
  else Let (Lit seed, Ann (make (depth - 1) (n + 1) ((seed + 1) land 0xffffffff)))

type totals = { checksum : int; failures : int }

let rec batch (count : int) (depth : int) (seed : int) (acc : totals) : totals =
  if count = 0 then acc
  else
    let delta =
      match run 512 (Eval (make depth 0 seed, [])) Halt with
      | Done value -> { checksum = value; failures = 0 }
      | Exhausted | Invalid_scope -> { checksum = 0; failures = 1 }
    in
    batch (count - 1) depth ((seed + 1) land 0xffffffff)
      { checksum = (acc.checksum + delta.checksum) land 0xffffffff;
        failures = acc.failures + delta.failures }
