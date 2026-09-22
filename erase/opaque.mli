(** Erasure of checked programs. Classification uses the checked environment;
    the erasure evaluator sees proof declarations only as typed postulates. *)

val prepare :
  ?budget:Kanon_kernel.Budget.t ->
  Kanon_kernel.Global.t ->
  (string * Kanon_kernel.Global.entry) list ->
  (Kanon_kernel.Global.t * (string * Kanon_kernel.Global.entry) list,
   Kanon_kernel.Error.t) result

val program :
  ?budget:Kanon_kernel.Budget.t ->
  Kanon_kernel.Global.t ->
  (string * Kanon_kernel.Global.entry) list ->
  ((string * Kanon_kernel.Erase.entry) list, Kanon_kernel.Error.t) result
