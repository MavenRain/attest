(** Erasure of checked programs. Classification uses the checked environment;
    global proofs and classifiable closed inline proofs become typed
    postulates before evaluation. Proofs depending on locals remain open. *)

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
