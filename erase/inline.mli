(** Replace closed inline proofs in ordinary entries with fresh typed
    postulates, using the original checked context for classification.
    The returned declaration rows do not expose the internal postulates. *)
val prepare :
  Kanon_kernel.Check.ctx ->
  Kanon_kernel.Global.t ->
  (string * Kanon_kernel.Global.entry) list ->
  (Kanon_kernel.Global.t * (string * Kanon_kernel.Global.entry) list,
   Kanon_kernel.Error.t) result
