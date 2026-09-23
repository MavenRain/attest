(** Replace inline proofs in ordinary entries with fresh typed postulates,
    using the original checked context for classification. Known function,
    let and former binders become erased parameters of closed postulates.
    Branch, motive and indirectly typed lambda scopes remain conservative.
    The returned declaration rows do not expose the internal postulates. *)
val prepare :
  Kanon_kernel.Check.ctx ->
  Kanon_kernel.Global.t ->
  (string * Kanon_kernel.Global.entry) list ->
  (Kanon_kernel.Global.t * (string * Kanon_kernel.Global.entry) list,
   Kanon_kernel.Error.t) result
