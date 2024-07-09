val open_theorem :
  name:Names.Id.t ->
  inductive:Libnames.qualid ->
  motive:Constrexpr.constr_expr ->
  unit

val open_theorem_extension :
  name:Names.Id.t -> unit

val close_theorem : unit -> unit
val start_proving : unit -> Declare.Proof.t
