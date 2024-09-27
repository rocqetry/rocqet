open Types

val close_recursion : unit -> unit

val open_recursion :
  args:Frec_arg.t list ->
  suffix:RecKind.t ->
  arguments:Names.Id.t list ->
  unit

val open_recursion_extension : name:Names.Id.t -> unit

val add_handler :
  name:Names.Id.t ->
  arguments:Names.Id.t list option ->
  handler:Constrexpr.constr_expr ->
  unit

val elegant : Names.Id.t -> (Names.Id.t * Constrexpr.constr_expr) list -> unit
