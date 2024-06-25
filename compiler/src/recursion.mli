open Types

(* val add_recursor :
  ind_decls:(Names.Id.t * Libnames.qualid * Constrexpr.constr_expr) list ->
  rec_mod:Libnames.qualid ->
  suffix:RecKind.t ->
  unit*)

val close_recursion : unit -> unit

val open_recursion :
  name:Names.Id.t ->
  inductive:Libnames.qualid ->
  motive:Constrexpr.constr_expr ->
  suffix:RecKind.t ->
  unit

val open_recursion_extension : name:Names.Id.t -> unit

val add_handler : name:Names.Id.t -> handler:Constrexpr.constr_expr -> unit
