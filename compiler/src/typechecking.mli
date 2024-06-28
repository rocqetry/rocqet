open Types

val check_exhaustive: 
  name:Names.Id.t -> 
  inductive:VernacInductive.t -> 
  handlers:(Names.Id.t * Constrexpr.constr_expr) list -> 
  unit

val check_further_binding_structure : LinkageCtx.t -> unit
