open Types

val add_record : RecordDecl.t -> VernacInductive.t -> unit

val extend_record :
  rd:RecordDecl.t ->
  original_inductive:VernacInductive.t ->
  defaults:(Names.Id.t * Constrexpr.constr_expr) list ->
  unit
