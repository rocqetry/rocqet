open Types

val check_exhaustive :
  names:Names.Id.t list ->
  inductive:VernacInductive.t ->
  inductive_path:Libnames.qualid ->
  handlers:Names.Id.t list ->
  unit

val check_further_binding_structure : LinkageCtx.t -> unit
