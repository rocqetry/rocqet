open Types

val check_exhaustive :
  names:Names.Id.t list ->
  inductive:VernacInductive.t ->
  inductive_paths:Libnames.qualid list ->
  handlers:Names.Id.t list ->
  (Names.Id.t * Names.Id.t list) list

val check_further_binding_structure : LinkageCtx.t -> unit
