val add : 
  inductive_path:Libnames.qualid -> 
  handlers:Names.Id.t list ->
  prec_suffix:Names.Id.t ->
  unit

val extend : 
   inductive_path : Libnames.qualid ->
   old_prec_suffix : Names.Id.t ->
   prec_suffix : Names.Id.t ->
   inherited_handlers: Names.Id.t list ->
   handlers: Names.Id.t list ->
   unit
