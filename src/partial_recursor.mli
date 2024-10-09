val add : 
  inductive_path:Libnames.qualid -> 
  handlers:Names.Id.t list ->
  unit

val extend : 
   inductive_path : Libnames.qualid ->
   inherited_handlers: Names.Id.t list ->
   handlers: Names.Id.t list ->
   unit
