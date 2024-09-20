open Types

val lookup_field_in_base :
  field:Names.Id.t ->  
  context:LinkageCtx.t ->  
  LinkageElem.t option

val inherit_name : name:Names.Id.t -> unit

val inherit_dependencies : prefix:Names.Id.t -> unit

val inherit_elements : 
   elements:(Names.Id.t * LinkageElem.t) list -> 
   linkage:Linkage.t ->
   context:LinkageCtx.t ->
   Linkage.t

val linkage_concatenate :
  derived:Linkage.t ->
  base:Linkage.t ->
  Linkage.t
