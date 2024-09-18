open Types

val lookup_field_in_base :
  field:Names.Id.t ->
  (* The field name *)    
  context:LinkageCtx.t ->
  (* The current linkage context *)
  LinkageElem.t option

val inherit_name : name:Names.Id.t -> unit

(* Inherit the dependencies of a particular field from it's
   base families into the current linkage context *)
val inherit_dependencies : prefix:Names.Id.t -> unit

val inherit_elements : 
   elements:(Names.Id.t * LinkageElem.t) list -> 
   linkage:Linkage.t ->
   Linkage.t

val linkage_concatenate :
  derived:Linkage.t ->
  base:Linkage.t ->
  Linkage.t
