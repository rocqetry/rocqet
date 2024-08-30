open Types

val inherit_element :
  field:Names.Id.t ->
  (* The field name *)
  linkage:Linkage.t ->
  (* The current linkage *)
  context:LinkageCtx.t ->
  (* The current linkage context *)
  LinkageElem.t option

(* Inherit the dependencies of a particular field from it's
   base families into the current linkage context *)
val inherit_dependencies : prefix:Names.Id.t -> unit
