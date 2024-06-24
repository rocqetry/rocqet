open Types

module PluginScopes : sig
  val peek : unit -> PluginCmdScope.t option
  val push : PluginCmdScope.t -> unit
  val pop : Names.Id.t -> PluginCmdScope.t option
  val ensure_in_scope : scope:PluginCmd.t -> unit
end

(* Global computed linkages *)
module Linkages : sig
  val add : Linkage.t -> unit
  val lookup : Names.Id.t -> Linkage.t option
end

(* Computing a linkage in an open context *)
module Context : sig
  val get : unit -> LinkageCtx.t
  val get_store : unit -> LinkageCtx.t option
  val lookup : Libnames.qualid -> Linkage.t option

  val lookup_linkage_elem :
    LinkageCtx.t -> Libnames.qualid -> (LinkageElem.t * Linkage.t) option
  val lookup_inductive_for_recursion : 
    name:Libnames.qualid -> 
    LinkageCtx.t -> 
    VernacInductive.t * CompiledRecursors.t * Linkage.t
  
  val family_name : LinkageCtx.t -> Names.Id.t
  val family_linkage : LinkageCtx.t -> Linkage.t
  val add_field : name:Names.Id.t -> elem:LinkageElem.t -> unit
  val further_bound_linkage : LinkageCtx.t -> Linkage.t option
  val base_linkage : LinkageCtx.t -> Linkage.t option

  val base_linkage_elem :
    LinkageCtx.t -> field:Names.Id.t -> (Linkage.t * LinkageElem.t) option

  val further_bound_linkage_elem :
    LinkageCtx.t -> field:Names.Id.t -> (Linkage.t * LinkageElem.t) option

  val replace : linkage:Linkage.t -> unit
  val destructive_update : LinkageCtx.t option -> unit
end
