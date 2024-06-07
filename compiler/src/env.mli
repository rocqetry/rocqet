open Types

module PluginScopes : sig
  val peek : unit -> PluginCmdScope.t option
  val push : PluginCmdScope.t -> unit
  val pop : Names.Id.t -> PluginCmdScope.t option
  val ensure_in_scope : scope:PluginCmd.t -> unit
end

(* Stored computed linkages *)
module Linkages : sig
  val add : Linkage.t -> unit
  val lookup : Names.Id.t -> Linkage.t option
end

(* Computing a linkage in an open context *)
module Context : sig
  val get : unit -> LinkageCtx.t
  val family_name : LinkageCtx.t -> Names.Id.t
  val family_linkage : LinkageCtx.t -> Linkage.t
  val start_linkage : Names.Id.t -> unit
  val start_linkage_with_base : name:Names.Id.t -> base:Names.Id.t -> unit
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
