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
  val start_linkage : Names.Id.t -> unit
  val start_linkage_with_base : name:Names.Id.t -> base:Names.Id.t -> unit
  val add_field : name:Names.Id.t -> elem:LinkageElem.t -> unit
  val close : unit -> Linkage.t 
  val replace : linkage:Linkage.t -> unit
end
