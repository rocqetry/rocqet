open Types

module PluginScopes : sig
  val peek : unit -> PluginCmdScope.t option
  val push : PluginCmdScope.t -> unit
  val pop : Names.Id.t list -> PluginCmdScope.t option
  val ensure_in_scope : scope:PluginCmd.t -> unit
  val display : unit -> unit
end

(* Global computed linkages *)
module Linkages : sig
  val add : Linkage.t -> unit
  val lookup : Names.Id.t -> Linkage.t option
  (* exposing this here for implicit horizontal import *)
  val lookup_external : Names.Id.t -> Linkage.t option
  val lookup_external_horizontals : Names.Id.t -> Linkage.t list
end

(* Computing a linkage in an open context *)
module Context : sig
  val get : unit -> LinkageCtx.t
  val get_store : unit -> LinkageCtx.t option

  type compiled_context =
    Libnames.qualid * (Names.variable * Constrexpr.module_ast) list

  val pin_context : unit -> unit
  val unpin_context : unit -> unit
  val with_pinned_context : 'a. (unit -> 'a) -> 'a
  val with_unpinned_context : 'a. (unit -> 'a) -> 'a
  val compute_or_pinned : (unit -> compiled_context) -> compiled_context
  val local_lookup : LinkageCtx.t -> Libnames.qualid -> Linkage.t option
  val lookup : LinkageCtx.t option -> Libnames.qualid -> Linkage.t option

  val lookup_linkage_elem :
    LinkageCtx.t -> Libnames.qualid -> (LinkageElem.t * Linkage.t) option

  val lookup_inductive_for_recursion :
    name:Libnames.qualid ->
    LinkageCtx.t ->
    VernacInductive.t * Recursors.t * Linkage.t

  val family_name : LinkageCtx.t -> Names.Id.t
  val family_linkage : LinkageCtx.t -> Linkage.t
  val add_field : name:Names.Id.t -> elem:LinkageElem.t -> unit
  val base_linkage : LinkageCtx.t -> Linkage.t option

  val base_linkage_elem :
    LinkageCtx.t -> field:Names.Id.t -> (Linkage.t * LinkageElem.t) option

  (* These functions return the further bound family/linkage and the
     deriving family which gave rise to this further binding *)
  val further_bound_linkage :
    LinkageCtx.t -> ((Names.Id.t * Names.Id.t) * Linkage.t) list

  val further_bound_linkage_elem :
    LinkageCtx.t ->
    field:Names.Id.t ->
    ((Names.Id.t * Names.Id.t) * Linkage.t * LinkageElem.t) list

  val replace : linkage:Linkage.t -> unit
  val destructive_update : LinkageCtx.t option -> unit
end
