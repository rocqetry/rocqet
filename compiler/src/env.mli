open Types

module PluginScopes : sig
  val peek : unit -> PluginCmdScope.t option
  val push : PluginCmdScope.t -> unit
  val pop : Names.Id.t -> PluginCmdScope.t option
  val ensure_in_scope : scope:PluginCmd.t -> unit
end

module InhJudgements : sig
  val push : name:Names.Id.t -> judgement:InhJudgement.t -> unit
  val pop : unit -> (Names.Id.t * InhJudgement.t) option
  val peek : unit -> (Names.Id.t * InhJudgement.t) option
  val ensure_open_judgememt : unit -> unit
  val current_output_ctx : unit -> FamilyContext.t
  val current_family_name : unit -> Names.Id.t
end

module GlobalCtx : sig
  val push :
    name:Names.Id.t ->
    family_term:FamilyTerm.t ->
    family_type:FamilyType.t ->
    unit

  val lookup : Names.Id.t -> FamilyRef.t option
end
