module PluginScopes : sig
  val peek : unit -> Ftypes.PluginCmdScope.t option
  val push : Ftypes.PluginCmdScope.t -> unit
  val pop : Names.Id.t -> Ftypes.PluginCmdScope.t option
  val ensure_in_scope : scope:Ftypes.PluginCmd.t -> unit
end

module InhJudgements : sig
  val push : name:Names.Id.t -> judgement:Ftypes.InhJudgement.t -> unit
  val pop : unit -> (Names.Id.t * Ftypes.InhJudgement.t) option
  val ensure_open_judgememt : unit -> unit
  val current_output_ctx : unit -> Ftypes.FamilyContext.t
end
