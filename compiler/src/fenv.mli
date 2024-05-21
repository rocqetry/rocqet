module PluginScopes : sig 
  val peek : unit -> Ftypes.PluginCmdScope.t option
  val push : Ftypes.PluginCmdScope.t -> unit
  val pop : Names.Id.t -> Ftypes.PluginCmdScope.t option 
end

module InhJudgements : sig 
  val push : name:Names.Id.t -> judgement:Ftypes.InhJudgement.t -> unit 
end 
