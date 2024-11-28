val add :
  name:Names.Id.t ->
  ty:Constrexpr.constr_expr ->
  script:Ltac_plugin.Tacexpr.raw_tactic_expr ->
  plain:bool ->
  unit
