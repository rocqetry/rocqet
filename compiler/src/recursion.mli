val add_recursor :
  ind_decls:(Names.Id.t * Libnames.qualid * Constrexpr.constr_expr) list ->
  rec_mod:Libnames.qualid ->
  suffix:string ->
  unit
