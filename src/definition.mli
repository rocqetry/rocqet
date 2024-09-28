val add_definition :
  name:Names.Id.t ->
  ?body_type:Constrexpr.constr_expr ->
  Constrexpr.constr_expr ->
  unit

val add_opaque_definition : 
  name:Names.Id.t ->
  body_type:Constrexpr.constr_expr ->
  body_expr:Constrexpr.constr_expr ->
  unit

val override : name:Names.Id.t -> expr:Constrexpr.constr_expr -> unit
