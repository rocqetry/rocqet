val rename_ind_constructors :
  Vernacexpr.constructor_expr list ->
  base_name:Names.Id.t ->
  derived_name:Names.Id.t ->
  Vernacexpr.constructor_expr list

val self_version : Names.Id.t -> Names.Id.t

val fresh_name : prefix:string -> Names.Id.t
