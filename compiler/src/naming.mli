val point_qualid : Names.Id.t -> Libnames.qualid -> Libnames.qualid

val rename_ind_constructors :
  Vernacexpr.constructor_expr list ->
  base_name:Names.Id.t ->
  derived_name:Names.Id.t ->
  Vernacexpr.constructor_expr list

val self_version : Names.Id.t -> Names.Id.t
val module_name_of : family_name:Names.Id.t -> Names.Id.t -> Names.Id.t
val fresh_name : prefix:string -> Names.Id.t

val name_map_with :
  (Names.Id.t -> Names.Id.t) -> Names.Id.t list -> Names.Id.t Names.Id.Map.t

val to_name_optionqualid :
  Libnames.qualid -> Names.Id.t * Libnames.qualid option

val path_to_list : Libnames.qualid -> Names.Id.t list

val inv_name_map_with :
  (Names.Id.t -> Names.Id.t) -> Names.Id.t list -> Names.Id.t Names.Id.Map.t
