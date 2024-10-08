val motive_of : Names.Id.t -> Names.Id.t
val internal_name : Names.Id.t -> Names.Id.t
val recursor_type : inductive:Names.Id.t -> string -> Names.Id.t
val handler_type : Names.Id.t -> suffix:string -> Names.Id.t

val inductive_axiom_name : Names.Id.t -> Names.Id.t

val recursion_handler_type :
  function_name:Names.Id.t -> case_name:Names.Id.t -> Names.Id.t

val principle_name : inductive:Names.Id.t -> kind:string -> Names.Id.t

val computational_axiom_name :
  recursor_name:Names.Id.t -> constructor_name:Names.Id.t -> Names.Id.t

val partial_recursor_name : 
  inductive_name:Names.Id.t -> 
  family_name:Names.Id.t -> 
  Names.Id.t

val prec_computational_axiom_name: 
  constructor_name:Names.Id.t -> 
  family_name:Names.Id.t -> 
  Names.Id.t

val point_qualid : Names.Id.t -> Libnames.qualid -> Libnames.qualid
val qualid_point : Libnames.qualid option -> Names.Id.t -> Libnames.qualid
val path_to_prefix : Libnames.qualid -> Libnames.qualid option * Names.Id.t
val handler_name : recursor:Names.Id.t -> case:Names.Id.t -> Names.Id.t

val replace_qualid_root :
  source:Names.Id.t ->
  target:Names.Id.t ->
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr

val rename_ind_constructors :
  Vernacexpr.constructor_expr list ->
  base_name:Names.Id.t ->
  derived_name:Names.Id.t ->
  Vernacexpr.constructor_expr list

val add_path_constr_expr :
  Names.Id.t ->
  Names.Id.Set.t ->
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr

val add_prefix_path :
  path:Libnames.qualid ->
  names:Names.Id.Set.t ->
  target:Constrexpr.constr_expr ->
  Constrexpr.constr_expr

val self_version : Names.Id.t -> Names.Id.t
val un_self_version : Names.Id.t -> Names.Id.t
val module_name_of : family_name:Names.Id.t -> Names.Id.t -> Names.Id.t
val fresh_name : prefix:string -> Names.Id.t

val replace_self_qualification :
  target:Libnames.qualid option ->
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr

val name_map_with :
  (Names.Id.t -> Names.Id.t) -> Names.Id.t list -> Names.Id.t Names.Id.Map.t

val to_name_optionqualid :
  Libnames.qualid -> Names.Id.t * Libnames.qualid option

val path_to_list : Libnames.qualid -> Names.Id.t list
val list_to_path : Names.Id.t list -> Libnames.qualid

val inv_name_map_with :
  (Names.Id.t -> Names.Id.t) -> Names.Id.t list -> Names.Id.t Names.Id.Map.t

val concat_names : Names.Id.t list -> Names.Id.t

val is_self_name : Names.Id.t -> bool

val is_self_qualid : Libnames.qualid -> bool

val remove_self_qualid : Libnames.qualid -> Libnames.qualid
