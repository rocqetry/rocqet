open Types

(* TODO: We should not expose this here *)
module B = Backend.Vernac

(* Module compilation helpers *)
val wrap_module :
  module_name:Names.Id.t ->
  inner_module:CompiledModule.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModule.t

(* Compiling inductive definitions *)
val compile_inductive_signature :
  ind_def:VernacInductive.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModuleType.t

val compile_inductive_implementation :
  ind_def:VernacInductive.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModule.t * (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t

(* Compiling recursors *)
val compile_recursors :
  ind_def:VernacInductive.t ->
  recursors:(Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledRecursor.t RecursorStore.t

val compile_principle_signature :
  ind_def:VernacInductive.t ->
  recursors:(Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModuleType.t

val compile_principle_implementation :
  (Names.Id.t * Constrexpr.module_ast) list -> CompiledModule.t

(* Compiling recursive definitions *)
val compile_motives :
  names:Names.Id.t list ->
  motives:Constrexpr.constr_expr list ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModule.t

val compile_recursive_definition_signature :
  names:Names.Id.t list ->
  motive_module:CompiledModule.t ->
  handler_cases:CompiledModule.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->  
  family_name:Names.Id.t ->
  computational_behaviour:[ `Exposed | `Hidden ] ->
  computational_axioms:(Names.Id.t * Constrexpr.constr_expr) list ->
  CompiledModuleType.t

val compile_recursive_definition_implementation :
  inductive:VernacInductive.t ->
  provenance:Linkage.t ->
  recursor_name:Names.Id.t ->
  handlers:Names.Id.t list ->
  rec_principle_prefix:Libnames.qualid option ->
  suffix:RecKind.t ->  
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  handler_cases:CompiledModule.t ->
  CompiledModule.t * (Names.Id.t * Constrexpr.constr_expr) list

val include_handler_types : Linkage.t -> CompiledRecursor.t -> unit B.t

val compile_handler_cases :
  name:Names.Id.t ->
  context:LinkageCtx.t ->
  parameters:(Names.Id.t * Constrexpr.module_ast) list ->
  motive:CompiledModule.t ->
  handler_cases:(Names.Id.t * Constrexpr.constr_expr) list ->
  handler_types:(Names.Id.t * Constrexpr.constr_expr) list ->
  compiled_handler_types:CompiledModule.t ->
  provenance:Linkage.t ->
  recursor:CompiledRecursor.t ->
  CompiledModule.t

val aggregate_handler_types :
  CompiledRecursor.t ->
  (Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModule.t

(* FInduction *)
val compile_theorem_implementation :
  name:Names.Id.t ->
  parameters:(Names.Id.t * Constrexpr.module_ast) list ->
  compiled_handlers:CompiledModule.t ->
  motive_name:Names.Id.t ->
  inductive_name:Names.Id.t ->
  suffix:RecKind.t ->
  goal:Constrexpr.constr_expr ->
  provenance:Linkage.t ->
  handler_names:Names.Id.t list ->
  CompiledModule.t

(* Compiling Linkage Contexts *)
val compile_linkage_context :
  field_name:Names.Id.t ->
  LinkageCtx.t ->
  CompiledModuleType.t * (Names.Id.t * Constrexpr.module_ast) list

(* Compiling Linkages *)
val compile_linkage : Linkage.t -> CompiledModule.t
val compile_nested_linkage : Linkage.t -> CompiledModule.t
val compile_linkage_signature : Linkage.t -> CompiledModuleType.t

(* Compiling a field definition *)
val compile_definition :
  name:Names.Id.t ->
  ?body_type:Constrexpr.constr_expr ->
  body_expr:Constrexpr.constr_expr ->
  (Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModule.t

(* Linkage computation *)
val recompute_linkage : Linkage.t -> Linkage.t
