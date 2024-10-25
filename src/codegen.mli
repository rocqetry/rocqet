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

val compile_inductive_constr :
  name:Names.Id.t ->
  ty:Constrexpr.constr_expr ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModuleType.t

val compile_inductive_implementation :
  ind_def:VernacInductive.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModule.t * ((Names.Id.t * Constrexpr.constr_expr) list) RecursorStore.t

(* Compiling recursors *)
(* val compile_recursors :
  ind_def:VernacInductive.t ->
  recursors:(Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledRecursor.t RecursorStore.t *)

(* Compiling recursive definitions *)
val compile_motives :
  names:Names.Id.t list ->
  motives:Constrexpr.constr_expr list ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModule.t

(*val compile_handler_types :
  names:Names.Id.t list ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  recursor:CompiledRecursor.t ->
  inductive_path:Libnames.qualid ->
  cases:Names.Id.t list ->
  CompiledModule.t*)

val compile_handler_case :
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  name:Names.Id.t ->
  body:Constrexpr.constr_expr ->
  ty:Constrexpr.constr_expr ->
  CompiledModule.t

val compile_theorem_definition_signature :
  names:Names.Id.t list ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModuleType.t

val compile_computational_axiom_signature :
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  constructor_name:Names.Id.t ->
  inductive_name:Names.Id.t ->
  inductive:VernacInductive.t ->
  recursor_name:Names.Id.t ->
  prefix:Libnames.qualid option ->
  Names.Id.t * Constrexpr.constr_expr * CompiledModuleType.t

val compile_prec_computational_axiom_signature :
    ctx : (Names.Id.t * Constrexpr.module_ast) list ->
    constructor_name : Names.Id.t ->
    constructor_path : Libnames.qualid ->
    handlers: Names.Id.t list ->
    inductive_name: Names.Id.t ->
    inductive : VernacInductive.t ->
    prec_suffix: Names.Id.t ->                
    recursor_path : Libnames.qualid  ->    
    Names.Id.t * Constrexpr.constr_expr * CompiledModuleType.t 

val compile_recursive_definition_signature :
  names:Names.Id.t list ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModuleType.t

val calculate_rec_principle_prefix :
  inductive_path:Libnames.qualid -> context:LinkageCtx.t -> Libnames.qualid

val compile_handler_cases :
  name:Names.Id.t ->
  context:LinkageCtx.t ->
  parameters:(Names.Id.t * Constrexpr.module_ast) list ->
  motive:CompiledModule.t ->
  handler_cases:(Names.Id.t * Constrexpr.constr_expr) list ->
  handler_types:(Names.Id.t * Constrexpr.constr_expr) list ->
  CompiledModule.t

(* Compiling Linkage Contexts *)
val compile_linkage_context :
  field_name:Names.Id.t ->
  LinkageCtx.t ->
  CompiledModuleType.t * (Names.Id.t * Constrexpr.module_ast) list

(* Compiling Linkages *)
val compile_linkage : Linkage.t -> CompiledModule.t
val compile_linkage_signature : Linkage.t -> CompiledModuleType.t

(* Compiling a field definition *)
val compile_definition :
  name:Names.Id.t ->
  ?body_type:Constrexpr.constr_expr ->
  body_expr:Constrexpr.constr_expr ->
  (Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModule.t

(* Compiling FLemma signatures *)
val compile_lemma_signature :
  name:Names.Id.t ->
  ty:Constrexpr.constr_expr ->
  parameters:(Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModuleType.t

val compile_default_params :
  context:(Names.Id.t * Constrexpr.module_ast) list -> 
  (Names.Id.t * CompiledModule.t) list
