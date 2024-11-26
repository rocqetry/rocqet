open Types

(* TODO: We should not expose this here *)
module B = Backend.Vernac

val compile_empty_signature :
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModuleType.t

(* Compiling inductive definitions *)
val compile_inductive_signature :
  ind_def:VernacInductive.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModuleType.t

val compile_inductive_axiom :
  name:Names.Id.t ->
  ty:Constrexpr.constr_expr ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  CompiledModuleType.t

val compile_inductive_implementation :
  ind_def:VernacInductive.t ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModule.t *
  ((Names.Id.t * Constrexpr.constr_expr) list) RecursorStore.t *
   Constrexpr.constr_expr RecursorStore.t

(* Compiling recursive definitions *)

val compile_theorem_definition_signature :
  names:Names.Id.t list ->
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  family_name:Names.Id.t ->
  CompiledModuleType.t

val compile_computational_axiom_signature :
  ctx:(Names.Id.t * Constrexpr.module_ast) list ->
  constructor_name:Names.Id.t ->  
  inductive:VernacInductive.t ->
  inductive_paths:Libnames.qualid list ->
  recursor_names: Names.Id.t Names.Id.Map.t ->
  prefix:Libnames.qualid option ->
  Names.Id.t * Constrexpr.constr_expr * CompiledModuleType.t

val compile_prec_computational_axiom_signature :
    ctx : (Names.Id.t * Constrexpr.module_ast) list ->
    constructor_name : Names.Id.t ->
    constructor_path : Libnames.qualid ->
    handlers: Names.Id.t list ->    
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

(* Compiling Linkage Contexts *)
val compile_linkage_context :
  field_name:Names.Id.t ->
  LinkageCtx.t ->
  CompiledModuleType.t * (Names.Id.t * Constrexpr.module_ast) list

(* Compiling Linkages *)
val compile_linkage : Linkage.t -> CompiledModule.t
(* include signature, helper signature *)
val compile_linkage_signature : Linkage.t -> CompiledModuleType.t * CompiledModuleType.t

val compile_final_linkage_signature : 
  linkage:Linkage.t -> 
  base:Libnames.qualid -> 
  CompiledModuleType.t

val compile_same_linkage_signature :
  linkage:Linkage.t -> 
  signature:CompiledModuleType.t -> 
  default_ctx_params:(Names.Id.t * CompiledModule.t) list -> 
  CompiledModuleType.t

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
