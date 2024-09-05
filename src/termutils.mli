open Types

val global_env : unit -> Evd.evar_map * Environ.env

val internalize :
  Environ.env ->
  Constrexpr.constr_expr ->
  Evd.evar_map ->
  Evd.evar_map * Evd.econstr

val checked_type_of : Constrexpr.constr_expr -> Constr.t
val reflect_checked_term : Constr.t -> Constrexpr.constr_expr
val cbn_type_check : Constrexpr.constr_expr -> Constr.t
val ident_to_module_expr : Libnames.qualid -> Constrexpr.module_ast

type local_binder_expr_assume =
  Names.lname list * Constrexpr.binder_kind * Constrexpr.constr_expr

val collect_argument_and_ret_of_type :
  Constrexpr.constr_expr ->
  (local_binder_expr_assume * Constrexpr.constr_expr) list
  * Constrexpr.constr_expr

val extract_variables_and_apply :
  Constrexpr.constr_expr ->
  (local_binder_expr_assume * Constrexpr.constr_expr) list
  * Constrexpr.constr_expr

val apply_module :
  functor_expr:Constrexpr.module_ast ->
  arguments:Libnames.qualid list ->
  Constrexpr.module_ast

val generate_computational_axioms :
  provenance:Names.Id.t ->
  constructors:Names.Id.t list ->
  recursor:Names.Id.t ->
  prefix:Libnames.qualid option ->
  (Names.Id.t * Constrexpr.constr_expr) list

val handler_types_table :
  Libnames.qualid -> Names.Id.t -> CompiledRecursor.t -> RecKind.t -> (Names.Id.t * Constrexpr.constr_expr) list

val extract_handlers_from_inductive_proof :
  Names.Id.t list ->
  Constrexpr.constr_expr ->
  RecKind.t ->
  (Names.Id.t * Constrexpr.constr_expr) list

val calculate_inductive_proof_goal :
  handler_types:Constrexpr.constr_expr list ->    
  suffix:RecKind.t ->
  Constrexpr.constr_expr

val mk_lambda :
  Names.Id.t list -> Constrexpr.constr_expr -> Constrexpr.constr_expr

val mk_lambda_with_type :
  (Names.Id.t * Constrexpr.constr_expr) list ->
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr

(* fun (x : ...) -> forall (x : ...) *)
val lambda_to_prod : Constrexpr.constr_expr -> Constrexpr.constr_expr
