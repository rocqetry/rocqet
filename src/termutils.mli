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

val flatten_inductive_constructor_type :
  inductive:VernacInductive.t ->
  constructor:Names.Id.t ->
  Libnames.qualid_r option list
(** Given a constructor name [n] in an inductive type [i], 
   [flatten_inductive_constructor_type i n] returns a list 
   of optional names. This list correspoinds to the types of 
   argument of [i]. If the type of an argument is a 
   simple name [name] and [name] is the same as [i], then
   it would be [Some name] otherwise it will be none.
   We are effectively tracking the recursive location in 
   the constructor where the inductived type appears 
   recursively. *)

val generate_one_computational_axiom :
  inductive:VernacInductive.t ->
  recursor_name:Names.Id.t ->
  recursor_path:Libnames.qualid ->
  constructor_name:Names.Id.t ->
  constructor_path:Libnames.qualid ->
  context:LinkageCtx.t option ->
  Names.Id.t * Constrexpr.constr_expr

val generate_computational_axioms :
  inductive:VernacInductive.t ->
  recursor:Names.Id.t ->
  context:LinkageCtx.t option ->
  prefix:Libnames.qualid option ->
  (Names.Id.t * Constrexpr.constr_expr) list

val handler_types_table :
  Libnames.qualid ->
  Names.Id.t ->
  CompiledRecursor.t ->
  RecKind.t ->
  (Names.Id.t * Constrexpr.constr_expr) list

val handler_type_for_recursion :
  name:Names.Id.t ->
  inductive_path:Libnames.qualid ->
  recursor:Recursor.t ->
  (Names.Id.t * Constrexpr.constr_expr) list

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
val extract_functor_name : Constrexpr.module_ast -> CompiledModuleType.t

val extract_handler_types_from_principle :
  inductive:VernacInductive.t ->
  principles:(Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t ->
  Recursors.t
