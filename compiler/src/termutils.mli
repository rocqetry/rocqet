val global_env : unit -> Evd.evar_map * Environ.env

val internalize :
  Environ.env ->
  Constrexpr.constr_expr ->
  Evd.evar_map ->
  Evd.evar_map * Evd.econstr

val checked_type_of : Constrexpr.constr_expr -> Constr.t
val reflect_checked_term : Constr.t -> Constrexpr.constr_expr
val ident_to_module_expr : Libnames.qualid -> Constrexpr.module_ast

val apply_module :
  functor_expr:Constrexpr.module_ast ->
  arguments:Libnames.qualid list ->
  Constrexpr.module_ast
