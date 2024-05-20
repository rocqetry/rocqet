val global_env : unit -> Evd.evar_map * Environ.env

val push_local : Names.Name.t Context.binder_annot * Evd.econstr -> Environ.env -> Environ.env

val define : Names.variable -> Evd.econstr -> Evd.evar_map -> unit

val internalize : Environ.env -> Constrexpr.constr_expr -> Evd.evar_map -> Evd.evar_map * Evd.econstr

