open Types

val resolve_constrexpr :
  context:LinkageCtx.t ->
  expression:Constrexpr.constr_expr ->
  Constrexpr.constr_expr

val resolve_inductive :
  context:LinkageCtx.t -> inductive:VernacInductive.t -> VernacInductive.t

(* The linkage will be resolved by construction, otherwise how did it
   get created? *)
(* val resolve_linkage : context:LinkageCtx.t -> linkage:Linkage.t ->
   Linkage.t *)
