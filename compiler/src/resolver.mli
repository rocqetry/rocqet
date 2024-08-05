open Types

val resolve_qualid : 
  context:LinkageCtx.t ->
  qualid:Libnames.qualid -> 
  Libnames.qualid

val resolve_constrexpr :
  context:LinkageCtx.t ->
  expression:Constrexpr.constr_expr ->
  Constrexpr.constr_expr

val resolve_constrexpr_list :
  context:LinkageCtx.t ->
  expressions:Constrexpr.constr_expr list ->
  Constrexpr.constr_expr list

val resolve_inductive :
  context:LinkageCtx.t -> inductive:VernacInductive.t -> VernacInductive.t

(* The linkage will be resolved by construction, otherwise how did it
   get created? *)
(* val resolve_linkage : context:LinkageCtx.t -> linkage:Linkage.t ->
   Linkage.t *)
