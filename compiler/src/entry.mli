open Types

(* Handle a `Family ...` command *)
val family : Names.Id.t -> unit

(* Handle a `Family ... extends ...` command *)
val family_extends : derived:Names.Id.t -> base:Libnames.qualid -> unit

(* Handle a `FInductive ... := ...` command *)
val finductive : VernacInductive.t -> unit

(* Handle a `FEnd ...` command *)
val fend : Names.Id.t -> unit

(* Handle a `FRecursor ... using ... by ...` command *)
val frecursor :
  ind_decls:(Names.Id.t * Libnames.qualid * Constrexpr.constr_expr) list ->
  rec_mod:Libnames.qualid ->
  suffix:Names.Id.t ->
  unit

(* Handle a `FDefinition ... : ... = ...` command *)
val definition :
  name:Names.Id.t ->
  body_type:Constrexpr.constr_expr ->
  body_expr:Constrexpr.constr_expr ->
  unit
