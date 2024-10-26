open Types

(* Handle a `Family ...` command *)
val family : Names.Id.t -> unit

(* Handle a `Family ... extends ...` command *)
val family_extends : derived:Names.Id.t -> base:Libnames.qualid -> unit

(* Hanle a `Family ... extends ... using ...`  *)
val family_extends_list :
  derived:Names.Id.t ->  
  bases:Libnames.qualid list ->
  unit

(* Handle a `Metadata ...` section *)
val metadata : Names.Id.t -> unit

(* Handle a `FInductive ... := ...` command *)
val finductive : VernacInductive.t -> unit

val fend_with: Names.Id.t list -> unit

(* Handle a `FEnd ...` command *)
val fend : Names.Id.t -> unit

(* Handle a `FRecursor ... using ... by ...` command *)
(*val frecursor :
  ind_decls:(Names.Id.t * Libnames.qualid * Constrexpr.constr_expr) list ->
  rec_mod:Libnames.qualid ->
  suffix:RecKind.t ->
  unit*)

(* Handle a `FDefinition ... : ... = ...` command *)
val definition :
  name:Names.Id.t ->
  ?body_type:Constrexpr.constr_expr ->
  Constrexpr.constr_expr ->
  unit

val opaque_definition :
  name:Names.Id.t ->
  body_type:Constrexpr.constr_expr ->
  body_expr:Constrexpr.constr_expr ->
  unit

val foverride:
  name:Names.Id.t ->
  expr:Constrexpr.constr_expr ->
  unit

val foverride_lemma :
  Names.Id.t -> unit

(* Handle an `FRecursion ...` *)
val frecursion :
  Frec_arg.t list ->
  RecKind.t ->
  unit

(* Handle an `FRecursion ...` extension *)
val frecursion_extension : names:Names.Id.t list -> unit

(* Handle a `Case ... := ...` *)
val frecursion_handler :
  name:Names.Id.t ->
  arguments:Names.Id.t list option ->
  handler:Constrexpr.constr_expr ->
  unit

(* New FRecursion syntax *)
val frecursion_elegant :
  Names.Id.t -> (Names.Id.t * Constrexpr.constr_expr) list -> unit

(* Handle an `FInduction ...` *)
val finduction : Frec_arg.t list -> unit

(* Handle a `FInduction ...` extension *)
val finduction_extension : names:Names.Id.t list -> unit
val fproof : unit -> Declare.Proof.t
val fproof_lemma : unit -> Declare.Proof.t

(* Handle an `FLemma ... : ...` *)
val flemma : Names.Id.t -> Constrexpr.constr_expr -> unit
val close_flemma : unit -> unit
val display_plugin_scope : unit -> unit

val closing_fact : 
  name:Names.Id.t -> 
  ty:Constrexpr.constr_expr -> 
  script:Ltac_plugin.Tacexpr.raw_tactic_expr -> 
  unit

val inherit_name : name:Names.Id.t -> unit

val open_trait_with_base : name:Names.Id.t -> base:Names.Id.t -> unit
