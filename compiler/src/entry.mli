open Types

(* Handle a `Family ...` command *)
val family : Names.Id.t -> unit

(* Handle a `Family ... extends ...` command *)
val family_extends : derived:Names.Id.t -> base:Libnames.qualid -> unit

(* Handle a `FInductive ... := ...` command *)
val finductive : VernacInductive.t -> unit

(* Handle a `FEnd ...` command *)
val fend : Names.Id.t -> unit
