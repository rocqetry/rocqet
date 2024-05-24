(* Handle a `Family ...` command *)
val family : Names.Id.t -> unit

(* Handle a `Family ... extends ...` command *)
val family_extends : derived:Names.Id.t -> base:Names.Id.t -> unit

(* Handle a `FInductive ... := ...` command *)
val finductive : Ftypes.VernacInductive.t -> unit

(* Handle a `FEnd ...` command *)
val fend : Names.Id.t -> unit
