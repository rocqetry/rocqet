val family : Names.Id.t -> unit 

val family_extends : derived:Names.Id.t -> base:Names.Id.t -> unit

val finductive : (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list -> unit 

val fend : Names.Id.t -> unit 
