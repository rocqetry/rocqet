val close_current_inheritance_judgement : unit -> unit
val open_new_inheritance_judgement : Names.Id.t -> unit

val open_derived_inheritance_judgement :
  base:Names.Id.t -> derived:Names.Id.t -> unit
