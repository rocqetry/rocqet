val open_family : Names.Id.t -> unit
val open_family_with_base : name:Names.Id.t -> base:Libnames.qualid -> unit

val open_family_with_base_list :
  name:Names.Id.t -> bases:Libnames.qualid list -> unit

val close_family : unit -> unit

val define_final_family : 
  name:Names.Id.t -> 
  value : Libnames.qualid -> 
  unit
