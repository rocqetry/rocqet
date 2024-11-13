val open_with_base : name:Names.Id.t -> base:Names.Id.t -> unit
val open_with_base_list:
  name:Names.Id.t ->
  bases:Names.Id.t list ->
  unit

val open_trait : name:Names.Id.t -> unit

val close_trait : unit -> unit
