open Types

val open_theorem : args:Frec_arg.t list -> unit
val open_theorem_extension : names:Names.Id.t list -> unit
val close_theorem : unit -> unit
val start_proving : unit -> Declare.Proof.t
