module ScopeClosing : sig
  val inherit_all_remained : unit -> unit
  val close_current_inheritance_judgement : unit -> unit
end

val add_new_family : Names.Id.t -> unit
val add_inductive_definition : Ftypes.VernacInductive.t -> unit
