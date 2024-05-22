module type S = sig
  val define_module : Names.Id.t -> unit
  val dump_output : string -> unit
end
