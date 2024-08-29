open Types

module Vernac : sig
  type 'a t

  val thunk : (unit -> unit t) -> unit t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( >> ) : 'a t -> 'b t -> 'b t
  val return : 'a -> 'a t
  val flatmap : 'a t list -> unit t
  val run : 'a t -> 'a
  val end_proof : Names.Id.t -> unit t
  val define_inductive : VernacInductive.t -> unit t

  val define_inductive_scheme :
    (Names.Id.t * Names.Id.t * Sorts.family) list -> unit t

  val define_term :
    ?ty:Constrexpr.constr_expr ->
    name:Names.Id.t ->
    Constrexpr.constr_expr ->
    unit t

  val open_module :
    module_name:Names.Id.t ->
    parameters:(Names.Id.t * Constrexpr.module_ast) list ->
    CompiledModule.t t

  val close_module : module_name:Names.Id.t -> CompiledModule.t t

  val define_module :
    module_name:Names.Id.t ->
    parameters:(Names.Id.t * Constrexpr.module_ast) list ->
    body:(CompiledModule.t list -> unit t) ->
    CompiledModule.t t

  val declare_module : module_name:Names.Id.t -> Constrexpr.module_ast -> unit t

  val define_moduletype :
    module_name:Names.Id.t ->
    parameters:(Names.Id.t * Constrexpr.module_ast) list ->
    body:(CompiledModule.t list -> unit t) ->
    CompiledModuleType.t t

  val include_module : module_expr:Constrexpr.module_ast -> unit t
  val assume_parameter : name:Names.Id.t -> ty:Constrexpr.constr_expr -> unit t
  val postulate_axiom : name:Names.Id.t -> ty:Constrexpr.constr_expr -> unit t

  val construct_term_using_proof :
    name:Names.Id.t ->
    proof:Ltac_plugin.Tacexpr.raw_tactic_expr ->
    ty:Constrexpr.constr_expr ->
    unit ->
    unit t
end

module Declare : sig
  val start_module :
    Names.Id.t -> (Names.Id.t * Constrexpr.module_ast) list -> CompiledModule.t

  val end_module : unit -> CompiledModule.t
end
