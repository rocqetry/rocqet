open Bwd

module VernacInductive : sig
  type t =
    (Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) list

  val extract_type_and_cstrs :
    Vernacexpr.inductive_expr ->
    (* inductive type name * sort/kind  *)
    (Names.Id.t * Constrexpr.constr_expr option)
    * (* constr name * constructor type *)
    (Names.Id.t * Constrexpr.constr_expr) list

  val extract_all_names_with_type :
    t ->
    ((Names.Id.t * Constrexpr.constr_expr)
    * (Names.Id.t * Constrexpr.constr_expr) list)
    list

  val extract_all_names : t -> (Names.Id.t * Names.Id.t list) list
  val extract_inductive_name : t -> Names.Id.t

  val definition_mapping :
    prefix:string ->
    t ->
    t * (Names.Id.t * Constrexpr.constr_expr * Constrexpr.constr_expr) list

  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t
  val concatenate : base:t -> derived:t -> t
end

module CompiledModule : sig
  type t = Libnames.qualid
end

module CompiledModuleType : sig
  type t = Libnames.qualid
end

module RecKind : sig
  type t = Ind | IndComplete | Rec | Rect

  val compare : t -> t -> int
  val to_string : t -> string
  val of_string : string -> t
  val of_name : Names.Id.t -> t
end

module RecursorStore : Map.S with type key = RecKind.t

module CompiledRecursor : sig
  type t = {
    inductive_names : Names.Id.t list;
    compiled_recursor : CompiledModuleType.t;
    compiled_handlers : (Names.Id.t * CompiledModuleType.t) list;
  }
end

module CompiledRecursors : sig
  type t = {
    compiled_context : CompiledModuleType.t;
    recursors : CompiledRecursor.t RecursorStore.t;
  }
end

module PluginCmd : sig
  type t = Family | Recursion
end

module PluginCmdScope : sig
  type t = { command : PluginCmd.t; name : Names.Id.t; close : unit -> unit }
end

module rec LinkageElem : sig
  type t =
    | InductiveDefinition of {
        inductive : VernacInductive.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        compiled_recursors : CompiledRecursors.t ref;
      }
    | FamilyDefinition of {
        linkage : Linkage.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
      }
    | FieldDefinition of {
        body_expr : Constrexpr.constr_expr;
        body_type : Constrexpr.constr_expr option;
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModuleType.t;
      }
    | RecursorDefinition of {
        names : Names.Id.t list;
        handlers : Names.Id.t list;
        (* ind_names : Names.Id.t list; *)
        inductive : VernacInductive.t;
        recursor_module : Libnames.qualid;
        motive_module : CompiledModule.t;
        suffix : RecKind.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
      }
    | PrincipleDefinition of {
        compiled_context : CompiledModuleType.t;
        inductive : VernacInductive.t;
        compiled_impl : CompiledModule.t;
        compiled_signature : CompiledModuleType.t;
      }
end

and Linkage : sig
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  val context_parameters : t -> Libnames.qualid list
  val context_match : t -> t -> [ `Equal | `Less | `More ]
  val top_most_self_name : t -> Names.Id.t
  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t
  val concatenate_recursive : derived:t -> base:t -> t
  val concatenate : derived:t -> base:t -> t
  val concatenate_prefix : prefix:Names.Id.t -> derived:t -> base:t -> t

  val concatenate_recursive_prefix :
    prefix:Names.Id.t -> derived:t -> base:t -> t
end

and LinkageCtx : sig
  type t = Toplevel of Linkage.t | Nested of t * Linkage.t
end

module FieldInhKind : sig
  type t = New | Extend of LinkageElem.t
end
