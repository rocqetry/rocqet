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
  
  val create_inductive_constructor_map : t -> Names.Id.t list Names.Id.Map.t

  val extract_all_names_with_type :
    t ->
    ((Names.Id.t * Constrexpr.constr_expr)
    * (Names.Id.t * Constrexpr.constr_expr) list)
    list

  val extract_all_names : t -> (Names.Id.t * Names.Id.t list) list
  val extract_inductive_name : t -> Names.Id.t
  val extract_all_inductive_names : t -> Names.Id.t list

  val extract_all_constructors : t -> Names.Id.t list

  val definition_mapping :
    t -> t * (Names.Id.t * Constrexpr.constr_expr * Constrexpr.constr_expr) list

  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t
  val concatenate : base:t -> derived:t -> t

  val lookup_inductive_name: constructor:Names.Id.t -> inductive:t -> Names.Id.t
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

module MutualRecursor : sig
  type t = {
    mutual_recursor : Constrexpr.constr_expr;
    mutual_handlers : (Names.Id.t * Constrexpr.constr_expr) list;
    }
end

module Recursor : sig
  type t = {
    recursors : Constrexpr.constr_expr Names.Id.Map.t;
    handlers : (Names.Id.t * Constrexpr.constr_expr) list Names.Id.Map.t;
    mutual : MutualRecursor.t option;
  }
end

module Recursors : sig
  type t = Recursor.t RecursorStore.t
end

module PluginCmd : sig
  type t = Family | Recursion | Induction | MetaData | Lemma | Trait
end

module PluginCmdScope : sig
  type t = { command : PluginCmd.t; names : Names.Id.t list; close : unit -> unit }
end

module rec LinkageElem : sig
  type t =
    | InductiveDefinition of {
        inductive : VernacInductive.t;
        recursors : Recursors.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;        
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | InductiveAxiom of {
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | FamilyDefinition of {
        linkage : Linkage.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | TraitDefinition of { 
        linkage: Linkage.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | FieldDefinition of {
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | OpaqueFieldDefinition of {
        type_name : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | RecursorDefinition of {
        names : Names.Id.t list;        
        handlers : (Names.Id.t * Names.Id.t list) list;
        inductive_paths : Libnames.qualid list;
        suffix : RecKind.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        arguments : Names.Id.t list;
        prefix : Libnames.qualid;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | TheoremDefinition of {
        names : Names.Id.t list;
        suffix : RecKind.t;
        inductive_paths : Libnames.qualid list;
        handlers : (Names.Id.t * Names.Id.t list) list;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | ComputationalAxiom of {
        name : Names.Id.t;
        axiom : Constrexpr.constr_expr;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | MetaDataSection of {
        name : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | ClosingFact of { 
        type_name : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        script: Ltac_plugin.Tacexpr.raw_tactic_expr;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
    }
    | PartialRecursor of { 
        name: Names.Id.t;
        type_name: Names.Id.t;
        inductive_path: Libnames.qualid;
        handlers: Names.Id.t list;
        defining_handlers : Names.Id.t list;
        behaviour: (Names.Id.t * Names.Id.t) list;
        prec_suffix : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;                
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
end

and Linkage : sig
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    default_ctx_params : (Names.Id.t * CompiledModule.t) list;
    name : Names.Id.t;
    definition: Names.Id.t option;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  val context_parameters : t -> Libnames.qualid list
  val top_most_self_name : t -> Names.Id.t

  val path_substitution_elem :
    LinkageElem.t -> source:Names.Id.t -> target:Names.Id.t -> LinkageElem.t

  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t
end

and LinkageCtx : sig
  type t = Toplevel of Linkage.t | Nested of t * Linkage.t
end

module Frec_arg : sig 
   type t = 
     { name: Names.Id.t; 
       inductive: Libnames.qualid;
       motive: Constrexpr.constr_expr }
end 
