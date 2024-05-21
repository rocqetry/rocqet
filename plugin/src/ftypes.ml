(* Contains only type definitions used around the plugins *)
module VernacInductive = struct 
  type t = (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list
end

module FamilyId = struct 
  type t = int
  let fresh =
    let store = ref 0 in
    fun () -> incr store; !store    
end

module FamilyName = struct 
  type t = { name: Names.Id.t; id: FamilyId.t }
end

(* A module we have compiled *)
module CompiledModule = struct 
  type t = Libnames.qualid
end 

(* The type of an "element" in a family type *)
module rec FamilyTypeElem : sig 
   type t = 
     | FInductive of 
         { original_inductive : VernacInductive.t; 
           constructor_names : Names.Id.t list;
           compiled_signature : CompiledModule.t; 
           complied_impl : CompiledModule.t }
end = FamilyTypeElem

(* The type of a family *)
and FamilyType : sig
  type t =
    { name : FamilyName.t; 
      body : (Names.Id.t * FamilyTypeElem.t) list; }
end = FamilyType

(* The family context, binding names to their respective types *)
(* I suspect this is a list because we need to have nested families, 
   so the pair at the head of the list will be the current context *)
and FamilyContext : sig
  type t = FamCtx of (Names.Id.t * FamilyType.t) list
end = FamilyContext

module rec FamilyRef : sig
  type t = ToplevelRef of Names.Id.t 
end = FamilyRef

and FamilyTermElem : sig 
  type t =    
    | CompiledDefinition of CompiledModule.t
end = FamilyTermElem

and FamilyTerm : sig 
  type t = 
    { name : Names.Id.t; 
      body : (Names.Id.t * FamilyTermElem.t) list }
end = FamilyTerm

and InhElement : sig 
  type t = 
    | CInhNew of CompiledModule.t
    | CInhExtendInh of InhJudgement.t
end = InhElement

and InhJudgement : sig 
  type t = 
    { base : FamilyType.t; 
      derived : FamilyType.t; 
      body : (Names.Id.t * InhElement.t) list; } 
  val empty : base:FamilyType.t -> derived:FamilyType.t -> t
end = struct   
  type t = 
    { base : FamilyType.t; 
      derived : FamilyType.t; 
      body : (Names.Id.t * InhElement.t) list; } 
  let empty ~base ~derived = { base; derived; body = [] }
end

(* A single plugin command *)
(* e.g Family A. ... *)
module PluginCmd = struct 
  type t = Family
end

(* A scope is a plugin command enriched with a name and a "closing" handler *)
(* `close` is a generic handle that is called to close the scope *)
module PluginCmdScope = struct 
  type t = 
      { command : PluginCmd.t; 
        name : Names.Id.t;        
        close: unit -> unit; }
end

(*
module NestedFamilyContext = struct 
  type t = 
    | Top of FamilyContext.t
    | Level of FamilyContext.t * t
end

(* Field inheritance kind *)
module FieldInheritanceKind = struct 
  type t = New | Extend
end

module FamilyDefinitionContext = struct 
  type t =
    | InitialInhBase of Family.Ref.t option (* A toplevel family *)
end


(* Try to integrate Logs library for logging *)
(* Log to file, Log to output *)



(* inherits_all_remained *)
(* close_current_inh_judgement *)
(* ontopinh *)
(* inhnewind *)

*)

