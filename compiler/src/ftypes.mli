module VernacInductive : sig 
  type t = (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list
  
  val extract_type_and_cstrs : Vernacexpr.inductive_expr -> 
        (* inductive type name * sort/kind  *)
        (Names.Id.t * Constrexpr.constr_expr option) *
         (* constr name * constructor type *)
        (Names.Id.t * Constrexpr.constr_expr) list
  val extract_all_ident : t -> Names.Id.t list  
  val extract_type_ident : t -> Names.Id.t list
  val extract_cstrs_ident : t -> Names.Id.t list
end

module FamilyId : sig
  type t = int
  val fresh : unit -> t
end

module FamilyName : sig
  type t = { name: Names.Id.t; id: FamilyId.t }
end 

module CompiledModule : sig
  type t = Libnames.qualid
end

module CompiledModuleType : sig
  type t = Libnames.qualid
end

module rec FamilyTypeElem : sig 
   type t = 
     | FInductive of 
         { original_inductive : VernacInductive.t; 
           constructor_names : Names.Id.t list;
           compiled_signature : CompiledModuleType.t; 
           compiled_impl : CompiledModule.t }
end

and FamilyType : sig
  type t =
    { name : FamilyName.t; 
      body : (Names.Id.t * FamilyTypeElem.t) list; }  
  val extend : name: Names.Id.t -> elem:FamilyTypeElem.t -> t -> t
end

and FamilyContext : sig
  type t = FamCtx of (Names.Id.t * FamilyType.t) list  
end

module rec FamilyRef : sig
  type t = ToplevelRef of Names.Id.t 
end

and FamilyTermElem : sig 
  type t =    
    | CompiledDefinition of CompiledModule.t
end

and FamilyTerm : sig 
  type t = 
    { name : Names.Id.t; 
      body : (Names.Id.t * FamilyTermElem.t) list }
end

and InhElement : sig 
  type t = 
    | CInhNew of CompiledModule.t
    | CInhExtendInh of InhJudgement.t
end

and InhJudgement : sig   
  type t = 
    { base : FamilyType.t; 
      derived : FamilyType.t; 
      body : (Names.Id.t * InhElement.t) list;
      ctx: FamilyContext.t; }
  val empty : base:FamilyType.t -> derived:FamilyType.t -> t
end

module PluginCmd : sig  
  type t = Family
end 

module PluginCmdScope : sig 
  type t = 
      { command : PluginCmd.t; 
        name : Names.Id.t; 
        close: unit -> unit; }
end 
