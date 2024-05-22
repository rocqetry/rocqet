module VernacInductive = struct 
  type t = (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list
  
  (* This returns (inductive type name, inductive type sort) and 
                  (constructor name * consructor type)  list*)
  let extract_type_and_cstrs (inductive : Vernacexpr.inductive_expr)  =
    let (ind_type_name, ind_params, indtype, cstrlist) = inductive in 
    (* assert_cerror ~einfo:"Doesn't Support Inductive Parameter yet" 
       (fun _ -> fst ind_params = [] && snd ind_params = None); *)    
    let _, (ind_type_name, _) = ind_type_name in
    let ind_type_name = CAst.with_val (fun x -> x) ind_type_name in 
    let each_constr ((_, (cname, cty)) : Vernacexpr.constructor_expr) =
      let cname = CAst.with_val (fun x -> x) cname in (cname , cty) in 
    match cstrlist with
    | Vernacexpr.Constructors cstrlist -> (ind_type_name, indtype), (List.map each_constr cstrlist)
    | Vernacexpr.RecordDecl _ ->
       (* cerror ~einfo:"Incorrect Inductive Signature" () *) 
       failwith "Records not yet supported"
  
  let extract_all_ident ind_def =     
    let all_names = 
      ind_def 
      |> List.map (fun (ind_expr, _) -> ind_expr |> extract_type_and_cstrs)
    in 
    let type_names = all_names |> List.map (fun x -> x |> fst |> fst) in
    let cstr_names = 
      all_names 
      |> List.concat_map snd
      |> List.map fst 
    in 
    type_names @ cstr_names
  
  (* Get the name of an inductive definition *)
  let extract_type_ident ind_def =
    ind_def
    |> List.map @@ fun (ind_expr, _) -> 
        ind_expr 
        |> extract_type_and_cstrs
        |> fst (* get the type name, type sort *) 
        |> fst (* get just the type name *)
        
  
  (* Get the constructors in an inductive definition *)
  let extract_cstrs_ident ind_def =    
     ind_def
     |> List.map (fun (ind_expr, _) -> ind_expr |> extract_type_and_cstrs)
     |> List.concat_map (fun (_, cstrs) -> cstrs |> List.map fst)
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

(* The name of a module that has been compiled *)
module CompiledModule = struct 
  type t = Libnames.qualid
end

module rec FamilyTypeElem : sig 
   type t = 
     | FInductive of 
         { original_inductive : VernacInductive.t; 
           constructor_names : Names.Id.t list;
           compiled_signature : CompiledModule.t; 
           compiled_impl : CompiledModule.t }
end = FamilyTypeElem

and FamilyType : sig
  type t =
    { name : FamilyName.t; 
      body : (Names.Id.t * FamilyTypeElem.t) list; }

  val extend : name: Names.Id.t -> elem:FamilyTypeElem.t -> t -> t
end = struct 
  type t =
    { name : FamilyName.t; 
      body : (Names.Id.t * FamilyTypeElem.t) list; }

  let extend ~name ~elem family_type = 
    let { body; _ } = family_type in
    { family_type with body = (name, elem) :: body }
end

(* The family context, binding names to their respective types *)
(* I suspect this is a list because we need to have nested families, 
   so the pair at the head of the list will be the current context *)
and FamilyContext : sig
  type t = FamCtx of (Names.Id.t * FamilyType.t) list  
end = struct 
  type t = FamCtx of (Names.Id.t * FamilyType.t) list
end

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
      body : (Names.Id.t * InhElement.t) list;
      ctx: FamilyContext.t; } 
  val empty : base:FamilyType.t -> derived:FamilyType.t -> t
end = struct   
  type t = 
    { base : FamilyType.t; 
      derived : FamilyType.t; 
      body : (Names.Id.t * InhElement.t) list;
      ctx: FamilyContext.t; } 
  let empty ~base ~derived = { base; derived; ctx = FamCtx []; body = [] }
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

