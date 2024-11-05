open Bwd

(* A parsed vernacular inductive type *)
module VernacInductive = struct
  type t =
    (Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) list

  (* This returns (inductive type name, inductive type sort) and
                  (constructor name * consructor type)  list*)
  let extract_type_and_cstrs (inductive : Vernacexpr.inductive_expr) =
    let ( (_coercion_flag, (ind_type_name, _cumul_univ_decl)),
          _ind_params,
          ind_type,
          cstrlist ) =
      inductive
    in
    let each_constr ((_flags, (cname, cty)) : Vernacexpr.constructor_expr) =
      (cname.v, cty)
    in
    match cstrlist with
    | Vernacexpr.Constructors cstrlist ->
        ((ind_type_name.v, ind_type), List.map each_constr cstrlist)
    | Vernacexpr.RecordDecl _ -> Errors.fail ~info:"Records not yet supported"

  (* name -> name list *)
  (* inductive name -> constructors *)
  let create_inductive_constructor_map (inductive : t) =
    inductive
    |> List.map fst
    |> List.map extract_type_and_cstrs
    |> List.map (fun ((inductive_name, _), constructors) -> inductive_name, List.map fst constructors)
    |> Names.Id.Map.of_list

  let extract_all_constructors inductive =
    inductive       
       |> create_inductive_constructor_map
       |> Names.Id.Map.bindings |> List.concat_map snd 

  let extract_all_names_with_type ind_def =
    ind_def
    |> List.map (fun (ind, _) -> ind |> extract_type_and_cstrs)
    |> List.map (fun ((ind_name, ty), cstrs) ->
           let ty =
             match ty with
             | None ->
                 Errors.fail
                   ~info:"You need to specify the sort of an inductive type"
             | Some ty -> ty
           in
           ((ind_name, ty), cstrs))

  let extract_all_names ind_def =
    ind_def
    |> List.map (fun (ind, _) -> ind |> extract_type_and_cstrs)
    |> List.map (fun ((ind_name, _), cstrs) -> (ind_name, List.map fst cstrs))

  let extract_inductive_name ind_def =
    ind_def |> extract_all_names |> List.hd |> fst

  let extract_all_inductive_names inductive =
    inductive |> extract_all_names |> List.map fst 

  (* Create a "definition mapping" *)
  let definition_mapping ind_def =
    let all_names_with_type =
      let type_decls, constr_decls =
        ind_def |> extract_all_names_with_type |> List.split
      in
      type_decls @ List.concat constr_decls
    in
    let prefix_with_internal = Naming.internal_name in
    let apply_subst_expr =
      let all_original_names = all_names_with_type |> List.map fst in
      let map_name_newname =
        Naming.name_map_with prefix_with_internal all_original_names
      in
      Constrexpr_ops.replace_vars_constr_expr map_name_newname
    in
    let apply_subst_inductive_expr
        (( ( (coercion_flag, (ind_type_name, cumul_univ_decl)),
             ind_params,
             ind_type,
             csts ),
           decl_notations ) :
          Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) :
        Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list =
      let ind_type_name = CAst.map prefix_with_internal ind_type_name in
      let ind_type = Option.map apply_subst_expr ind_type in
      match csts with
      | Vernacexpr.Constructors csts ->
          let csts =
            csts
            |> List.map (fun (flags, (cst_name, cst_type)) ->
                   ( flags,
                     ( CAst.map prefix_with_internal cst_name,
                       apply_subst_expr cst_type ) ))
          in
          let csts = Vernacexpr.Constructors csts in
          ( ( (coercion_flag, (ind_type_name, cumul_univ_decl)),
              ind_params,
              ind_type,
              csts ),
            decl_notations )
      | _ -> Errors.fail ~info:"Records not yet supported"
    in
    (* Exporting the names *)
    let alias_all_name_term_type_decl =
      List.map
        (fun (name, ty) ->
          (name, Constrexpr_ops.mkIdentC (prefix_with_internal name), ty))
        all_names_with_type
    in
    let modified_ind_def = List.map apply_subst_inductive_expr ind_def in
    (modified_ind_def, alias_all_name_term_type_decl)

  (* base -> derived *)
  let path_subtitution (inductive : t) ~source ~target =
    let check_one_type (((u, paramty, tyty, newcstrs): Vernacexpr.inductive_expr), _) =
      let childcstrs =
        match newcstrs with
        | Vernacexpr.Constructors constr ->
            (* The right self_names should be passed to us *)
            (* let base_name = Naming.self_version base in
               let derived_name = Naming.self_version derived in*)
            let base_constr_renamed =
              Naming.rename_ind_constructors constr ~base_name:source
                ~derived_name:target
            in
            Vernacexpr.Constructors base_constr_renamed
        | _ -> Errors.fail ~info:"Record types are not yet supported"
      in
      let tyty = tyty |> Option.map (Naming.replace_qualid_root ~source ~target) in
      let child_ind = (u, paramty, tyty, childcstrs) in
      (child_ind, [])
    in
    inductive |> List.map check_one_type

  let inductive_expr_name (expr : Vernacexpr.inductive_expr) = 
    let ( (_coercion_flag, (ind_type_name, _cumul_univ_decl)),
          _ind_params,
          _ind_type,
          _cstrlist ) =
      expr
    in
    ind_type_name.v  

  let concatenate ~(base : t) ~(derived : t) : t =
    let remove_duplicates lst =
      let rec aux seen = function
        | [] -> []
        | hd :: tl ->
            if List.mem hd seen then aux seen tl else hd :: aux (hd :: seen) tl
      in
      aux [] lst
    in
    let check_one_type
        ( (((_, (old_name, _)), _, _, oldcstrs), _),
          ((((_, (new_name, _)) as a), b, c, newcstrs), _) ) =
      if CAst.eq ( <> ) old_name new_name then
        Errors.fail ~info:"Name mismatch when extending inductive types.";
      let childcstrs =
        match (oldcstrs, newcstrs) with
        | ( Vernacexpr.Constructors base_constr,
            Vernacexpr.Constructors derived_constr ) ->
            Vernacexpr.Constructors
              (remove_duplicates (base_constr @ derived_constr))
        | _, _ -> Errors.fail ~info:"Record types are not yet supported"
      in
      let child_ind = (a, b, c, childcstrs) in
      (child_ind, [])
    in
    let combine (lefts : t) (rights : t) = 
      lefts
      |> List.map (fun ((b, _)as base) ->         
         let result = 
           rights
           |> List.find_opt (fun (d, _) -> 
                  Names.Id.equal (inductive_expr_name d) 
                    (inductive_expr_name b)) 
         in 
         match result with 
         | None -> base 
         | Some derived -> check_one_type (base, derived))      
    in
    let combined = combine base derived in  
    let combined_names = combined |> List.map (fun (e, _) -> inductive_expr_name e) in
    let _ = 
      combined_names |> List.iter (fun n -> Printf.printf "Comb: %s\n" (Names.Id.to_string n))
    in    

    let rest =       
      derived |> List.filter (fun (r, _) ->         
        match combined_names |> List.find_opt (fun l -> Names.Id.equal l (inductive_expr_name r)) with 
        | None -> true
        | Some _ -> false)
    in    
    combined @ rest    

  let lookup_inductive_name ~constructor ~inductive =
    let result = 
      inductive
      |> List.map fst
      |> List.map extract_type_and_cstrs
      |> List.find_map (fun ((inductive_name, _), constructors) ->
             let constructors = List.map fst constructors in
             if List.exists (Names.Id.equal constructor) constructors then
               Some inductive_name
             else None)
    in
    match result with
    | None -> Errors.fail ~info:"constructor not bound in any inductive"
    | Some result -> result
    
end

(* Module naming *)
module CompiledModule = struct
  type t = Libnames.qualid
end

module CompiledModuleType = struct
  type t = Libnames.qualid
end

(*
module Path = struct
  type t = Libnames.qualid
end
*)

module RecKind = struct
  type t = Ind | IndComplete | Rec | Rect

  let compare r1 r2 =
    match (r1, r2) with
    | Ind, Ind -> 0
    | IndComplete, IndComplete -> 0
    | Rec, Rec -> 0
    | Rect, Rect -> 0
    | _ -> -1

  let to_string = function
    | Ind -> "_ind"
    | IndComplete -> "_ind_comp"
    | Rec -> "_rec"
    | Rect -> "_rect"

  let of_string = function
    | "_ind" -> Ind
    | "_ind_comp" -> IndComplete
    | "_rec" -> Rec
    | "_rect" -> Rect
    | _ -> Errors.fail ~info:"Unknown RecKind"

  let of_name name = name |> Names.Id.to_string |> of_string
end

module RecursorStore = Map.Make (RecKind)

(* TODO: rethink keeping the big recursor *)
module MutualRecursor = struct
  type t = {
    mutual_recursor : Constrexpr.constr_expr;
    mutual_handlers : (Names.Id.t * Constrexpr.constr_expr) list;
    }
end

module Recursor = struct
  type t = {    
    recursors : Constrexpr.constr_expr Names.Id.Map.t;
    handlers : (Names.Id.t * Constrexpr.constr_expr) list Names.Id.Map.t;    
    mutual : MutualRecursor.t option;
  }
end

(* Contains the type of the
   "rec" principle and the types
   of each handler for that particular "rec" *)
(* map from inductive to the "separate big" principle *)
module Recursors = struct
  type t = Recursor.t RecursorStore.t
end

(* Linkages *)

(** A [LinkageElem] represents all information there is to know about afield
    in a family. This information includes compiled implemetations, signatures,
    contexts, expressions, etc. *)
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
    (* All names bound by an inductive definition:
       inductive type names and constructor names, as 
       parameters in the context *)
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
        compiled_impl : CompiledModule.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    (* Opaque definitions are overridable *)
    | OpaqueFieldDefinition of {
        type_name : Names.Id.t;
        compiled_context : CompiledModuleType.t;        
        compiled_impl : CompiledModule.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
    | RecursorDefinition of {
        names : Names.Id.t list;
        (* inductive_name to handlers *)
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
        (* Might include some handlers that are inherited, 
           but needed to calculate the right arguments to the prect *)
        handlers: Names.Id.t list;
        (* The handlers actually defined with "some" in this extension
           It is important for fdicriminate to know this. *)
        defining_handlers : Names.Id.t list;
        (* constructor name, computational axiom name *)
        behaviour: (Names.Id.t * Names.Id.t) list;
        prec_suffix : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;        
        default_ctx_params : (Names.Id.t * CompiledModule.t) list;
      }
end =
  LinkageElem

and Linkage : sig
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    default_ctx_params : (Names.Id.t * CompiledModule.t) list;
    (* TODO: This should be a Libnames.qualid *)
    name : Names.Id.t;
    definition: Names.Id.t option;
    (* currently base is a concatenation of further binding bases 
       and normal basses *)
    base : t option; 
    base_names : Names.Id.t list;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
    signature : CompiledModuleType.t option;
  }

  (* TODO: Some of these are not needed and some should be moved to
     inheritance.ml *)
  val context_parameters : t -> Libnames.qualid list
  val top_most_self_name : t -> Names.Id.t
  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t

  val path_substitution_elem :
    LinkageElem.t -> source:Names.Id.t -> target:Names.Id.t -> LinkageElem.t
end = struct
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    default_ctx_params : (Names.Id.t * CompiledModule.t) list;
    name : Names.Id.t;
    definition: Names.Id.t option;
    base : t option;
    base_names : Names.Id.t list;    
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
    signature : CompiledModuleType.t option;
  }

  let context_parameters linkage =
    linkage.context |> Bwd.map fst
    |> Bwd.map Libnames.qualid_of_ident
    |> Bwd.to_list

  let top_most_self_name linkage =
    match Bwd.to_list linkage.context with
    | [] -> Naming.self_version linkage.name
    | (name, _) :: _ -> name

  let rec path_substitution_elem elem ~source ~target =      
    let g (name, expr) =
          if Names.Id.equal source name then (target, expr) else (name, expr)
    in
    let path_subst_ctx ctx = 
      ctx |> List.map g
    in 
    match elem with
    | LinkageElem.MetaDataSection metadata ->
        let default_ctx_params = path_subst_ctx metadata.default_ctx_params in
        LinkageElem.MetaDataSection { metadata with default_ctx_params }
    | ClosingFact fact -> 
       let default_ctx_params = path_subst_ctx fact.default_ctx_params in
       ClosingFact { fact with default_ctx_params }
    | PartialRecursor prec -> 
       let default_ctx_params = path_subst_ctx prec.default_ctx_params in
       PartialRecursor { prec with default_ctx_params }
    | InductiveAxiom axiom -> 
       let default_ctx_params = path_subst_ctx axiom.default_ctx_params in
       InductiveAxiom { axiom with default_ctx_params } 
    | OpaqueFieldDefinition definition ->
        let default_ctx_params = path_subst_ctx definition.default_ctx_params in
        OpaqueFieldDefinition { definition with default_ctx_params; }
    | ComputationalAxiom comp ->
        let axiom = Naming.replace_qualid_root ~source ~target comp.axiom in
        let default_ctx_params = path_subst_ctx comp.default_ctx_params in
        ComputationalAxiom { comp with axiom; default_ctx_params }
    | FamilyDefinition family ->        
        let context = family.linkage.context |> Bwd.map g in
        let linkage =
          { (path_subtitution family.linkage ~source ~target) with context }
        in
        let default_ctx_params = path_subst_ctx family.default_ctx_params in
        FamilyDefinition { family with linkage; default_ctx_params }
    | TraitDefinition trait -> 
       let context = trait.linkage.context |> Bwd.map g in
        let linkage =
          { (path_subtitution trait.linkage ~source ~target) with context }
        in
        let default_ctx_params = path_subst_ctx trait.default_ctx_params in
        TraitDefinition { trait with linkage; default_ctx_params }
    | InductiveDefinition definition ->
       let default_ctx_params = path_subst_ctx definition.default_ctx_params in
       (* TODO: refactor out. Path sustitution on recursors *)
       let recursors =
         definition.recursors
         |> RecursorStore.map (fun (r: Recursor.t) ->
                let recursors = r.recursors |> Names.Id.Map.map (Naming.replace_qualid_root ~source ~target) in
                let handlers =
                  r.handlers
                  |> Names.Id.Map.map (List.map (fun (n, e) -> (n, Naming.replace_qualid_root ~source ~target e)))
                in
                let mutual =
                  r.mutual
                  |> Option.map (fun (m : MutualRecursor.t) ->
                       let mutual_recursor = Naming.replace_qualid_root ~source ~target m.mutual_recursor in
                       let mutual_handlers = m.mutual_handlers |> List.map (fun (n, e) -> (n, Naming.replace_qualid_root ~source ~target e)) in
                       MutualRecursor.{ mutual_recursor; mutual_handlers } )
                in 
              Recursor.{ recursors; handlers; mutual } )
       in
       InductiveDefinition
          {
            definition with
            recursors;
            default_ctx_params;
            inductive =
              VernacInductive.path_subtitution definition.inductive ~source
                ~target;
          }
    | FieldDefinition field -> 
       let default_ctx_params = path_subst_ctx field.default_ctx_params in
       FieldDefinition { field with default_ctx_params; }
    | RecursorDefinition definition -> 
       let default_ctx_params = path_subst_ctx definition.default_ctx_params in
       RecursorDefinition { definition with default_ctx_params }
    | TheoremDefinition definition -> 
       let default_ctx_params = path_subst_ctx definition.default_ctx_params in
       TheoremDefinition { definition with default_ctx_params }

  and path_subtitution linkage ~source ~target =
    let f (name, elem) = (name, path_substitution_elem elem ~source ~target) in
    let fields = linkage.fields |> Bwd.map f in
    { linkage with fields }
end

(* A linkage we are currently constructing *)
and LinkageCtx : sig
  type t = Toplevel of Linkage.t | Nested of t * Linkage.t
end =
  LinkageCtx

(* I think this can be merged with LinkageCtx *)
(* A single plugin command *)
(* e.g Family A. ... *)
module PluginCmd = struct
  type t = Family | Recursion | Induction | MetaData | Lemma | Trait
end

(* A scope is a plugin command enriched with a name and a "closing" handler *)
(* `close` is a generic handle that is called to close the scope *)
module PluginCmdScope = struct
  type t = { command : PluginCmd.t; names : Names.Id.t list; close : unit -> unit }
end

module Frec_arg = struct  
   type t = 
     { name: Names.Id.t; 
       inductive: Libnames.qualid;
       motive: Constrexpr.constr_expr }
end
