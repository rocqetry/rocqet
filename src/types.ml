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
    let check_one_type ((((_, (_, _)) as a), b, c, newcstrs), _) =
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
      let child_ind = (a, b, c, childcstrs) in
      (child_ind, [])
    in
    inductive |> List.map check_one_type

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
    if List.length base <> List.length derived then
      Errors.fail ~info:"All inductive types must be specified when extending.";
    List.combine base derived |> List.map check_one_type
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

module CompiledRecursor = struct
  type t = {
    inductive_names : Names.Id.t list;
    compiled_recursor : CompiledModuleType.t;
    handlers : (Names.Id.t * Constrexpr.constr_expr) list;
    compiled_handlers : (Names.Id.t * CompiledModuleType.t) list;
  }
end

module CompiledRecursors = struct
  type t = {
    (* TODO: do we need to keep track of the context? *)
    compiled_context : CompiledModuleType.t;
    recursors : CompiledRecursor.t RecursorStore.t;
  }
end

module Recursor = struct
  type t = {
      inductive_names : Names.Id.t list;
      recursor : Constrexpr.constr_expr;
      handlers : (Names.Id.t * Constrexpr.constr_expr) list;
  }  
end

(* Contains the type of the
   "rec" principle and the types
   of each handler for that particular "rec" *)
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
        default_ctx_params : CompiledModule.t list;
      }
    (* All names bound by an inductive definition:
       inductive type names and constructor names *)
    | InductiveConstr of {
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : CompiledModule.t list;
      }
    | FamilyDefinition of {
        linkage : Linkage.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        default_ctx_params : CompiledModule.t list;
      }
    | FieldDefinition of {
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        default_ctx_params : CompiledModule.t list;
      }
    (* Opaque definitions are overridable *)
    | OpaqueFieldDefinition of {
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : CompiledModule.t list;
      }
    | RecursorDefinition of {
        names : Names.Id.t list;
        handlers : Names.Id.t list;
        inductive_path : Libnames.qualid;
        suffix : RecKind.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        arguments : Names.Id.t list;
        prefix : Libnames.qualid;
        default_ctx_params : CompiledModule.t list;
      }
    | TheoremDefinition of {
        names : Names.Id.t list;        
        suffix : RecKind.t;
        inductive_path : Libnames.qualid;
        handlers : Names.Id.t list;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : CompiledModule.t list;
      }
    | ComputationalAxiom of {
        name : Names.Id.t;
        axiom : Constrexpr.constr_expr;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        default_ctx_params : CompiledModule.t list;
     }
    | MetaDataSection of {
        name : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        default_ctx_params : CompiledModule.t list;
      }
end =
  LinkageElem

and Linkage : sig
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    default_ctx_params : CompiledModule.t list;
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  val context_parameters : t -> Libnames.qualid list  
  val top_most_self_name : t -> Names.Id.t
  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t
  val path_substitution_elem :
    LinkageElem.t -> source:Names.Id.t -> target:Names.Id.t -> LinkageElem.t
end = struct
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    default_ctx_params : CompiledModule.t list;  
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
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
    match elem with
    | LinkageElem.MetaDataSection metadata ->
       LinkageElem.MetaDataSection metadata
    | LinkageElem.InductiveConstr constr ->
      LinkageElem.InductiveConstr constr
    | LinkageElem.OpaqueFieldDefinition definition ->
       LinkageElem.OpaqueFieldDefinition definition
    | LinkageElem.ComputationalAxiom comp ->
       let axiom = Naming.replace_qualid_root ~source ~target comp.axiom in
       LinkageElem.ComputationalAxiom { comp with axiom } 
    | LinkageElem.FamilyDefinition family ->
        let g (name, expr) =
          if Names.Id.equal source name then (target, expr) else (name, expr)
        in
        let context = family.linkage.context |> Bwd.map g in
        let linkage =
          { (path_subtitution family.linkage ~source ~target) with context }
        in
        LinkageElem.FamilyDefinition { family with linkage }
    | LinkageElem.InductiveDefinition definition ->
        LinkageElem.InductiveDefinition
          {
            definition with
            inductive =
              VernacInductive.path_subtitution definition.inductive ~source
                ~target;
          }
    | LinkageElem.FieldDefinition field ->        
        FieldDefinition field
    | LinkageElem.RecursorDefinition definition ->                
        RecursorDefinition definition          
    | LinkageElem.TheoremDefinition definition ->        
        TheoremDefinition definition

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
  type t = Family | Recursion | Induction | MetaData | Lemma
end

(* A scope is a plugin command enriched with a name and a "closing" handler *)
(* `close` is a generic handle that is called to close the scope *)
module PluginCmdScope = struct
  type t = { command : PluginCmd.t; name : Names.Id.t; close : unit -> unit }
end

(* Does a field exends a field in the base family? *)
module FieldInhKind = struct
  type t = New | Extend of LinkageElem.t
end
