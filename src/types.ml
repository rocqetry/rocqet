open Bwd
open Bwd.Infix

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
(* This should really be Names.ModPath.t *)
module CompiledModule = struct
  type t = Libnames.qualid
end

module CompiledModuleType = struct
  type t = Libnames.qualid
end

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

(* Linkages *)

(** A [LinkageElem] represents all information there is to know about afield
    in a family. This information includes compiled implemetations, signatures,
    contexts, expressions, etc. *)
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
        compiled_impl : CompiledModule.t;
      }
    (* Opaque definitions are overridable *)
    | OpaqueFieldDefinition of {
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        compiled_signature : CompiledModuleType.t;
      }
    | RecursorDefinition of {
        names : Names.Id.t list;
        motives : Constrexpr.constr_expr list;
        handler_types : (Names.Id.t * Constrexpr.constr_expr) list;
        handler_cases : (Names.Id.t * Constrexpr.constr_expr) list;
        inductive : VernacInductive.t;
        inductive_path : Libnames.qualid;
        recursor_module : Libnames.qualid;
        motive_module : CompiledModule.t;
        suffix : RecKind.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        arguments : Names.Id.t list;
        prefix : Libnames.qualid;
      }
    | PrincipleDefinition of {
        compiled_context : CompiledModuleType.t;
        inductive : VernacInductive.t;
        compiled_impl : CompiledModule.t;
        compiled_signature : CompiledModuleType.t;
      }
    | TheoremDefinition of {
        names : Names.Id.t list;
        motives : Constrexpr.constr_expr list;
        goal : Constrexpr.constr_expr;
        suffix : RecKind.t;
        inductive : VernacInductive.t;
        inductive_path : Libnames.qualid;
        handlers : (Names.Id.t * Constrexpr.constr_expr) list;
        compiled_handlers : CompiledModule.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
      }
    | MetaDataSection of {
        name : Names.Id.t;
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
      }
end =
  LinkageElem

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

  val path_substitution_elem :
    LinkageElem.t -> source:Names.Id.t -> target:Names.Id.t -> LinkageElem.t

  val concatenate_elem : LinkageElem.t -> LinkageElem.t -> LinkageElem.t
  val concatenate_recursive : derived:t -> base:t -> t

  (* Linkage concatenation *)
  val concatenate : derived:t -> base:t -> t

  (* Concatenate the fields before `prefix` *)
  val concatenate_prefix : prefix:Names.Id.t -> derived:t -> base:t -> t

  val concatenate_recursive_prefix :
    prefix:Names.Id.t -> derived:t -> base:t -> t

  val pointwise_concatenate_recursive_prefix :
    prefix:Names.Id.t -> derived:t -> base:t -> t
end = struct
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  let context_parameters linkage =
    linkage.context |> Bwd.map fst
    |> Bwd.map Libnames.qualid_of_ident
    |> Bwd.to_list

  let context_match left right =
    let left_length = Bwd.length left.context
    and right_length = Bwd.length right.context in
    if left_length < right_length then `Less
    else if left_length > right_length then `More
    else `Equal

  let top_most_self_name linkage =
    match Bwd.to_list linkage.context with
    | [] -> Naming.self_version linkage.name
    | (name, _) :: _ -> name

  let rec path_substitution_elem elem ~source ~target =
    match elem with
    | LinkageElem.MetaDataSection metadata ->
        LinkageElem.MetaDataSection metadata
    | LinkageElem.OpaqueFieldDefinition definition ->
        LinkageElem.OpaqueFieldDefinition definition
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
        let body_expr =
          Naming.replace_qualid_root ~source ~target field.body_expr
        in
        let body_type =
          field.body_type
          |> Option.map (Naming.replace_qualid_root ~source ~target)
        in
        FieldDefinition { field with body_expr; body_type }
    | LinkageElem.RecursorDefinition definition ->
        let motives =
          definition.motives
          |> List.map (Naming.replace_qualid_root ~source ~target)
        in
        let handler_types =
          definition.handler_types
          |> List.map (fun (name, e) ->
                 (name, Naming.replace_qualid_root ~source ~target e))
        in
        let handler_cases =
          definition.handler_cases
          |> List.map (fun (name, e) ->
                 (name, Naming.replace_qualid_root ~source ~target e))
        in
        RecursorDefinition
          { definition with motives; handler_types; handler_cases }
    | LinkageElem.TheoremDefinition definition ->
        let motives =
          definition.motives
          |> List.map (Naming.replace_qualid_root ~source ~target)
        in
        TheoremDefinition { definition with motives }
    | LinkageElem.PrincipleDefinition principle ->
        LinkageElem.PrincipleDefinition principle

  and path_subtitution linkage ~source ~target =
    let f (name, elem) = (name, path_substitution_elem elem ~source ~target) in
    let fields = linkage.fields |> Bwd.map f in
    { linkage with fields }

  let rec concatenate_elem elem0 elem1 =
    let remove_duplicates lst =
      let rec aux seen = function
        | [] -> []
        | hd :: tl ->
            if List.mem hd seen then aux seen tl else hd :: aux (hd :: seen) tl
      in
      aux [] lst
    in
    match (elem0, elem1) with
    | LinkageElem.RecursorDefinition e0, LinkageElem.RecursorDefinition e1 ->
        let handler_cases = e0.handler_cases @ e1.handler_cases in
        let handler_cases = remove_duplicates handler_cases in
        let handler_types = e0.handler_types @ e1.handler_types in
        let handler_types = remove_duplicates handler_types in
        LinkageElem.RecursorDefinition { e1 with handler_cases; handler_types }
    | LinkageElem.TheoremDefinition e0, LinkageElem.TheoremDefinition e1 ->
        let handler_cases = e0.handlers @ e1.handlers in
        let handlers = remove_duplicates handler_cases in
        LinkageElem.TheoremDefinition { e0 with handlers }
    | LinkageElem.InductiveDefinition e0, LinkageElem.InductiveDefinition e1 ->
        LinkageElem.InductiveDefinition
          {
            e0 with
            inductive =
              VernacInductive.concatenate ~base:e0.inductive
                ~derived:e1.inductive;
          }
    | LinkageElem.FamilyDefinition e0, LinkageElem.FamilyDefinition e1 ->
        let linkage =
          concatenate_recursive ~base:e0.linkage ~derived:e1.linkage
        in
        LinkageElem.FamilyDefinition { e0 with linkage }
    | FieldDefinition _, FieldDefinition e1 ->
        FieldDefinition e1 (* Override a field? *)
    | PrincipleDefinition _, PrincipleDefinition e1 -> PrincipleDefinition e1
    | MetaDataSection _, MetaDataSection m -> MetaDataSection m
    | _, _ -> Errors.fail ~info:"Invalid concatnenation arguments"

  (* Deep concatenation *)
  (* If the base is empty we loose some items *)
  and concatenate_recursive ~derived ~base =
    (* Using pick here reorders the fields in a family, which is wrong *)
    let rec pick x lst =
      match lst with
      | [] -> (None, [])
      | (hd, elem) :: tl ->
          if Names.Id.equal hd x then (Some (hd, elem), tl)
          else
            let result, rest = pick x tl in
            (result, (hd, elem) :: rest)
    in
    let rec go base derived =
      match base with
      | [] -> derived
      | (name, elem) :: base -> (
          match pick name derived with
          | None, _ -> (name, elem) :: go base derived
          | Some (_, delem), derived ->
              (name, concatenate_elem elem delem) :: go base derived)
    in
    let fields = go (Bwd.to_list base.fields) (Bwd.to_list derived.fields) in
    Linkage.{ derived with fields = Bwd.of_list fields }

  (* Naive concatenation *)
  let concatenate ~derived ~base =
    let rec compute_difference ~base
        ~(derived : (Names.Id.t * LinkageElem.t) list) =
      match (base, derived) with
      | [], [] -> []
      | (bname, belem) :: rest_base, (dname, _) :: rest_derived ->
          if Names.Id.equal bname dname then
            compute_difference ~base:rest_base ~derived:rest_derived
          else
            (* Check if the name has already been inherited:
               in a later position *)
            let inherited_later =
              rest_derived |> List.map fst |> List.exists (Names.Id.equal bname)
            in
            if not inherited_later then
              (bname, belem) :: compute_difference ~base:rest_base ~derived
            else compute_difference ~base:rest_base ~derived
      | _ :: _, [] -> base
      | [], _ :: _ -> []
    in
    let base_fields = base.Linkage.fields |> Bwd.to_list in
    let derived_fields = derived.Linkage.fields |> Bwd.to_list in
    let inherited_fields =
      compute_difference ~base:base_fields ~derived:derived_fields
    in
    let fields = derived.fields <@ inherited_fields in
    Linkage.{ derived with fields }

  (* Naive concatenation of the linkage before a particular field *)
  let concatenate_prefix ~prefix ~(derived : Linkage.t) ~(base : Linkage.t) =
    let rec calculate_dependencies fields =
      match fields with
      | Bwd.Emp -> concatenate ~derived ~base
      | Bwd.Snoc (fields, (found_name, _)) when Names.Id.equal found_name prefix
        ->
          concatenate ~base:{ base with fields } ~derived
      | Bwd.Snoc (fields, _) -> calculate_dependencies fields
    in
    calculate_dependencies base.fields

  let pointwise_concatenate_recursive_prefix ~prefix ~(derived : Linkage.t)
      ~(base : Linkage.t) =
    let rec extract_prefix fields =
      match fields with
      | Bwd.Emp -> fields
      | Bwd.Snoc (fields, (found_name, _)) when Names.Id.equal found_name prefix
        ->
          fields
      | Bwd.Snoc (fields, _) -> extract_prefix fields
    in
    let derived = { derived with fields = extract_prefix derived.fields } in
    let base = { base with fields = extract_prefix base.fields } in
    concatenate_recursive ~derived ~base

  let concatenate_recursive_prefix ~prefix ~(derived : Linkage.t)
      ~(base : Linkage.t) =
    let rec calculate_dependencies fields =
      match fields with
      | Bwd.Emp -> concatenate_recursive ~base ~derived
      | Bwd.Snoc (fields, (found_name, _)) when Names.Id.equal found_name prefix
        ->
          concatenate_recursive ~base:{ base with fields } ~derived
      | Bwd.Snoc (fields, _) -> calculate_dependencies fields
    in
    calculate_dependencies base.fields
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
