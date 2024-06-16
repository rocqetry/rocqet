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
    (* assert_cerror ~einfo:"Doesn't Support Inductive Parameter yet"
       (fun _ -> fst ind_params = [] && snd ind_params = None); *)
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
  let definition_mapping ~prefix ind_def =
    let all_names_with_type =
      let type_decls, constr_decls =
        ind_def |> extract_all_names_with_type |> List.split
      in
      type_decls @ List.concat constr_decls
    in
    let prefix_with_internal = Nameops.add_prefix prefix in
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

module CompiledRecursors = struct
  type t = {
    (* TODO: do we need to keep track of the context? *)
    compiled_context : CompiledModuleType.t;
    (*
      ((type_names * suffix)
      * compiled_recursor
      * (case_name * compiled_handler) list)
      list
    *)
    recursors :
      ((Names.Id.t list * string)
      * CompiledModule.t
      * (Names.Id.t * CompiledModule.t) list)
      list;
  }
end

(* Linkages *)

(* A Linkage element is the "type" of a single field in a family *)
(* I use "type" becuase it is not really a type *)
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
        body_type : Constrexpr.constr_expr;
        compiled_context : CompiledModuleType.t;
        compiled_impl : CompiledModuleType.t;
      }
    | RecursorDefinition of {
        names : Names.Id.t list;
        ind_names : Libnames.qualid list;
        recursor_module : Libnames.qualid;
        motive_module : CompiledModule.t;
        suffix : string;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
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

  val context_match : t -> t -> [ `Equal | `Less | `More ]
  val top_most_self_name : t -> Names.Id.t
  val path_subtitution : t -> source:Names.Id.t -> target:Names.Id.t -> t
  val concatenate_recursive : derived:t -> base:t -> t

  (* Linkage concatenation *)
  val concatenate : derived:t -> base:t -> t

  (* Concatenate the fields before `prefix` *)
  val concatenate_prefix : prefix:Names.Id.t -> derived:t -> base:t -> t

  val concatenate_recursive_prefix :
    prefix:Names.Id.t -> derived:t -> base:t -> t
end = struct
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

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

  let rec path_subtitution linkage ~source ~target =
    let f (name, elem) =
      let elem =
        match elem with
        | LinkageElem.FamilyDefinition family ->
            LinkageElem.FamilyDefinition
              {
                family with
                linkage = path_subtitution family.linkage ~source ~target;
              }
        | LinkageElem.InductiveDefinition definition ->
            LinkageElem.InductiveDefinition
              {
                definition with
                inductive =
                  VernacInductive.path_subtitution definition.inductive ~source
                    ~target;
              }
        | LinkageElem.FieldDefinition field -> FieldDefinition field
        | LinkageElem.RecursorDefinition definition ->
            RecursorDefinition definition
      in
      (name, elem)
    in
    let fields = linkage.fields |> Bwd.map f in
    { linkage with fields }

  (* Deep concatenation *)
  (* If the base is empty we loose some items *)
  let rec concatenate_recursive ~derived ~base =
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
          | Some (_, delem), derived -> (
              match (elem, delem) with
              | ( LinkageElem.InductiveDefinition ibase,
                  LinkageElem.InductiveDefinition iderived ) ->
                  let elem =
                    LinkageElem.InductiveDefinition
                      {
                        ibase with
                        inductive =
                          VernacInductive.concatenate ~base:ibase.inductive
                            ~derived:iderived.inductive;
                      }
                  in
                  (name, elem) :: go base derived
              | ( LinkageElem.FamilyDefinition ibase,
                  LinkageElem.FamilyDefinition iderived ) ->
                  let linkage =
                    concatenate_recursive ~base:ibase.linkage
                      ~derived:iderived.linkage
                  in
                  let elem =
                    LinkageElem.FamilyDefinition { ibase with linkage }
                  in
                  (name, elem) :: go base derived
              | FieldDefinition _, FieldDefinition _ ->
                  Errors.fail ~info:"Field name conflict"
              | _ -> Errors.fail ~info:"Wrong concatenation arguments"))
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
      | Bwd.Emp -> derived
      | Bwd.Snoc (fields, (found_name, _)) when Names.Id.equal found_name prefix
        ->
          concatenate ~base:{ base with fields } ~derived
      | Bwd.Snoc (fields, _) -> calculate_dependencies fields
    in
    calculate_dependencies base.fields

  let concatenate_recursive_prefix ~prefix ~(derived : Linkage.t)
      ~(base : Linkage.t) =
    let rec calculate_dependencies fields =
      match fields with
      | Bwd.Emp -> derived
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
  type t = Family
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
