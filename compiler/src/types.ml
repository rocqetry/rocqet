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

  let extract_inductive_name ind_def =
    let (type_name, _), _ = ind_def |> extract_all_names_with_type |> List.hd in
    type_name

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
          Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) =
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
end


(* Module naming *)
(* This should really be Names.ModPath.t *)
module CompiledModule = struct
  type t = Libnames.qualid
end

module CompiledModuleType = struct
  type t = Libnames.qualid
end

(* Linkages *)
module InhOp = struct
  type t = CInhNew | CInhExtend | CInhInherit
end

(* A Linkage element is the "type" of a single field in a family *)
(* I use "type" becuase it is not really a type *)
module rec LinkageElem : sig
  type t =
    | InductiveDefinition of {
        inductive : VernacInductive.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
            (** `operation` describes how a field is transformed from the base family 
             to the derived family. If there is no base family it is just InhOp.CInhNew,
             otherwise it describes the nature of the transformation of a field from 
             the base family to the derived family *)
        operation : InhOp.t;
      }
    | FamilyDefinition of {
        linkage : Linkage.t;
        compiled_context : CompiledModuleType.t;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
      }
end =
  LinkageElem

and Linkage : sig
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    compiled_context : CompiledModuleType.t option;
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }  
  
  (* Linkage concatenation *)
  val concatenate : derived:t -> base:t -> t

  (* Concatenate the fields before `prefix` *)
  val concatenate_prefix : prefix:Names.Id.t -> derived:t -> base:t -> t
end = struct
  type t = {
    context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
    compiled_context : CompiledModuleType.t option;
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  let concatenate ~derived ~base =
    (* This is a very naive concatenation *)
    let rec compute_difference ~base ~derived =
      match (base, derived) with
      | [], [] -> []
      | (bname, belem) :: base', (dname, _) :: derived' ->
          if Names.Id.equal bname dname then
            compute_difference ~base:base' ~derived:derived'
          else
            (* Since this element is inherited, it should have InhOp.CInhInherit *)
            (* let belem = LinkageElem.{ belem with in  *)
            (bname, belem) :: compute_difference ~base:base' ~derived
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

  let concatenate_prefix ~prefix ~(derived : Linkage.t) ~(base : Linkage.t) =
    let rec calculate_dependencies fields =
      match fields with
      | Bwd.Emp -> Bwd.Emp
      | Bwd.Snoc (fields, (found_name, _)) when Names.Id.equal found_name prefix
        ->
          (* Remove the fields in the that have already been extended by the derived family *)
          (* Here we could use the previous concatenate *)
          fields
          |> Bwd.filter (fun (name, _) ->
                 derived.fields |> Bwd.map fst
                 |> Bwd.exists (Names.Id.equal name)
                 |> not)
      | Bwd.Snoc (fields, _) -> calculate_dependencies fields
    in
    let inherited_fields = calculate_dependencies base.fields in
    let fields = inherited_fields <@ Bwd.to_list derived.fields in
    { derived with fields }
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
