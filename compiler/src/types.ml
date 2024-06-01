open Bwd
open Bwd.Infix

(* A parsed vernacular inductive type *)
module VernacInductive = struct
  type t =
    (Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) list

  (* This returns (inductive type name, inductive type sort) and
                  (constructor name * consructor type)  list*)
  let extract_type_and_cstrs (inductive : Vernacexpr.inductive_expr) =
    let ind_type_name, ind_params, indtype, cstrlist = inductive in
    (* assert_cerror ~einfo:"Doesn't Support Inductive Parameter yet"
       (fun _ -> fst ind_params = [] && snd ind_params = None); *)
    let _, (ind_type_name, _) = ind_type_name in
    let ind_type_name = CAst.with_val (fun x -> x) ind_type_name in
    let each_constr ((_, (cname, cty)) : Vernacexpr.constructor_expr) =
      let cname = CAst.with_val (fun x -> x) cname in
      (cname, cty)
    in
    match cstrlist with
    | Vernacexpr.Constructors cstrlist ->
        ((ind_type_name, indtype), List.map each_constr cstrlist)
    | Vernacexpr.RecordDecl _ -> Errors.fail ~info:"Records not yet supported"

  let extract_all_names_with_type ind_def =
    ind_def
    |> List.map (fun ind -> ind |> fst |> extract_type_and_cstrs)
    |> List.map (fun ((ind_name, ty), cstrs) ->
           let ty =
             match ty with
             | None ->
                 Errors.fail
                   ~info:"You need to specify the sort of an inductive type"
             | Some ty -> ty
           in
           ((ind_name, ty), cstrs))

  let extract_inductive_names_with_sort ind_def =
    ind_def |> extract_all_names_with_type |> List.map fst

  let extract_inductive_name ind_def =
    ind_def |> extract_inductive_names_with_sort |> List.hd |> fst

  let extract_constructor_names_with_type ind_def =
    ind_def |> extract_all_names_with_type |> List.concat_map snd

  let extract_all_ident ind_def =
    let all_names =
      ind_def
      |> List.map (fun (ind_expr, _) -> ind_expr |> extract_type_and_cstrs)
    in
    let type_names = all_names |> List.map (fun x -> x |> fst |> fst) in
    let cstr_names = all_names |> List.concat_map snd |> List.map fst in
    type_names @ cstr_names

  (* Get the name of an inductive definition *)
  let extract_type_ident ind_def =
    ind_def
    |> List.map @@ fun (ind_expr, _) ->
       ind_expr |> extract_type_and_cstrs
       |> fst (* get the type name, type sort *)
       |> fst (* get just the type name *)

  (* Get the constructors in an inductive definition *)
  let extract_constructors_ident ind_def =
    ind_def
    |> List.map (fun (ind_expr, _) -> ind_expr |> extract_type_and_cstrs)
    |> List.concat_map (fun (_, cstrs) -> cstrs |> List.map fst)

  (* Create a "definition mapping" *)
  let definition_mapping ~prefix ind_def =
    let all_names_with_type =
      ind_def |> List.map (fun (ind_expr, _) -> extract_type_and_cstrs ind_expr)
    in
    let prefix_with_internal (name : Names.Id.t) =
      Nameops.add_prefix prefix name
    in
    let all_original_names =
      all_names_with_type
      |> List.concat_map (fun ((ind_name, _), cstrs) ->
             ind_name :: List.map fst cstrs)
    in
    let all_new_names = List.map prefix_with_internal all_original_names in
    let definition_mapping = List.combine all_original_names all_new_names in
    let map_name_newname =
      List.fold_right
        (fun (original_name, new_name) map ->
          Names.Id.Map.add original_name new_name map)
        definition_mapping Names.Id.Map.empty
    in
    let apply_subst_expr =
      Constrexpr_ops.replace_vars_constr_expr map_name_newname
    in
    (* TODO: Rename the variables in this function *)
    let apply_subst_inductive_expr (((a, (b, c)), d, e, f), g) =
      let b = CAst.map prefix_with_internal b in
      let e = Option.map apply_subst_expr e in
      match f with
      | Vernacexpr.Constructors csts ->
          let csts =
            List.map
              (fun (z, (x, y)) ->
                (z, (CAst.map prefix_with_internal x, apply_subst_expr y)))
              csts
          in
          let f = Vernacexpr.Constructors csts in
          (((a, (b, c)), d, e, f), g)
      | _ -> Errors.fail ~info:"Records not yet supported"
    in
    (* Use option to extract the type *)
    let all_names_with_type =
      List.concat_map
        (fun ((x, y), z) -> (x, Option.get y) :: z)
        all_names_with_type
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
        operation : InhOp.t;
      }
end =
  LinkageElem

and Linkage : sig
  type t = {
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  val concatenate : derived:t -> base:t -> t
  val concatenate_prefix : prefix:Names.Id.t -> derived:t -> base:t -> t
end = struct
  type t = {
    name : Names.Id.t;
    base : t option;
    fields : (Names.Id.t * LinkageElem.t) Bwd.t;
  }

  let concatenate ~derived ~base =
    (* This is a very naive concatenation *)
    let rec compute_difference ~base ~derived =
      match (base, derived) with
      | [], [] -> []
      | (bname, belem) :: base', (dname, delem) :: derived' ->
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
  type t = Toplevel of Linkage.t
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
