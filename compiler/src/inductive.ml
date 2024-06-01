open Types
open Env

(* Return the name of the compiled family field and return its compiled context's name *)
let inductive_to_famtype ~(ind_def : VernacInductive.t)
    ~(ctx : CompiledModuleType.t) ~family_name : CompiledModuleType.t =
  let inductive_name = ind_def |> VernacInductive.extract_inductive_name in
  let type_decls =
    ind_def |> VernacInductive.extract_inductive_names_with_sort
  in
  let constr_decls =
    ind_def |> VernacInductive.extract_constructor_names_with_type
  in
  let module_name =
    let prefix =
      inductive_name
      |> Nameops.add_prefix (Names.Id.to_string family_name)
      |> Names.Id.to_string
    in
    Naming.fresh_name ~prefix
  in
  let module Backend = Codegen.VernacBackend in
  let declare_typedecls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) type_decls
  in
  let declare_csts_decls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) constr_decls
  in
  let all_decls = declare_typedecls @ declare_csts_decls in
  let parameters =
    [ (Naming.self_version family_name, Termutils.ident_to_module_expr ctx) ]
  in
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name ~parameters ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

(* This is the instantiation of an inductive type and it's recursors *)
let inductive_to_famterm_and_recursor_type ~(ind_def : VernacInductive.t)
    ~(ctx : CompiledModuleType.t) ~family_name : CompiledModule.t =
  let original_ind_name = ind_def |> VernacInductive.extract_inductive_name in
  (* Generate a definition mapping of the inductive type and
     return the new inductive definition and the export of the correct names *)
  let modified_indcstrs, alias_all_name_term_type_decl =
    VernacInductive.definition_mapping ~prefix:"__internal_" ind_def
  in
  let module_name =
    let name =
      Nameops.add_prefix (Names.Id.to_string family_name) original_ind_name
    in
    Naming.fresh_name ~prefix:(name |> Names.Id.to_string)
  in
  let open Codegen.VernacBackend in
  let parameters =
    [ (Naming.self_version family_name, Termutils.ident_to_module_expr ctx) ]
  in
  let module_name =
    run
    @@ define_module ~module_name ~parameters ~body:(fun _ ->
           let* () = define_inductive modified_indcstrs in
           let alias_all =
             List.map
               (fun (original_name, new_name, ty) ->
                 define_term ~name:original_name ~expr:new_name ~ty)
               alias_all_name_term_type_decl
           in
           let* _ = flatmap alias_all in
           return ())
  in
  module_name

let declare_inductive_definition ~(ind_def_name : Names.Id.t)
    ~(ind_def : VernacInductive.t) =
  let context = Context.get () in
  let compiled_ctx =
    Codegen.compile_linkage_context ~field_name:ind_def_name context
  in
  let (LinkageCtx.Toplevel linkage) = context in
  let family_name = linkage.Linkage.name in
  let compiled_signature =
    inductive_to_famtype ~ind_def ~ctx:compiled_ctx ~family_name
  in
  let compiled_impl =
    inductive_to_famterm_and_recursor_type ~ind_def ~ctx:compiled_ctx
      ~family_name
  in
  let elem =
    LinkageElem.InductiveDefinition
      {
        inductive = ind_def;
        compiled_context = compiled_ctx;
        compiled_impl;
        compiled_signature;
        operation = InhOp.CInhNew;
      }
  in
  Context.add_field ~name:ind_def_name ~elem

let check_extended_inductive_compatible ~(base : VernacInductive.t)
    ~(derived : VernacInductive.t) ~base_name ~derived_name : VernacInductive.t
    =
  let base = base |> List.hd in
  (* No mutual inductive types *)
  let derived = derived |> List.hd in

  (* No mutual indcutive types *)
  let _, _, _, oldcstrs = fst base in
  let a, b, c, newcstrs = fst derived in
  let childcstrs =
    match (oldcstrs, newcstrs) with
    | ( Vernacexpr.Constructors base_constr,
        Vernacexpr.Constructors derived_constr ) ->
        let base_name = Naming.self_version base_name in
        let derived_name = Naming.self_version derived_name in
        let base_constr_renamed =
          Naming.rename_ind_constructors base_constr ~base_name ~derived_name
        in
        Vernacexpr.Constructors (base_constr_renamed @ derived_constr)
    | _, _ -> Errors.fail ~info:"Record types are not yet supported"
  in
  let child_ind = (a, b, c, childcstrs) in
  let child_ind_def = [ (child_ind, []) ] in
  child_ind_def

let extend_inductive_definition ~ind_def_name ~ind_def
    ~(inherited_elem : LinkageElem.t) =
  let (LinkageCtx.Toplevel linkage) = Context.get () in
  let base_linkage =
    match linkage.base with
    | None ->
        Errors.fail
          ~info:"There needs to be a base family to extend an inductive type"
    | Some base_linkage -> base_linkage
  in
  let linkage =
    Linkage.concatenate_prefix ~prefix:ind_def_name ~derived:linkage
      ~base:base_linkage
  in
  Context.replace ~linkage;
  match inherited_elem with
  | LinkageElem.InductiveDefinition { inductive; compiled_signature; _ } ->
      let context = Context.get () in
      let (LinkageCtx.Toplevel linkage) = context in
      let Linkage.{ name; fields; base; _ } = linkage in
      let base =
        match base with
        | None -> Errors.fail ~info:"Should not happen"
        | Some base -> base
      in
      let complete_ind_def =
        check_extended_inductive_compatible ~base:inductive ~derived:ind_def
          ~base_name:base.name ~derived_name:name
      in
      let compiled_ctx =
        Codegen.compile_linkage_context ~field_name:ind_def_name context
      in
      let compiled_signature =
        inductive_to_famtype ~ind_def:complete_ind_def ~ctx:compiled_ctx
          ~family_name:name
      in
      let compiled_impl =
        inductive_to_famterm_and_recursor_type ~ind_def:complete_ind_def
          ~ctx:compiled_ctx ~family_name:name
      in
      let elem =
        LinkageElem.InductiveDefinition
          {
            inductive = complete_ind_def;
            compiled_context = compiled_ctx;
            compiled_impl;
            compiled_signature;
            operation = InhOp.CInhNew;
          }
      in
      Context.add_field ~name:ind_def_name ~elem

let add_inductive_definition ind_def =
  let ind_def_name = ind_def |> VernacInductive.extract_inductive_name in
  match Inheritance.infer_field_inh_kind ind_def_name with
  | FieldInhKind.New -> declare_inductive_definition ~ind_def_name ~ind_def
  | FieldInhKind.Extend inherited_elem ->
      extend_inductive_definition ~ind_def_name ~ind_def ~inherited_elem
