open Types
open Env

(* Return the name of the compiled family field and return its compiled context's name *)
let inductive_to_famtype ~(ind_def : VernacInductive.t)
      ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
      ~family_name : CompiledModuleType.t =
  let module_name =
    let inductive_name = ind_def |> VernacInductive.extract_inductive_name in
    Naming.module_name_of ~family_name inductive_name
  in
  let module Backend = Codegen.VernacBackend in
  let all_decls =
    let type_decls, constr_decls =
      ind_def |> VernacInductive.extract_all_names_with_type |> List.split
    in
    type_decls @ List.concat constr_decls
    |> List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty)
  in  
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

(* This is the instantiation of an inductive type and it's recursors *)
let inductive_to_famterm_and_recursor_type ~(ind_def : VernacInductive.t)      
      ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
      ~family_name : CompiledModule.t =
  (* Generate a definition mapping of the inductive type and
     return the new inductive definition and the export of the correct names *)
  let modified_indcstrs, alias_all_name_term_type_decl =
    VernacInductive.definition_mapping ~prefix:"__internal_" ind_def
  in
  let module_name =
    let original_ind_name = ind_def |> VernacInductive.extract_inductive_name in
    Naming.module_name_of ~family_name original_ind_name
  in
  let open Codegen.VernacBackend in
  let module_name =
    run
    @@ define_module ~module_name ~parameters:ctx ~body:(fun _ ->
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
  let compiled_ctx, parameters =
    Codegen.compile_linkage_context ~field_name:ind_def_name context
  in  
  let family_name =
    match context with
    | LinkageCtx.Toplevel linkage
    | LinkageCtx.Nested (_, linkage) -> linkage.name
  in 
  let compiled_signature =
    inductive_to_famtype ~ind_def ~ctx:parameters ~family_name
  in
  let compiled_impl =
    inductive_to_famterm_and_recursor_type ~ind_def ~ctx:parameters
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

let concatenate_inductive ~(base : VernacInductive.t)
    ~(derived : VernacInductive.t) ~base_name ~derived_name : VernacInductive.t
    =
  let check_one_type
      ( (((_, (old_name, _)), _, _, oldcstrs), _),
        ((((_, (new_name, _)) as a), b, c, newcstrs), _) ) =
    if CAst.eq ( <> ) old_name new_name then
      Errors.fail ~info:"Name mismatch when extending inductive types.";
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
    (child_ind, [])
  in
  if List.length base <> List.length derived then
    Errors.fail ~info:"All inductive types must be specified when extending.";
  List.combine base derived |> List.map check_one_type

let extend_inductive_definition ~ind_def_name ~ind_def
    ~(inherited_elem : LinkageElem.t) =
  let context = Context.get () in
  let linkage =
    match context with
    | LinkageCtx.Toplevel linkage -> linkage
    | LinkageCtx.Nested (_, linkage) -> linkage
  in 
  let base_linkage =    
    (* Again, we should fall back on the base if there is no further binding module *)
    match context with
    | LinkageCtx.Toplevel linkage -> linkage.base
    | LinkageCtx.Nested (_, _) -> Context.further_bound context
  in 
  let base_linkage =
    match base_linkage with
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
  | LinkageElem.FamilyDefinition _ -> Errors.fail ~info:"Expected to extend an inductive type"
  | LinkageElem.InductiveDefinition { inductive; _ } ->
      let context = Context.get () in
      let linkage =
         match context with
         | LinkageCtx.Toplevel linkage -> linkage
         | LinkageCtx.Nested (_, linkage) -> linkage
      in  
      let Linkage.{ name; base; _ } = linkage in
      let base_name =
        match base with
        | None ->
           (* Also: further binding? *)
           (* Path substitution *)
           Names.Id.of_string "TODO"
        | Some base -> base.name
      in
      let complete_ind_def =
        concatenate_inductive ~base:inductive ~derived:ind_def
          ~base_name ~derived_name:name
      in
      let compiled_ctx, parameters =
        Codegen.compile_linkage_context ~field_name:ind_def_name context
      in
      let compiled_signature =
        inductive_to_famtype ~ind_def:complete_ind_def ~ctx:parameters
          ~family_name:name
      in
      let compiled_impl =
        inductive_to_famterm_and_recursor_type ~ind_def:complete_ind_def
          ~ctx:parameters ~family_name:name
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
