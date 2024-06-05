open Types
open Env

(* Return the name of the compiled family field and return its compiled context's name *)
let inductive_to_famtype ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModuleType.t =
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
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModule.t =
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

let add_inductive_definition inductive =
  let inductive_name = VernacInductive.extract_inductive_name inductive in
  let context = Context.get () in
  let further = Context.further_bound_linkage context in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in
  let family = Context.family_name context in
  let linkage, base_name =
    match (further, base) with
    | Some base, None | None, Some base ->
        (* Always subtitute path before concatenation *)
        let base =
          Linkage.path_subtitution base ~base:base.name ~derived:linkage.name
        in
        let prefix =
          Linkage.concatenate_prefix ~prefix:inductive_name ~derived:linkage
            ~base
        in
        (prefix, base.name)
    | None, None -> (linkage, family)
    | Some _futher, Some _base -> Errors.fail ~info:"Not yet implemented"
  in
  Context.replace ~linkage;
  let context = Context.get () in
  let further_elem =
    Context.further_bound_linkage_elem context ~field:inductive_name
  in
  let base_elem = Context.base_linkage_elem context ~field:inductive_name in
  let inductive =
    let open LinkageElem in
    match (further_elem, base_elem) with
    | Some (InductiveDefinition { inductive = base; _ }), None
    | None, Some (InductiveDefinition { inductive = base; _ }) ->
        (* Always do path subsitution before concatenation *)
        let base =
          VernacInductive.path_subtitution base ~base:base_name ~derived:family
        in
        VernacInductive.concatenate ~base ~derived:inductive
    | Some (InductiveDefinition _), Some (InductiveDefinition _) ->
        Errors.fail ~info:"Not yet implemented"
    | None, None -> inductive
    | _, _ -> Errors.fail ~info:"Expected extension with inductive type"
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:inductive_name context
  in
  let family_name = Context.family_name context in
  let compiled_signature =
    inductive_to_famtype ~ind_def:inductive ~ctx:parameters ~family_name
  in
  let compiled_impl =
    inductive_to_famterm_and_recursor_type ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let elem =
    LinkageElem.InductiveDefinition
      {
        inductive;
        compiled_context;
        compiled_impl;
        compiled_signature;
        operation = InhOp.CInhNew;
      }
  in
  Context.add_field ~name:inductive_name ~elem
