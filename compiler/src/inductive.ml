open Types
open Env

let add_inductive_definition inductive =
  let inductive_name = VernacInductive.extract_inductive_name inductive in
  let context = Context.get () in
  let linkage = Context.family_linkage context in
  let further_elem =
    Context.further_bound_linkage_elem context ~field:inductive_name
  in
  let base_elem = Context.base_linkage_elem context ~field:inductive_name in
  let inductive =
    match (further_elem, base_elem) with
    | ( Some (further, InductiveDefinition { inductive = further_inductive; _ }),
        None ) ->
        (* Further binding *)
        let further_inductive =
          VernacInductive.path_subtitution further_inductive
            ~source:(Linkage.top_most_self_name further)
            ~target:(Linkage.top_most_self_name linkage)
        in
        VernacInductive.concatenate ~base:further_inductive ~derived:inductive
    | None, Some (base, InductiveDefinition { inductive = base_inductive; _ })
      ->
        (* Inheritance *)
        let base_inductive =
          VernacInductive.path_subtitution base_inductive
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
        in
        VernacInductive.concatenate ~base:base_inductive ~derived:inductive
    | None, None -> inductive
    | ( Some (further, InductiveDefinition further_inductive),
        Some (base, InductiveDefinition base_inductive) ) ->
        (* Further binding + Inheritance *)
        let further_inductive = further_inductive.inductive in
        let further_inductive =
          VernacInductive.path_subtitution further_inductive
            ~source:(Linkage.top_most_self_name further)
            ~target:(Linkage.top_most_self_name linkage)
        in
        let base_inductive = base_inductive.inductive in
        let base_inductive =
          VernacInductive.path_subtitution base_inductive
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
        in
        let base_inductive =
          VernacInductive.concatenate ~base:further_inductive
            ~derived:base_inductive
        in
        VernacInductive.concatenate ~base:base_inductive ~derived:inductive
    | _, _ ->
        Errors.fail
          ~info:
            "An inductive type can only be extended by another inductive type"
  in
  Inheritance.inherit_dependencies ~prefix:inductive_name;
  let context = Context.get () in
  let inductive = Resolver.resolve_inductive ~context ~inductive in 
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:inductive_name context
  in
  let family_name = Context.family_name context in
  let compiled_signature =
    Codegen.compile_inductive_signature ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let compiled_impl =
    Codegen.compile_inductive_implementation ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let elem =
    LinkageElem.InductiveDefinition
      { inductive; compiled_context; compiled_impl; compiled_signature }
  in
  Context.add_field ~name:inductive_name ~elem
