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
    let open LinkageElem in
    match (further_elem, base_elem) with
    | ( Some (further, InductiveDefinition { inductive = further_inductive; _ }),
        None ) ->
        (* Further binding *)
        let base =
          VernacInductive.path_subtitution further_inductive
            ~source:(Linkage.top_most_self_name further)
            ~target:(Linkage.top_most_self_name linkage)
        in
        VernacInductive.concatenate ~base ~derived:inductive
    | None, Some (base, InductiveDefinition { inductive = base_inductive; _ })
      ->
        (* Inheritance *)
        let base =
          VernacInductive.path_subtitution base_inductive
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
        in
        VernacInductive.concatenate ~base ~derived:inductive
    | None, None -> inductive
    | Some (_, InductiveDefinition _), Some (_, InductiveDefinition _) ->
        (* Further binding + Inheritance *)
        Errors.fail
          ~info:
            "Further binding and inheritance at the same time has not been \
             implememnted for inductive types"
    | _, _ ->
        Errors.fail
          ~info:
            "An inductive type can only be extended by another inductive type"
  in
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
