open Types
open Env

let add_inductive_definition inductive =
  let inductive_name = VernacInductive.extract_inductive_name inductive in
  let context = Context.get () in
  let linkage = Context.family_linkage context in
  let elem =
    Inheritance.inherit_element ~linkage ~context ~field:inductive_name
  in
  let inductive =
    match elem with
    | None -> inductive
    | Some (InductiveDefinition { inductive = inherited_inductive; _ }) ->
        VernacInductive.concatenate ~base:inherited_inductive ~derived:inductive
    | Some _ ->
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
  let compiled_impl, recursors =
    Codegen.compile_inductive_implementation ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let compiled_recursors =
    ref CompiledRecursors.{ compiled_context; recursors = RecursorStore.empty }
  in
  let elem =
    LinkageElem.InductiveDefinition
      {
        inductive;
        compiled_context;
        compiled_impl;
        compiled_signature;
        compiled_recursors;
      }
  in
  Context.add_field ~name:inductive_name ~elem;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:inductive_name context
  in
  let compiled_recs =
    Codegen.compile_recursors ~ind_def:inductive ~recursors ~ctx:parameters
      ~family_name
  in
  (compiled_recursors :=
     CompiledRecursors.{ compiled_context; recursors = compiled_recs });
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:inductive_name context
  in
  let principle_signature =
    Codegen.compile_principle_signature ~ind_def:inductive ~recursors
      ~ctx:parameters ~family_name
  in
  let principle_impl = Codegen.compile_principle_implementation parameters in
  let principle =
    LinkageElem.PrincipleDefinition
      {
        compiled_context;
        inductive;
        compiled_signature = principle_signature;
        compiled_impl = principle_impl;
      }
  in
  let name = Nameops.add_suffix inductive_name "IndPrinciple" in
  Context.add_field ~name ~elem:principle
