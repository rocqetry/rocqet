open Types
open Env

let add_inductive_axiom ~name ~ty =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty = Resolver.resolve_constrexpr ~context ~expression:ty in
  let compiled_signature =
    Codegen.compile_inductive_axiom ~name ~ty ~ctx:parameters
  in
  let elem =
    LinkageElem.InductiveAxiom
      { compiled_context; compiled_signature; default_ctx_params }
  in
  (* Fake names becuase the InductiveDefinition will already
     have the names and expose then to the resolver
     too *)
  let name = Naming.inductive_axiom_name name in
  Context.add_field ~name ~elem

(* Extract the constructors *)
let constructors inductive =
  inductive |> VernacInductive.extract_all_names_with_type |> List.split |> snd
  |> List.concat

(* Extract the inductive types *)
let types inductive =
  inductive |> VernacInductive.extract_all_names_with_type |> List.split |> fst

let add_new_inductive_definition ~inductive ~inductive_name =
  Inheritance.inherit_dependencies ~prefix:inductive_name;
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive = Resolver.resolve_inductive ~context ~inductive in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:inductive_name context
  in
  let family_name = Context.family_name context in
  let compiled_signature =
    Codegen.compile_inductive_signature ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let compiled_impl, principles, mutual_principle =
    Codegen.compile_inductive_implementation ~ind_def:inductive ~ctx:parameters
      ~family_name
  in

  let recursors =
    Termutils.extract_handler_types_from_principle ~inductive ~principles
      ~mutual_principle
  in

  let elem =
    LinkageElem.InductiveDefinition
      {
        inductive;
        compiled_context;
        compiled_impl;
        compiled_signature;
        recursors;
        default_ctx_params;
      }
  in
  Context.add_field ~name:inductive_name ~elem;

  let _ =
    types inductive
    |> List.iter (fun (name, ty) -> add_inductive_axiom ~name ~ty)
  in

  let _ =
    constructors inductive
    |> List.iter (fun (name, ty) -> add_inductive_axiom ~name ~ty)
  in
  ()
(* if not (Termutils.is_indexed_inductive inductive) then
   let inductive_path = Libnames.qualid_of_ident inductive_name in
   (* Would not work for mutually inductive *)
   let handlers = constructors inductive |> List.map fst in
   Partial_recursor.add ~inductive_path ~inherited_handlers:[] ~handlers *)

let extend_inductive_definition ~inherited_inductive ~extension ~inductive_name
    =
  Inheritance.inherit_dependencies ~prefix:inductive_name;
  let inductive =
    VernacInductive.concatenate ~base:inherited_inductive ~derived:extension
  in
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive = Resolver.resolve_inductive ~context ~inductive in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:inductive_name context
  in
  let family_name = Context.family_name context in
  let compiled_signature =
    Codegen.compile_inductive_signature ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let compiled_impl, principles, mutual_principle =
    Codegen.compile_inductive_implementation ~ind_def:inductive ~ctx:parameters
      ~family_name
  in
  let recursors =
    Termutils.extract_handler_types_from_principle ~inductive ~principles
      ~mutual_principle
  in
  let elem =
    LinkageElem.InductiveDefinition
      {
        inductive;
        compiled_context;
        compiled_impl;
        compiled_signature;
        recursors;
        default_ctx_params;
      }
  in
  Context.add_field ~name:inductive_name ~elem;

  (* We only want to check the names *)
  let list_difference list1 list2 =
    List.filter_map
      (fun (name, ty) ->
        match List.assoc_opt name list2 with
        | None -> Some (name, ty)
        | Some _ -> None)
      list1
  in

  (* Inductive Axioms *)
  let _ =
    let inherited_types = types inherited_inductive in
    let new_types = list_difference (types inductive) inherited_types in

    (* Force inherit old types *)
    let _ =
      inherited_types
      |> List.map (fun (name, _) ->
             Inheritance.inherit_name ~name:(Naming.inductive_axiom_name name))
    in

    new_types |> List.iter (fun (name, ty) -> add_inductive_axiom ~name ~ty)
  in

  let inherited_constructors = constructors inherited_inductive in
  let new_constructors =
    list_difference (constructors inductive) inherited_constructors
  in
  let _ =
    (* Force inherit old constructors *)
    let _ =
      inherited_constructors
      |> List.map (fun (name, _) ->
             Inheritance.inherit_name ~name:(Naming.inductive_axiom_name name))
    in

    new_constructors
    |> List.iter (fun (name, ty) -> add_inductive_axiom ~name ~ty)
  in
  ()

(* Partial Recursors *)
(* if not (Termutils.is_indexed_inductive inductive) then
   let inductive_path = Libnames.qualid_of_ident inductive_name in
   (* Would not work for mutually inductive *)
   let handlers = new_constructors |> List.map fst in
   let inherited_handlers = inherited_constructors |> List.map fst in

   Partial_recursor.extend ~inductive_path ~inherited_handlers ~handlers *)

let add_inductive_definition inductive =
  let inductive_name = VernacInductive.extract_inductive_name inductive in
  let context = Context.get () in
  let elem = Inheritance.lookup_field_in_base ~context ~field:inductive_name in
  match elem with
  | None -> add_new_inductive_definition ~inductive ~inductive_name
  | Some (InductiveDefinition { inductive = inherited_inductive; _ }) ->
      extend_inductive_definition ~inherited_inductive ~extension:inductive
        ~inductive_name
  | Some _ ->
      Errors.fail
        ~info:"An inductive type can only be extended by another inductive type"
