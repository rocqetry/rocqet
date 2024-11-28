open Types
open Env
open Bwd

let lookup_base context base =
  let path = Libnames.qualid_of_ident base in
  match Context.lookup (Some context) path with
  | Some linkage -> Some linkage
  | None -> (
      Inheritance.inherit_dependencies ~prefix:base;
      let elem = Inheritance.lookup_field_in_base ~field:base ~context in
      match elem with
      | Some (FamilyDefinition { linkage; _ }) -> Some linkage
      | _ -> Errors.fail ~info:"Unbound family definition")

let open_with_base ~name ~base =
  match Context.get_store () with
  | Some context ->
      let elem = lookup_base context base in
      let context = Context.get () in
      let _, parameters =
        Codegen.compile_linkage_context ~field_name:name context
      in
      let default_ctx_params =
        Codegen.compile_default_params ~context:parameters
      in
      let base =
        match elem with
        | Some linkage ->
            let linkage =
              Linkage.path_subtitution linkage
                ~source:(Naming.self_version linkage.name)
                ~target:(Naming.self_version name)
            in
            Some linkage
        | _ -> Errors.fail ~info:"Unbound family name"
      in
      let linkage =
        Linkage.
          {
            context = Bwd.of_list parameters;
            name;
            definition = None;
            base;
            (* there's not point of using the real name here? *)
            base_names = [];
            fields = Bwd.Emp;
            default_ctx_params;
            signature = None;
          }
      in
      let context = LinkageCtx.Nested (context, linkage) in
      (* We want to delay structural checks until it is "mixed in" *)
      (* Checks.check_further_binding_structure context; *)
      Context.destructive_update (Some context)
  | None ->
      let base =
        let path = Libnames.qualid_of_ident base in
        match Context.lookup None path with
        | Some linkage ->
            let linkage =
              Linkage.path_subtitution linkage
                ~source:(Naming.self_version linkage.name)
                ~target:(Naming.self_version name)
            in
            Some linkage
        | None -> Errors.fail ~info:"Unbound family name"
      in
      let linkage =
        Linkage.
          {
            context = Bwd.Emp;
            name;
            definition = None;
            base;
            base_names = [];
            fields = Bwd.Emp;
            default_ctx_params = [];
            signature = None;
          }
      in
      let context = LinkageCtx.Toplevel linkage in
      Context.destructive_update (Some context)

let open_with_base_list ~name ~(bases : Names.Id.t list) =
  match Context.get_store () with
  | Some context ->
      let base =
        bases
        |> List.map (fun base -> lookup_base context base)
        |> List.map (fun elem ->
               match elem with
               | None -> Errors.fail ~info:"Unbound family name"
               | Some elem -> elem)
        |> List.map (fun linkage ->
               Linkage.path_subtitution linkage
                 ~source:(Naming.self_version linkage.name)
                 ~target:(Naming.self_version name))
        |> Inheritance.linkages_concatenate
      in
      let context = Context.get () in
      let _, parameters =
        Codegen.compile_linkage_context ~field_name:name context
      in
      let default_ctx_params =
        Codegen.compile_default_params ~context:parameters
      in
      let linkage =
        Linkage.
          {
            context = Bwd.of_list parameters;
            name;
            definition = None;
            base = Some base;
            (* there's not point of using the real name here? *)
            base_names = [];
            fields = Bwd.Emp;
            default_ctx_params;
            signature = None;
          }
      in
      let context = LinkageCtx.Nested (context, linkage) in
      (* We want to delay structural checks until it is "mixed in" *)
      (* Checks.check_further_binding_structure context; *)
      Context.destructive_update (Some context)
  | None ->
      let paths = bases |> List.map Libnames.qualid_of_ident in
      let base =
        paths
        |> List.map (Context.lookup None)
        |> List.map (fun elem ->
               match elem with
               | None -> Errors.fail ~info:"Unbound family name"
               | Some elem -> elem)
        |> List.map (fun linkage ->
               Linkage.path_subtitution linkage
                 ~source:(Naming.self_version linkage.name)
                 ~target:(Naming.self_version name))
        |> Inheritance.linkages_concatenate
      in
      let linkage =
        Linkage.
          {
            context = Bwd.Emp;
            name;
            definition = None;
            base = Some base;
            base_names = [];
            fields = Bwd.Emp;
            default_ctx_params = [];
            signature = None;
          }
      in
      let context = LinkageCtx.Toplevel linkage in
      Context.destructive_update (Some context)

let open_trait ~name =
  match Context.get_store () with
  | Some _context ->
      let context = Context.get () in
      let _, parameters =
        Codegen.compile_linkage_context ~field_name:name context
      in
      let default_ctx_params =
        Codegen.compile_default_params ~context:parameters
      in
      let linkage =
        Linkage.
          {
            context = Bwd.of_list parameters;
            name;
            definition = None;
            base = None;
            base_names = [];
            fields = Bwd.Emp;
            default_ctx_params;
            signature = None;
          }
      in
      Context.destructive_update (Some (LinkageCtx.Nested (context, linkage)))
  | None ->
      let linkage =
        Linkage.
          {
            context = Bwd.Emp;
            name;
            definition = None;
            base = None;
            base_names = [];
            fields = Bwd.Emp;
            default_ctx_params = [];
            signature = None;
          }
      in
      Context.destructive_update (Some (LinkageCtx.Toplevel linkage))

let close_trait () =
  let context = Context.get () in
  match context with
  | LinkageCtx.Toplevel linkage ->
      Context.destructive_update None;
      Linkages.add linkage
  | LinkageCtx.Nested (upper, linkage) ->
      let signature, _ = Codegen.compile_linkage_signature linkage in
      let elem =
        let compiled_context =
          match linkage.context with
          | Bwd.Emp ->
              Errors.fail
                ~info:
                  "close_trait: Couldn't get compiled context from parameters"
          | Bwd.Snoc (_, (_, mapply)) -> Termutils.extract_functor_name mapply
        in
        let default_ctx_params =
          upper |> Context.family_linkage |> function
          | { default_ctx_params; _ } -> default_ctx_params
        in
        LinkageElem.TraitDefinition
          {
            linkage;
            compiled_context;
            compiled_signature = signature;
            default_ctx_params;
          }
      in
      Context.destructive_update (Some upper);
      Context.add_field ~name:linkage.name ~elem
