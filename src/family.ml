open Types
open Env
open Bwd

let open_family name =
  match Context.get_store () with
  | Some _context ->
      (* Inherit dependencies *)
      Inheritance.inherit_dependencies ~prefix:name;
      let context = Context.get () in
      let _, parameters =
        Codegen.compile_linkage_context ~field_name:name context
      in
      let default_ctx_params =
        Codegen.compile_default_params
          ~context:parameters
      in
      let elem = Inheritance.lookup_field_in_base ~field:name ~context in
      let base =
        match elem with
        | Some (LinkageElem.FamilyDefinition { linkage = further; _ }) -> Some further
        | Some _ -> Errors.fail ~info:"Expected a family linkage element"
        | None -> None
      in 
      let linkage =
        Linkage.
          {
            context = Bwd.of_list parameters;
            name;
            base;
            fields = Bwd.Emp;
            default_ctx_params
          }
      in            
      (* Check further binding structure? *)      
      Context.destructive_update (Some (LinkageCtx.Nested (context, linkage)))
  | None ->
      let linkage =
        Linkage.
          {
            context = Bwd.Emp;
            name;
            base = None;
            fields = Bwd.Emp;
            default_ctx_params = []
          }
      in
      Context.destructive_update (Some (LinkageCtx.Toplevel linkage))

let open_family_with_base ~name ~base =
  let context = Context.get_store () in
  match Context.lookup context base with
  | None -> Errors.fail ~info:"Unbound Family Name"
  | Some base_linkage -> 
      let base_linkage =
          Linkage.path_subtitution base_linkage
            ~source:(Naming.self_version base_linkage.name)
            ~target:(Naming.self_version name)
      in
      match Context.get_store () with
      | Some _context ->
          Inheritance.inherit_dependencies ~prefix:name;                    
          let context = Context.get () in
          let _, parameters =
            Codegen.compile_linkage_context ~field_name:name context
          in
          let default_ctx_params =
            Codegen.compile_default_params
              ~context:parameters
          in
          let elem = Inheritance.lookup_field_in_base ~field:name ~context in
          let base =            
            match elem with
            | Some (LinkageElem.FamilyDefinition { linkage = further; _ }) ->
               let derived = { further with context = Bwd.of_list parameters } in
               Some (Inheritance.linkage_concatenate ~derived ~base:base_linkage)
            | Some _ -> Errors.fail ~info:"Expected a family linkage element"
            | None -> Some base_linkage
          in
          let linkage =
            Linkage.
              {
                context = Bwd.of_list parameters;
                name;
                base;
                fields = Bwd.Emp;
                default_ctx_params;
              }
          in                              
          let context = LinkageCtx.Nested (context, linkage) in
          Checks.check_further_binding_structure context;
          Context.destructive_update (Some context)
      | None ->
          let linkage =
            Linkage.
              {
                context = Bwd.Emp;
                name;
                base = Some base_linkage;
                fields = Bwd.Emp;
                default_ctx_params = [];
              }
          in          
          let context = LinkageCtx.Toplevel linkage in          
          Context.destructive_update (Some context)

let close_family () =
  let context = Context.get () in
  match context with
  | LinkageCtx.Toplevel linkage ->
      let linkage =
        match linkage.base with
        | None -> linkage
        | Some base_linkage ->
           let elements = Bwd.to_list base_linkage.fields in 
           Inheritance.inherit_elements ~elements ~linkage ~context
      in      
      Context.destructive_update None;
      let _impl = Codegen.compile_linkage linkage in
      Linkages.add linkage
  | LinkageCtx.Nested (upper, linkage) ->
      let linkage =
        match linkage.base with
        | None -> linkage
        | Some base_linkage ->
           let elements = Bwd.to_list base_linkage.fields in           
           Inheritance.inherit_elements ~elements ~linkage ~context
      in      
      let signature = Codegen.compile_linkage_signature linkage in
      let impl = Codegen.compile_nested_linkage linkage in
      let elem =
        let compiled_context =          
          match linkage.context with
          | Bwd.Emp ->
              Errors.fail
                ~info:
                "close_family: Couldn't get compiled \
                 context from parameters"
          | Bwd.Snoc (_, (_, mapply)) -> Termutils.extract_functor_name mapply
        in
        let default_ctx_params =
          upper
          |> Context.family_linkage
          |> function { default_ctx_params; _ } -> default_ctx_params
        in
        LinkageElem.FamilyDefinition
          {
            linkage;
            compiled_context;
            compiled_signature = signature;
            compiled_impl = impl;
            default_ctx_params;
          }
      in
      Context.destructive_update (Some upper);
      Context.add_field ~name:linkage.name ~elem
