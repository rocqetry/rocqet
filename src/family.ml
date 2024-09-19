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
      let linkage =
        Linkage.
          {
            context = parameters |> Bwd.of_list;
            name;
            base = None;
            fields = Bwd.Emp;
            default_ctx_params
          }
      in
      let subst (target, source) l =
            Linkage.path_subtitution l
              ~source:(Naming.self_version source)
              ~target:(Naming.self_version target)
      in
      let furthers =
        (LinkageCtx.Nested (context, linkage))
        |> Context.further_bound_linkage        
      in      
      let base =
        match furthers with
        | [] -> None
        | (m, x) :: xs ->
            let f (m, further) furthers =
              Inheritance.linkage_concatenate ~derived:(subst m further) ~base:furthers
            in
            Some
              (List.fold_right f xs (subst m x))
      in
      (* Check further binding structure? *)
      let linkage = { linkage with base; } in
      Context.destructive_update (Some (LinkageCtx.Nested (context, linkage)))
  | None ->
      let linkage =
        Linkage.{ context = Bwd.Emp; name; base = None; fields = Bwd.Emp; default_ctx_params = [] }
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
          let linkage =
            Linkage.
              {
                context = parameters |> Bwd.of_list;
                name;
                base = Some base_linkage;
                fields = Bwd.Emp;
                default_ctx_params;
              }
          in                    
          let base = Some base_linkage in
          let linkage = { linkage with base; } in
          let context = LinkageCtx.Nested (context, linkage) in          
          let subst (target, source) l =
            Linkage.path_subtitution l
              ~source:(Naming.self_version source)
              ~target:(Naming.self_version target)
          in
          let furthers =
            context
            |> Context.further_bound_linkage            
          in
          let further =
            match furthers with
            | [] -> None
            | (m, x) :: xs ->
                let f (m, further) furthers =
                  Inheritance.linkage_concatenate ~derived:(subst m further) ~base:furthers
                in
                Some
                  (List.fold_right f xs (subst m x))
          in
          let base =
            match further with 
            | None -> base
            | Some further -> Some (Inheritance.linkage_concatenate ~derived:further ~base:base_linkage)
          in
          let linkage = { linkage with base; } in
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
          let base = Some base_linkage in
          let linkage = { linkage with base; } in
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
           Inheritance.inherit_elements ~elements ~linkage
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
           Inheritance.inherit_elements ~elements ~linkage
      in      
      let signature = Codegen.compile_linkage_signature linkage in
      let impl = Codegen.compile_nested_linkage linkage in
      let elem =
        let compiled_context =
          let rec extract_name (name : Constrexpr.module_ast) =
            match name.v with
            | Constrexpr.CMident name -> name
            | Constrexpr.CMapply (name, _) -> extract_name name
            | Constrexpr.CMwith (name, _) -> extract_name name
          in
          match linkage.context with
          | Bwd.Emp ->
              Errors.fail
                ~info:
                  "We should have parameters since we're in a nested context"
          | Bwd.Snoc (_, (_, name)) -> extract_name name
        in
        let default_ctx_params =
          match linkage.context with
          | Bwd.Emp -> []
          | Bwd.Snoc (context, _) ->
             Codegen.compile_default_params
               ~context:(Bwd.to_list context)
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
