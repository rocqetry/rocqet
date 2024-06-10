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
      let linkage =
        Linkage.
          {
            context = parameters |> Bwd.of_list;
            name;
            base = None;
            fields = Bwd.Emp;
          }
      in
      Context.destructive_update (Some (LinkageCtx.Nested (context, linkage)))
  | None ->
      let linkage =
        Linkage.{ context = Bwd.Emp; name; base = None; fields = Bwd.Emp }
      in
      Context.destructive_update (Some (LinkageCtx.Toplevel linkage))

let open_family_with_base ~name ~base =
  match Linkages.lookup base with
  | None -> Errors.fail ~info:("Unbound Name " ^ Names.Id.to_string base)
  | Some base_linkage -> (
      match Context.get_store () with
      | Some _context ->
          Inheritance.inherit_dependencies ~prefix:name;
          let context = Context.get () in
          let _, parameters =
            Codegen.compile_linkage_context ~field_name:name context
          in
          let linkage =
            Linkage.
              {
                context = parameters |> Bwd.of_list;
                name;
                base = Some base_linkage;
                fields = Bwd.Emp;
              }
          in
          let context = LinkageCtx.Nested (context, linkage) in
          Context.destructive_update (Some context)
      | None ->
          let linkage =
            Linkage.
              {
                context = Bwd.Emp;
                name;
                base = Some base_linkage;
                fields = Bwd.Emp;
              }
          in
          Context.destructive_update (Some (LinkageCtx.Toplevel linkage)))

(* Close a family *)
let close_family () : unit =
  let context = Context.get () in
  match context with
  | LinkageCtx.Toplevel linkage ->
      let linkage =
        match linkage.base with
        | None -> linkage
        | Some base_linkage ->
            let base_linkage =
              Linkage.path_subtitution base_linkage
                ~source:(Linkage.top_most_self_name base_linkage)
                ~target:(Linkage.top_most_self_name linkage)
            in
            Linkage.concatenate ~base:base_linkage ~derived:linkage
      in
      (* store := None; *)
      Context.destructive_update None;
      Codegen.compile_linkage linkage |> ignore;
      Linkages.add linkage
  | LinkageCtx.Nested (upper, linkage) as context ->
      let further_base = Context.further_bound_linkage context in
      let base = Context.base_linkage context in
      let linkage =
        match (further_base, base) with
        | None, None -> linkage
        | Some further, Some base ->
            let further =
              Linkage.path_subtitution further
                ~source:(Linkage.top_most_self_name further)
                ~target:(Linkage.top_most_self_name linkage)
            in            
            let base =
              let base = Codegen.parameterize ~prefix:linkage.context base in
              Linkage.path_subtitution base
                ~source:(Naming.self_version base.name)
                ~target:(Naming.self_version linkage.name)
            in
            let base = { base with name = further.name } in
            let base = Linkage.concatenate_recursive ~base:further ~derived:base in 
            Codegen.recompute_linkage base
        | _, Some base ->
            (* Here, we are assuming that base is a toplevel family *)
            (* Don't just reparameterize! We need some kind of condition to check
               on linkages to know when two linkages "can't fit" *)
            (* Possibly reparameterization can go both ways? *)
            let base = Codegen.parameterize ~prefix:linkage.context base in
            (* Here we don't need to topmost self name becuase this is classic
               inheritance, not further binding *)
            let base =
              Linkage.path_subtitution base
                ~source:(Naming.self_version base.name)
                ~target:(Naming.self_version linkage.name)
            in
            Linkage.concatenate ~base ~derived:linkage
        | Some further, _ ->
            let base =
              Linkage.path_subtitution further
                ~source:(Linkage.top_most_self_name further)
                ~target:(Linkage.top_most_self_name linkage)
            in
            if Bwd.length base.context <> Bwd.length linkage.context then              
              failwith "Need to reparameterize";            
            Linkage.concatenate ~base ~derived:linkage
      in
      let signature = Codegen.compile_nested_linkage_signature linkage in
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
        LinkageElem.FamilyDefinition
          {
            linkage;
            compiled_context;
            compiled_signature = signature;
            compiled_impl = impl;
          }
      in
      (* store := Some upper; *)
      Context.destructive_update (Some upper);
      Context.add_field ~name:linkage.name ~elem
