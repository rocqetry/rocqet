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
  match Context.lookup base with
  | None -> Errors.fail ~info:"Unbound Family Name"
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
          Typechecking.check_further_binding_structure context;
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
          let context = LinkageCtx.Toplevel linkage in
          Typechecking.check_further_binding_structure context;
          Context.destructive_update (Some context))

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
                ~source:(Naming.self_version base_linkage.name)
                ~target:(Naming.self_version linkage.name)
            in
            Linkage.concatenate_recursive ~base:base_linkage ~derived:linkage
      in
      (* store := None; *)
      Context.destructive_update None;

      (* Note that we only want to do this when late binding of family names
         happens in the linkage *)
      let linkage = Codegen.recompute_linkage linkage in
      Codegen.compile_linkage linkage |> ignore;
      Linkages.add linkage
  | LinkageCtx.Nested (upper, linkage) as context ->
      let further_base = Context.further_bound_linkage context in
      let base = Context.base_linkage context in
      let linkage =
        match (further_base, base) with
        | None, None ->
            (* failwith "" |> ignore;*)
            linkage
        | Some further, Some base ->
            let base =
              match Linkage.context_match base linkage with
              | `Less | `More ->
                  Codegen.recompute_linkage
                    { base with context = linkage.context }
              | `Equal -> base
            in
            let further =
              Linkage.path_subtitution further
                ~source:(Linkage.top_most_self_name further)
                ~target:(Linkage.top_most_self_name linkage)
            in
            let base =
              Linkage.path_subtitution base
                ~source:(Naming.self_version base.name)
                ~target:(Naming.self_version linkage.name)
            in
            let base = { base with name = further.name } in
            let base =
              Linkage.concatenate_recursive ~base:further ~derived:base
            in
            let result = Linkage.concatenate_recursive ~base ~derived:linkage in
            result
        | _, Some base ->
            let base =
              match Linkage.context_match base linkage with
              | `Less | `More ->
                  Codegen.recompute_linkage
                    { base with context = linkage.context }
              | `Equal -> base
            in
            let base =
              Linkage.path_subtitution base
                ~source:(Naming.self_version base.name)
                ~target:(Naming.self_version linkage.name)
            in
            Linkage.concatenate_recursive ~base ~derived:linkage
        | Some further, _ ->
            let base =
              Linkage.path_subtitution further
                ~source:(Linkage.top_most_self_name further)
                ~target:(Linkage.top_most_self_name linkage)
            in
            Linkage.concatenate_recursive ~base ~derived:linkage
      in
      (* Again should not do this all the time: *)
      let linkage = Codegen.recompute_linkage linkage in
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
