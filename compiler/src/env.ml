open Types
open Bwd
open Bwd.Infix

module PluginScopes = struct
  (* This is basically a stack of scopes *)
  let scopes = Summary.ref ~name:"PluginScopes" ([] : PluginCmdScope.t list)
  let peek () = match !scopes with [] -> None | scope :: _ -> Some scope

  let push scope =
    match peek () with
    | None | Some { command = PluginCmd.Family; _ } ->
        scopes := scope :: !scopes

  (* Basically, the caller wants to close the scope with
     name `scope_name`. `scope_name` can also serve as a form
     of verification, ensuring that we pop the right scope *)
  let pop scope_name =
    match !scopes with
    | [] -> None (* The caller should know how to handle this *)
    | ({ PluginCmdScope.name; _ } as scope) :: scopes_rest
      when name = scope_name ->
        scopes := scopes_rest;
        Some scope
    | _ -> Errors.report ~error:Errors.ClosingWrongScope

  let ensure_in_scope ~scope =
    match peek () with
    | Some { PluginCmdScope.command; _ } when command = scope -> ()
    | Some _ | None -> Errors.fail ~info:"Expected to be in a different scope"
end

(* Take note that there is now a local scope for linkages *)
module Linkages = struct
  let store = Summary.ref ~name:"Linkages" (Bwd.Emp : Linkage.t Bwd.t)
  let add linkage = store := Bwd.Snoc (!store, linkage)

  let lookup name =
    !store
    |> Bwd.find_opt (fun linkage -> Names.Id.equal linkage.Linkage.name name)
end

(* TODO: Give this a better name *)
module Context = struct
  let store = Summary.ref ~name:"LinkageContext" (None : LinkageCtx.t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is not current context"
    | Some context -> context

  let family_name context =
    match context with
    | LinkageCtx.Toplevel linkage | LinkageCtx.Nested (_, linkage) ->
        linkage.name

  let start_linkage name =
    match !store with
    | Some context ->
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
        store := Some (LinkageCtx.Nested (context, linkage))
    | None ->
        let linkage =
          Linkage.{ context = Bwd.Emp; name; base = None; fields = Bwd.Emp }
        in
        store := Some (LinkageCtx.Toplevel linkage)

  let start_linkage_with_base ~name ~base =
    match Linkages.lookup base with
    | None -> Errors.fail ~info:("Unbound Name " ^ Names.Id.to_string base)
    | Some base_linkage -> (
        match !store with
        | Some context ->
            (* Is this correct? *)
            (* Are we missing a parameter? *)
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
            store := Some context
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
            store := Some (LinkageCtx.Toplevel linkage))

  (* Add the field to the current linkage *)
  let add_field ~name ~elem =
    match !store with
    | None ->
        Errors.fail
          ~info:"You need to open a linkage context in order to add a field"
    | Some (LinkageCtx.Toplevel linkage) ->
        let fields = linkage.fields <: (name, elem) in
        let ctx = LinkageCtx.Toplevel { linkage with fields } in
        store := Some ctx
    | Some (LinkageCtx.Nested (upper, linkage)) ->
        let fields = linkage.fields <: (name, elem) in
        let linkage = Linkage.{ linkage with fields } in
        let ctx = LinkageCtx.Nested (upper, linkage) in
        store := Some ctx

  (* TODO: Don't allow this, have an update function *)
  let replace ~linkage =
    match !store with
    | None | Some (LinkageCtx.Toplevel _) ->
        store := Some (LinkageCtx.Toplevel linkage)
    | Some (LinkageCtx.Nested (upper, _)) ->
        store := Some (LinkageCtx.Nested (upper, linkage))

  let rec walk_up_linkage_context context =
    match context with
    | LinkageCtx.Toplevel linkage ->
        linkage.base |> Option.map (fun base -> (Bwd.Emp, base))
    | LinkageCtx.Nested (upper, linkage) ->
        walk_up_linkage_context upper
        |> Option.map (fun (path, base) ->
               (Bwd.Snoc (path, linkage.name), base))

  let rec walk_down_linkage (linkage : Linkage.t) path : Linkage.t option =
    match path with
    | [] -> Some linkage
    | head :: path -> (
        let Linkage.{ fields; _ } = linkage in
        let elem =
          fields |> Bwd.find_opt (fun (name, _) -> Names.Id.equal head name)
        in
        match elem with
        | None -> None
        | Some (_, LinkageElem.FamilyDefinition { linkage; _ }) ->
            walk_down_linkage linkage path
        | Some _ -> Errors.fail ~info:"Expected a family in path")

  let further_bound_linkage context =
    match context with
    | LinkageCtx.Toplevel _ -> None
    | LinkageCtx.Nested (_, _) -> (
        match walk_up_linkage_context context with
        | None -> None
        | Some (path, parent) -> walk_down_linkage parent (path |> Bwd.to_list))

  let base_linkage context =
    match context with
    | LinkageCtx.Toplevel linkage | LinkageCtx.Nested (_, linkage) ->
        linkage.base

  let base_linkage_elem context ~field =
    let lookup (linkage : Linkage.t) =
      linkage.fields
      |> Bwd.find_opt (fun (name, _) -> Names.Id.equal name field)
    in
    context |> base_linkage |> Option.map lookup |> Option.flatten
    |> Option.map snd

  let further_bound_linkage_elem context ~field =
    let lookup (linkage : Linkage.t) =
      linkage.fields
      |> Bwd.find_opt (fun (name, _) -> Names.Id.equal name field)
    in
    context |> further_bound_linkage |> Option.map lookup |> Option.flatten
    |> Option.map snd

  let family_linkage context =
    match context with
    | LinkageCtx.Toplevel linkage | LinkageCtx.Nested (_, linkage) -> linkage

  let close () : unit =
    let context = !store in
    match context with
    | None -> Errors.fail ~info:"There is no linkage context to close"
    | Some (LinkageCtx.Toplevel linkage) ->
        let linkage =
          match linkage.base with
          | None -> linkage
          | Some base_linkage ->
             let base_linkage =
               Linkage.path_subtitution base_linkage ~base:base_linkage.name ~derived:linkage.name
             in 
              Linkage.concatenate ~base:base_linkage ~derived:linkage
        in
        store := None;
        let _ = Codegen.compile_linkage linkage in
        Linkages.add linkage
    | Some (LinkageCtx.Nested (upper, linkage) as context) ->
        let linkage =
          match (further_bound_linkage context, base_linkage context) with
          | None, None -> linkage
          | Some _, Some _ ->
              Errors.fail
                ~info:
                  "Nested families can't be further bound and have a base \
                   family at the same time"
          | _, Some base ->
              let base = Codegen.parameterize ~prefix:linkage.context base in
              let base = Linkage.path_subtitution base ~base:base.name ~derived:linkage.name in 
              let further_bound = Linkage.concatenate ~base ~derived:linkage in
              further_bound
          | Some base, _ ->
              let base = Linkage.path_subtitution base ~base:base.name ~derived:linkage.name in 
              let further_bound = Linkage.concatenate ~base ~derived:linkage in
              further_bound
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
        store := Some upper;
        add_field ~name:linkage.name ~elem

  (* Does this linkage further binds any other linkage? *)
  (* Does this linkage have a base family? *)
  (* Futher binding take precedence over having a base family *)
  (* Precendece here means that if a field `f` is in both a base and futher bound family,
     we should pick the one in the further bound family *)
  (* Also maybe further binding logic should be in concatenate? *)
end
