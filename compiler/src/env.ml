open Types
open Bwd
open Bwd.Infix

module PluginScopes = struct
  (* This is basically a stack of scopes *)
  let scopes = Summary.ref ~name:"PluginScopes" ([] : PluginCmdScope.t list)
  let peek () = match !scopes with [] -> None | scope :: _ -> Some scope

  let push scope =
    match peek () with
    | None | Some { command = PluginCmd.(Family | Recursion | Induction); _ } ->
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
  let get_store () = !store

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

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no current context"
    | Some context -> context

  let lookup (path : Libnames.qualid) =
    let path = Naming.path_to_list path in
    let name = List.hd path in
    let rec walk context =
      match context with
      | LinkageCtx.Toplevel linkage -> (
          linkage.fields
          |> Bwd.find_map (fun (field_name, elem) ->
                 match elem with
                 | LinkageElem.FamilyDefinition { linkage; _ }
                   when Names.Id.equal name field_name ->
                     Some linkage
                 | _ -> None)
          |> function
          | None -> Linkages.lookup name
          | linkage -> linkage)
      | LinkageCtx.Nested (context, linkage) -> (
          linkage.fields
          |> Bwd.find_map (fun (field_name, elem) ->
                 match elem with
                 | LinkageElem.FamilyDefinition { linkage; _ }
                   when Names.Id.equal name field_name ->
                     Some linkage
                 | _ -> None)
          |> function
          | None -> walk context
          | linkage -> linkage)
    in
    let rest = List.tl path in
    let linkage =
      match !store with
      | None -> Linkages.lookup name
      | Some context -> walk context
    in
    match rest with
    | [] -> linkage
    | path ->
        Option.bind linkage (fun linkage -> walk_down_linkage linkage path)

  let lookup_linkage_elem context (path : Libnames.qualid) =
    (* Handle paths later *)
    let _family, name = Naming.path_to_prefix path in
    let rec go context =
      match context with
      | LinkageCtx.Toplevel linkage ->
          linkage.fields
          |> Bwd.find_map (fun (found_name, elem) ->
                 if Names.Id.equal name found_name then Some (elem, linkage)
                 else None)
      | LinkageCtx.Nested (context, linkage) -> (
          linkage.fields
          |> Bwd.find_map (fun (found_name, elem) ->
                 if Names.Id.equal name found_name then Some (elem, linkage)
                 else None)
          |> function
          | None -> go context
          | Some (elem, linkage) -> Some (elem, linkage))
    in
    go context

  let lookup_inductive_for_recursion ~name context =
    match lookup_linkage_elem context name with
    | Some
        ( LinkageElem.InductiveDefinition { inductive; compiled_recursors; _ },
          linkage ) ->
        (inductive, !compiled_recursors, linkage)
    | _ -> Errors.fail ~info:"Unbound inductive type "

  let family_name context =
    match context with
    | LinkageCtx.Toplevel linkage | LinkageCtx.Nested (_, linkage) ->
        linkage.name

  let family_linkage context =
    match context with
    | LinkageCtx.Toplevel linkage | LinkageCtx.Nested (_, linkage) -> linkage

  (* TODO: Don't allow this, have an update function *)
  let replace ~linkage =
    match !store with
    | None | Some (LinkageCtx.Toplevel _) ->
        store := Some (LinkageCtx.Toplevel linkage)
    | Some (LinkageCtx.Nested (upper, _)) ->
        store := Some (LinkageCtx.Nested (upper, linkage))

  (* Add the field to the current linkage *)
  let add_field ~name ~elem =
    let context = get () in
    let _ =
      match lookup_linkage_elem context (Libnames.qualid_of_ident name) with
      | Some _ ->
          Errors.fail
            ~info:
              "This element has already been defined or it has been previously \
               inherited"
      | _ -> ()
    in
    match context with
    | LinkageCtx.Toplevel linkage ->
        let fields = linkage.fields <: (name, elem) in
        let ctx = LinkageCtx.Toplevel { linkage with fields } in
        store := Some ctx
    | LinkageCtx.Nested (upper, linkage) ->
        let fields = linkage.fields <: (name, elem) in
        let linkage = Linkage.{ linkage with fields } in
        let ctx = LinkageCtx.Nested (upper, linkage) in
        store := Some ctx

  let destructive_update new_store = store := new_store

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
      |> Option.map (fun (_, elem) -> (linkage, elem))
    in
    context |> base_linkage |> Option.map lookup |> Option.flatten

  let further_bound_linkage_elem context ~field =
    let lookup (linkage : Linkage.t) =
      linkage.fields
      |> Bwd.find_opt (fun (name, _) -> Names.Id.equal name field)
      |> Option.map (fun (_, elem) -> (linkage, elem))
    in
    context |> further_bound_linkage |> Option.map lookup |> Option.flatten
end
