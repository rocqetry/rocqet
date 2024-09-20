open Types
open Bwd
open Bwd.Infix

module PluginScopes = struct
  (* This is basically a stack of scopes *)
  let scopes = Summary.ref ~name:"PluginScopes" ([] : PluginCmdScope.t list)
  let peek () = match !scopes with [] -> None | scope :: _ -> Some scope

  let push scope =
    match peek () with
    | None
    | Some
        {
          command =
            PluginCmd.(Family | Recursion | Induction | MetaData | Lemma);
          _;
        } ->
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
    | { PluginCmdScope.name; command; _ } :: rest ->
        let command =
          match command with
          | Lemma -> "FLemma"
          | Family -> "Family"
          | Induction -> "FInduction"
          | Recursion -> "FRecursion"
          | MetaData -> "MetaData"
        in
        let rest =
          rest
          |> List.map (fun (scope : PluginCmdScope.t) -> scope.name)
          |> List.map Names.Id.to_string
          |> String.concat ", "
        in
        let info =
          Printf.sprintf
            "Closing wrong scope: expected to close a scope which was opened \
             by \"%s %s.\" Commands waiting to be closed: %s."
            command (Names.Id.to_string name) rest
        in
        Errors.fail ~info

  let display () =
    let rest =
      !scopes
      |> List.map (fun (scope : PluginCmdScope.t) -> scope.name)
      |> List.map Names.Id.to_string
      |> String.concat ", "
    in
    Feedback.msg_info (Pp.str rest)

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

  (* All possible ways to walk up, stopping at a family with a base *)
  let rec walk_up_linkage_context context :
      (* path, derived, base*)
      (Names.Id.t Bwd.t * Linkage.t * Linkage.t) option list =
    match context with
    | LinkageCtx.Toplevel linkage ->
        [ linkage.base |> Option.map (fun base -> (Bwd.Emp, linkage, base)) ]
    | LinkageCtx.Nested (upper, linkage) ->
        let result =
          walk_up_linkage_context upper
          |> List.map (fun almost ->
                 almost
                 |> Option.map (fun (path, derived, base) ->
                        (Bwd.Snoc (path, linkage.name), derived, base)))
        in
        let current =
          linkage.base
          |> Option.map (fun base -> (Bwd.Emp, linkage, base))
        in
        current :: result

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

  let lookup context (path : Libnames.qualid) =
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
    (* let linkage =
         match walk context with
         | None -> Linkages.lookup name
         | Some context -> Some context
       in*)
    let linkage =
      match context with
      | None -> Linkages.lookup name
      | Some context -> walk context
    in
    match rest with
    | [] -> linkage
    | path ->
        Option.bind linkage (fun linkage -> walk_down_linkage linkage path)

  let lookup_linkage_elem context (path : Libnames.qualid) =
    let family, name = Naming.path_to_prefix path in
    let result =
      match Option.bind family (lookup (Some context)) with
      | None -> None
      | Some linkage ->
          linkage.fields
          |> Bwd.find_map (fun (found_name, elem) ->
                 if Names.Id.equal name found_name then Some (elem, linkage)
                 else None)
    in
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
    match family with None -> go context | Some _ -> result

  let lookup_inductive_for_recursion ~name context =
    match lookup_linkage_elem context name with
    | Some
        ( LinkageElem.InductiveDefinition { inductive; recursors; _ },
          linkage ) ->
        (inductive, recursors, linkage)
    | Some _ -> Errors.fail ~info:"Expected an inductive type"
    | None ->
        let info =
          Printf.sprintf "Unbound inductive type: %s"
            (Pretty.pretty_qualid name)
        in
        Errors.fail ~info

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
            (Printf.sprintf
               "This element %s has already been defined or it has been previously \
               inherited" (Names.Id.to_string name))
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

  (* derived, base *)
  let further_bound_linkage context :
      ((Names.Id.t * Names.Id.t) * Linkage.t) list =
    match context with
    | LinkageCtx.Toplevel _ -> []
    | LinkageCtx.Nested (_, l) -> (
        context
        |> walk_up_linkage_context
        |> List.filter_map (function
             | None -> None
             | Some (path, (derived : Linkage.t), (parent : Linkage.t)) ->
                 walk_down_linkage parent (path |> Bwd.to_list)
                 |> Option.map (fun further_bound ->
                        ((derived.name, parent.name), further_bound)))
        |> function
        | [] -> []
        | x :: xs -> (          
            (* We don't want to include the current family's base,
               as that is not a further bound linkage *)
            match l.base with None -> x :: xs | Some _ -> xs))

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

  let further_bound_linkage_elem context ~field :
      ((Names.Id.t * Names.Id.t) * Linkage.t * LinkageElem.t) list =
    let lookup (inh, (linkage : Linkage.t)) =
      linkage.fields
      |> Bwd.find_opt (fun (name, _) -> Names.Id.equal name field)
      |> Option.map (fun (_, elem) -> (inh, linkage, elem))
    in
    context |> further_bound_linkage |> List.filter_map lookup
end
