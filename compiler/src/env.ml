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

  let start_linkage name =
    match !store with
    | Some _ -> Errors.fail ~info:"A linkage has already started"
    | None ->
        let linkage = Linkage.{ name; base = None; fields = Bwd.Emp } in
        store := Some (LinkageCtx.Toplevel linkage)

  let start_linkage_with_base ~name ~base =
    match Linkages.lookup base with
    | None -> Errors.fail ~info:("Unbound Name " ^ Names.Id.to_string base)
    | Some base_linkage -> (
        match !store with
        | Some _ -> Errors.fail ~info:"A linkage has already started"
        | None ->
            let linkage =
              Linkage.{ name; base = Some base_linkage; fields = Bwd.Emp }
            in
            store := Some (LinkageCtx.Toplevel linkage))

  (* Add the field to the current linkage *)
  let add_field ~name ~elem =
    match !store with
    | None ->
        Errors.fail
          ~info:"You need to open a linkage context in order to add a field"
    | Some linkage ->
        let (LinkageCtx.Toplevel body) = linkage in
        let fields = body.fields <: (name, elem) in
        let linkage = LinkageCtx.Toplevel { body with fields } in
        store := Some linkage

  (* TODO: Don't allow this, have an update function *)
  let replace ~linkage = store := Some (LinkageCtx.Toplevel linkage)

  let close () =
    let context = !store in
    store := None;
    match context with
    | None -> Errors.fail ~info:"There is no linkage context to close"
    | Some context -> (
        let (LinkageCtx.Toplevel linkage) = context in
        match linkage.base with
        | None -> linkage
        | Some base_linkage ->
            Linkage.concatenate ~base:base_linkage ~derived:linkage)
end
