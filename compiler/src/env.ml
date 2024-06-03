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

  let start_linkage name =
    match !store with
    | Some context ->
       let compiled_context, parameters = Codegen.compile_linkage_context ~field_name:name context in
       let linkage =
         Linkage.{
             context = parameters |> Bwd.of_list;
             compiled_context = Some compiled_context;
             name;
             base = None;
             fields = Bwd.Emp
        }
       in
       let context = LinkageCtx.Nested (context, linkage) in 
       store := Some context
    | None ->
        let linkage =
          Linkage.{ context = Bwd.Emp; compiled_context = None; name; base = None; fields = Bwd.Emp }
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
           let compiled_context, parameters = Codegen.compile_linkage_context ~field_name:name context in
           let linkage =
             Linkage.{
                 context = parameters |> Bwd.of_list;
                 compiled_context = Some compiled_context;
                 name;
                 base = Some base_linkage;
                 fields = Bwd.Emp
            }
           in
           let context = LinkageCtx.Nested (context, linkage) in 
           store := Some context
        | None ->
            let linkage =
              Linkage.
                {
                  context = Bwd.Emp;
                  compiled_context = None; 
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
  let replace ~linkage = store := Some (LinkageCtx.Toplevel linkage)

  let rec walk_up context =
    match context with
    | LinkageCtx.Toplevel linkage ->
        linkage.base |> Option.map (fun base -> (Bwd.Emp, base))
    | LinkageCtx.Nested (upper, linkage) ->
        walk_up upper
        |> Option.map (fun (path, base) ->
               (Bwd.Snoc (path, linkage.name), base))

  let rec walk_down linkage path =
    match path with
    | [] -> linkage
    | head :: path ->
        let Linkage.{ fields; _ } = linkage in
        let linkage =
          let elem =
            fields |> Bwd.find_opt (fun (name, _) -> Names.Id.equal head name)
          in
          match elem with
          | None -> Errors.fail ~info:"Got a malformed path"
          | Some (_, LinkageElem.FamilyDefinition { linkage; _ }) -> linkage
          | Some _ -> Errors.fail ~info:"Expected a family in path"
        in
        walk_down linkage path

  let further_bound context =
    match context with
    | LinkageCtx.Toplevel _ -> None
    | LinkageCtx.Nested (_, _) ->
        match walk_up context with
        | None -> None            
        | Some (path, parent) -> Some (walk_down parent (path |> Bwd.to_list))                                  

  let close () : unit =
    let context = !store in
    match context with
    | None -> Errors.fail ~info:"There is no linkage context to close"
    | Some (LinkageCtx.Toplevel linkage) ->
      let linkage =
        match linkage.base with
        | None -> linkage
        | Some base_linkage ->                        
            Linkage.concatenate ~base:base_linkage ~derived:linkage
      in
          store := None;
          let _ = Codegen.compile_linkage linkage in 
          Linkages.add linkage
    | Some (LinkageCtx.Nested (upper, linkage) as context) ->
       let linkage = 
        match walk_up context with
        | None -> linkage            
        | Some (path, parent) ->
            (* This is the linkage we want to futher bind *)
            let further = walk_down parent (path |> Bwd.to_list) in
            let further_bound =
              Linkage.concatenate ~base:further ~derived:linkage
            in            
            further_bound
       in
       let signature = Codegen.compile_nested_linkage_signature linkage in
       let impl = Codegen.compile_nested_linkage linkage in
       let elem =
       LinkageElem.FamilyDefinition {
           linkage;
           compiled_context = linkage.compiled_context |> Option.get;
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

(*
                     Family A {
                        Family B {
                           Family C { } 
                        }
                     }
                   *)

(*
                     Family A1 extends C {
                        Family B { 
                           Family C { }
                        }
                     }
                    *)
