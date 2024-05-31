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

module InhJudgements = struct
  (* The name in the pair is the name of the family in the current
     inheritance context. i.e the family we're currenlty adding fields to *)
  let judgements =
    Summary.ref ~name:"InhJudgements"
      (None : (Names.Id.t * InhJudgement.t) option)

  let push ~name ~judgement = judgements := Some (name, judgement)

  let pop () =
    match !judgements with
    | None -> None
    | Some judgement ->
        judgements := None;
        Some judgement

  let peek () = !judgements

  let ensure_open_judgememt () =
    match !judgements with
    | None ->
        Errors.fail ~info:"Need to have a judgement present to add stuff to"
    | Some _ -> ()

  (* This means that the current context is gotten from the current Inh judgement *)
  let current_output_ctx () =
    match !judgements with
    | None ->
        Errors.fail
          ~info:
            "Ensure you are in a judgement before trying to get the family \
             context"
    | Some (name, judgement) ->
        let InhJudgement.{ derived; _ } = judgement in
        FamilyContext.Toplevel (name, derived)

  let current_family_name () =
    match !judgements with
    | None -> Errors.fail ~info:"There is no current family scope"
    | Some (name, _) -> name
end

(* This stores the toplevel families that have been closed *)
module GlobalCtx = struct
  let store = Summary.ref ~name:"GlobalCtx" ([] : FamilyRef.t list)

  let push ~name ~family_term ~family_type =
    let family_ref = FamilyRef.ToplevelRef (name, family_term, family_type) in
    store := family_ref :: !store

  let lookup name =
    !store
    |> List.find_opt (function FamilyRef.ToplevelRef (store_name, _, _) ->
           Names.Id.equal store_name name)
end

module Linkages = struct
  let store = Summary.ref ~name:"Linkages" (Bwd.Emp : Linkage.t Bwd.t)

  let add linkage = store := Bwd.Snoc (!store, linkage)

  let lookup name =
    !store |> Bwd.find_opt (fun linkage -> Names.Id.equal linkage.Linkage.name name)
end

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
    | Some base_linkage ->
       match !store with
       | Some _ -> Errors.fail ~info:"A linkage has already started"
       | None ->          
          let linkage = Linkage.{ name; base = Some base_linkage; fields = Bwd.Emp } in
          store := Some (LinkageCtx.Toplevel linkage)

  let add_field ~name ~elem =
    match !store with
    | None -> Errors.fail ~info:"You need to open a linkage context in order to add a field"
    | Some linkage ->
       let (LinkageCtx.Toplevel body) = linkage in
       let fields = body.fields <: (name, elem) in
       let linkage = LinkageCtx.Toplevel { body with fields; } in       
       store := Some linkage

  let linkage_concatenate ~(derived : Linkage.t) ~(base : Linkage.t) =
    (* This is a very naive concatenation *)
    let rec compute_difference ~base ~derived =
      match (base, derived) with
      | [], [] -> []
      | (bname, belem) :: base', (dname, delem) :: derived' ->
          if Names.Id.equal bname dname then
            compute_difference ~base:base' ~derived:derived'
          else
            (* Since this element is inherited, it should have InhOp.CInhInherit *)
            (* let belem = LinkageElem.{ belem with in  *)
            (bname, belem) :: compute_difference ~base:base' ~derived
      | _ :: _, [] -> base
      | [], _ :: _ -> []
    in
    let base_fields = base.Linkage.fields |> Bwd.to_list in
    let derived_fields = derived.Linkage.fields |> Bwd.to_list in 
    let inherited_fields = compute_difference ~base:base_fields ~derived:derived_fields in
    let fields = derived.fields <@ inherited_fields in
    Linkage.{ derived with fields; }

  (* Still naive *)
  let linkage_concatenate_prefix ~prefix ~(derived : Linkage.t) ~(base : Linkage.t) =
    let rec calculate_dependencies fields =
      match fields with
      | Bwd.Emp -> Bwd.Emp
      | Bwd.Snoc (fields, (found_name, _))
        when Names.Id.equal found_name prefix ->
         (* Remove the fields in the that have already been extended by the derived family *)
         (* Here we could use the previous concatenate *)
          fields
          |> Bwd.filter (fun (name, _) ->
                 derived.fields |> Bwd.map fst
                 |> Bwd.exists (Names.Id.equal name)
                 |> not)
      | Bwd.Snoc (fields, _) -> calculate_dependencies fields
    in
    let inherited_fields = calculate_dependencies base.fields in
    let fields = inherited_fields <@ Bwd.to_list derived.fields in
    Linkage.{ derived with fields; }
  
  let replace ~linkage = store := Some (LinkageCtx.Toplevel linkage)  

  let close () =
    let context = !store in
    store := None;
    match context with
    | None -> Errors.fail ~info:"There is linkage context to close"
    | Some context ->
       let (LinkageCtx.Toplevel linkage) = context in
       match linkage.base with
       | None -> linkage
       | Some base_linkage -> linkage_concatenate ~base:base_linkage ~derived:linkage          
end

