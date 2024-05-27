open Ftypes

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
    | _ -> Ferror.report ~error:Ferror.ClosingWrongScope

  let ensure_in_scope ~scope =
    match peek () with
    | Some { Ftypes.PluginCmdScope.command; _ } when command = scope -> ()
    | Some _ | None -> Ferror.fail ~info:"Expected to be in a different scope"
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

  let ensure_open_judgememt () =
    match !judgements with
    | None ->
        Ferror.fail ~info:"Need to have a judgement present to add stuff to"
    | Some _ -> ()

  (* This means that the current context is gotten from the current Inh judgement *)
  let current_output_ctx () =
    match !judgements with
    | None ->
        Ferror.fail
          ~info:
            "Ensure you are in a judgement before trying to get the family \
             context"
    | Some (name, judgement) ->
        let InhJudgement.{ derived; _ } = judgement in
        FamilyContext.Toplevel (name, derived)
end

(* This stores the toplevel families that have been closed *)
module GlobalCtx = struct
  let store = Summary.ref ~name:"GlobalCtx" ([] : FamilyRef.t list)

  let push ~name ~family_term ~family_type =
    let family_ref = FamilyRef.ToplevelRef (name, family_term, family_type) in    
    store := family_ref :: !store
end
