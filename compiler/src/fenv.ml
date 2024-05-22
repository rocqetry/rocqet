module PluginScopes = struct
  (* This is basically a stack of scopes *)
  let scopes = 
     Summary.ref 
       ~name:"PluginScopes" 
       ([] : Ftypes.PluginCmdScope.t list)

  let peek () = 
    match !scopes with 
    | [] -> None 
    | scope :: _ -> Some scope

  let push scope = 
    match peek () with 
    | None | Some { command = Ftypes.PluginCmd.Family; _ } -> 
       scopes := scope :: !scopes
  
  (* Basically, the caller wants to close the scope with 
     name `scope_name`. `scope_name` can also serve as a form 
     of verification, ensuring that we pop the right scope *)
  let pop scope_name = 
    match !scopes with 
    | [] -> None (* The caller should know how to handle this *)
    | { Ftypes.PluginCmdScope.name; _ } as scope :: scopes 
         when name = scope_name -> Some scope
    | _  ->  Ferror.report ~error:Ferror.ClosingWrongScope
  
  let ensure_in_scope ~scope = 
    match peek () with 
    | Some { Ftypes.PluginCmdScope.command; _ } when command = scope -> ()
    | Some _ | None -> Ferror.fail ~info:"Expected to be in a different scope"       
end

module InhJudgements = struct
  (* The name in the pair is the name of the family in the current 
     inheritance context. i.e the family we're currenlty adding fields to *)
  let judgements =
    Summary.ref
      ~name:"InhJudgements"
      ([] : (Names.Id.t * Ftypes.InhJudgement.t) list)
 
 let push ~name ~judgement = judgements := (name, judgement) :: !judgements

 let pop () = 
   match !judgements with 
   | [] -> None 
   | judgement :: js -> 
      judgements := js; 
      Some judgement

 let ensure_open_judgememt () =
   if not (List.length !judgements > 0) then
     Ferror.fail ~info:"Need to have a judgement present to add stuff to"

 (* This means that the current context is gotten from the current Inh judgement *)
 let current_output_ctx () = 
   let open Ftypes in
   match !judgements with 
   | [] -> FamilyContext.FamCtx []
   | (name, judgement) :: _ -> 
      let InhJudgement.{ derived; ctx; _ } = judgement in 
      let FamilyContext.FamCtx ctx = ctx in
      FamilyContext.FamCtx ((name, derived) :: ctx)      
end

