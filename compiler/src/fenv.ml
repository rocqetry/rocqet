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
    | { Ftypes.PluginCmdScope.name; _ } as scope :: scopes when name = scope_name -> Some scope
    | _  ->  Ferror.report ~error:Ferror.ClosingWrongScope 
    
end

module InhJudgements = struct 
  let judgements =
    Summary.ref
      ~name:"InhJudgements" 
      ([] : (Names.Id.t * Ftypes.InhJudgement.t) list)
 
 let push ~name ~judgement = judgements := (name, judgement) :: !judgements   
end


(* 
   This means that the current context is gotten from the current Inh judgement
   
*)
(* 
let currentinh_output_ctx () : family_ctxtype =
   match !inhcontentref with 
   | [] -> FamCtx []
   | content :: _ ->
     let fname, (((inp, oup) , FamCtx ctx), current_inh) = content in 
     FamCtx ((fname, oup)::ctx)  
*)
