(* Custom tactics for family polymorphism *)

(* fsimpl *)
let fsimpl () =
  Proofview.Goal.enter begin fun gl ->    
    let goal = Proofview.Goal.concl gl in    
    (* Get all hypotheses *)
    (* let hyps = Proofview.Goal.hyps gl in*)
    let env = Proofview.Goal.env gl in        
    let evar_map = Evd.from_env env in

    let goal_names = Termutils.constants_in_econstr evar_map goal in     
    (*let goal_names =
      goal 
      |> EConstr.to_constr evar_map                             
      |> Termutils.reflect_checked_term                             
      |> Constrexpr_ops.free_vars_of_constr_expr                           
      |> Names.Id.Set.to_list                             
    in *)

    let names = 
      goal_names 
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in 
    
    Feedback.msg_info (Pp.str names) ;    
    
    Proofview.tclUNIT ()
  end

(* finjection *)
(* fdiscriminate *)
(* fconstructor *)
