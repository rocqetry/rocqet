open Env

let add ~(inductive_path : Libnames.qualid) = 
  let context = Context.get () in  
  let ty = Termutils.compute_partial_recursor_signature ~inductive_path ~context in  
  let sigma, env = Termutils.global_env () in
  let s = Ppconstr.pr_constr_expr env sigma ty in
  Feedback.msg_warning s  

