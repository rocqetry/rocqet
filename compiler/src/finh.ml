(* Most of the logic here *)

let start_new_inh_judgement name = 
  let open Ftypes in 
  let id = FamilyId.fresh () in 
  let family_name = FamilyName.{ name; id } in 
  let family_type = FamilyType.{ name = family_name; body = [] } in
  (* A trvial self judgmemt *)
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  Fenv.InhJudgements.push ~name ~judgement

  
let add_inductive_definition ind_def = 
  Fenv.InhJudgements.ensure_open_judgememt () ;
  let all_names = Ftypes.VernacInductive.extract_all_ident ind_def in
  (* all_names 
    |> List.iter (fun name -> 
           name |> Names.Id.to_string |> Pp.str |> Feedback.msg_info) *)
  let _ind_def_name = all_names |> List.hd in
  let _ctx = Fenv.InhJudgements.current_output_ctx () in 
  (* TODO: We do type checking by tranpiling to Coq  *)
  (* let _ = inductive_to_famtype ([e], current_ctx) in *)
  (* let _ = inductive_to_famterm_and_recursor_type ([e], current_ctx) in *)
  (* 
     
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnewind current_inh indgroupname (e, current_ctx)))

  *)
  ()
    
 
(* 
let ontopinh f =  
  assert_current_has_open_judgement();
  let topinh = pop inhcontentref in 
  push inhcontentref (f topinh)
*)
