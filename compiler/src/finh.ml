let start_new_inh_judgement name = 
  let open Ftypes in 
  let id = FamilyId.fresh () in 
  let family_name = FamilyName.{ name; id } in 
  let family_type = FamilyType.{ name = family_name; body = [] } in
  (* A trvial self judgmemt *)
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  Fenv.InhJudgements.push ~name ~judgement

  
