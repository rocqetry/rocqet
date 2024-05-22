let add_new_family name = 
  let open Ftypes in 
  let id = FamilyId.fresh () in 
  let family_name = FamilyName.{ name; id } in 
  let family_type = FamilyType.{ name = family_name; body = [] } in
  (* A trvial self judgmemt *)
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  Fenv.InhJudgements.push ~name ~judgement


let inductive_to_famtype 
   ~(ind_def : Ftypes.VernacInductive.t)
   ~(ctx : Ftypes.FamilyContext.t) : Ftypes.CompiledModule.t = 
  
  failwith ""

let inductive_to_famterm_and_recursor_type
   ~(ind_def : Ftypes.VernacInductive.t)
   ~(ctx : Ftypes.FamilyContext.t) : Ftypes.CompiledModule.t = 
  failwith ""

(* we want to compile an inductive definition *)
(* We take in the current judgement *)
(* The name of the inductive type *)
(* The inductive definition itself *)
(* We also take the current context *)
let compile_inductive_definition 
  ~(judgement : Ftypes.InhJudgement.t) 
  ~(ind_def_name : Names.Id.t) 
  ~(ind_def: Ftypes.VernacInductive.t)
  ~(ctx: Ftypes.FamilyContext.t) : Ftypes.InhJudgement.t = 
  let open Ftypes in  
  let InhJudgement.{ derived; body; _ } = judgement in 
  let all_fields = VernacInductive.extract_all_ident ind_def in
  let compiled_signature = inductive_to_famtype ~ind_def ~ctx in 
  let compiled_impl = inductive_to_famterm_and_recursor_type ~ind_def ~ctx in
  let ctx_elem = 
    FamilyTypeElem.FInductive
       { original_inductive = ind_def;
         constructor_names = all_fields;
         compiled_signature;
         compiled_impl; }
  in  
  let derived_with_elem = 
    FamilyType.extend 
      ~name:ind_def_name ~elem:ctx_elem derived
  in  
  let inh_elem = InhElement.CInhNew compiled_impl in  
  { judgement with 
      derived = derived_with_elem; 
      body = (ind_def_name, inh_elem) :: body; }
  
let add_inductive_definition ind_def = 
  Fenv.InhJudgements.ensure_open_judgememt ();
  let all_names = Ftypes.VernacInductive.extract_all_ident ind_def in  
  let ind_def_name = List.hd all_names in
  let ctx = Fenv.InhJudgements.current_output_ctx () in 

  (* Type checking of the inductive definition: *)
  (*  We do type checking by tranpiling to Coq  *)
  (* let _ = inductive_to_famtype ([ind_def], current_ctx) in *)
  (* let _ = inductive_to_famterm_and_recursor_type ([ind_def], current_ctx) in *)

  match Fenv.InhJudgements.pop () with 
  | None -> Ferror.fail ~info:"Expected a non empty inh context"
  | Some (family_name, judgement) -> 
     let judgement = 
       compile_inductive_definition 
         ~judgement ~ind_def_name ~ind_def ~ctx
     in
     Fenv.InhJudgements.push ~name:family_name ~judgement
    
 

