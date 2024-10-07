(* Custom tactics for family polymorphism *)
open Types

(* selfnames -> (function, handler list) *)
let extract_handlers_names names = 
  let context = Env.Context.get () in
  names  
  |> List.filter_map (fun name -> 
        if Naming.is_self_qualid name 
        then
           name 
           |> Naming.remove_self_qualid
           |> Env.Context.lookup_linkage_elem context 
           |> Option.map fst
           |> Option.map (function 
              | LinkageElem.RecursorDefinition { names; handlers; _} -> 
                 let name = List.hd names in 
                 Some (name, handlers)
              | _ -> None)                      
           |> Option.flatten
        else None)  

let handlers_to_computational_axiom handlers = 
  let context = Env.Context.get () in
  handlers       
  |> List.concat_map (fun (recursor_name, handlers) ->        
       handlers 
       |> List.map (fun constructor_name -> 
              let name = 
                 Naming.computational_axiom_name 
                   ~recursor_name 
                   ~constructor_name
              in 
              Resolver.resolve_qualid 
                ~context 
                ~qualid:(Libnames.qualid_of_ident name)))

let handlers_to_case_definitions handlers = 
  let context = Env.Context.get () in
  handlers
  |> List.concat_map (fun (recursor, handlers) ->        
       handlers 
       |> List.map (fun case -> 
              let name = 
                 Naming.handler_name 
                   ~recursor
                   ~case
              in 
              Resolver.resolve_qualid 
                ~context 
                ~qualid:(Libnames.qualid_of_ident name))) 

let idtac =
  let open Ltac_plugin in
    let idtac =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident
                     (Names.Id.of_string "idtac"),
                   [] ))))
    in
    Tacinterp.interp idtac

(* repeat ( rewrite ... in * || ...) *)
let generate_rewrites computational_axioms = 
   let open Ltac_plugin in 
   let each_rewrite_tactic (each_eq : Libnames.qualid) = 
     (* this section can check g_tactic.mlg *)
     let rewrite_atom = Constrexpr_ops.mkRefC each_eq in 
     let l = [(true, Equality.Precisely 1, (None, ( rewrite_atom , Tactypes.NoBindings)))] in 
     let cl = { Locus.onhyps=None; concl_occs=Locus.AllOccurrences } in 
     let t = None in 
     let rewrite_tacatom =  CAst.make @@ Tacexpr.TacAtom (TacRewrite (false,l,cl,t)) in         
     Tacinterp.interp rewrite_tacatom 
   in 
   let all_rewrite_tactics = List.map each_rewrite_tactic computational_axioms in 
   (*let tacfail = 
     CAst.make (Tacexpr.TacFail (TacLocal,Locus.ArgArg 0,[]))
   in *)
   (* TODO: We actually wanto to do try (rewrite ...) ...  *)
   let union_rewrites = 
     List.fold_right (fun l r -> (Tacticals.tclORELSE l r)) all_rewrite_tactics idtac
   in 
   (* let repeat_union_rewrites = CAst.make (TacRepeat union_rewrites) in  *)
   union_rewrites

(* (unfold ... ) ...  *)
let generate_unfolds unfold case_definitions = 
   let open Ltac_plugin in 
   let each_rewrite_tactic (each_eq : Libnames.qualid) = 
     let each_eq =
       (Tacexpr.TacCall
          (CAst.make
             ( each_eq,
               [] )))      
     in
     let tactic = 
        CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident
                     (Names.Id.of_string unfold),
                   [ each_eq ] ))))
     in 
     Tacinterp.interp tactic
   in 
   let all_unfold_tactics = List.map each_rewrite_tactic case_definitions in       
   let union_unfolds = 
     List.fold_right (fun l r -> Tacticals.tclTHEN l r) all_unfold_tactics idtac        
   in
   union_unfolds

(* fsimpl *)
let fsimpl () =
  Proofview.Goal.enter begin fun gl ->    
    let goal = Proofview.Goal.concl gl in    
    let env = Proofview.Goal.env gl in        
    let evar_map = Evd.from_env env in

    let goal_names = Termutils.constants_in_econstr evar_map goal in            
    
    let handlers = extract_handlers_names goal_names in      

    let computational_axioms = handlers_to_computational_axiom handlers in        
    
    let case_definitions = handlers_to_case_definitions handlers in     
    
    let rewrites = generate_rewrites computational_axioms in
      
    let unfolds = generate_unfolds "__funfold" case_definitions in

    let names = 
      computational_axioms
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in 
    Feedback.msg_info (Pp.str names) ;    

    let names = 
      case_definitions
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in    
    Feedback.msg_info (Pp.str names) ;    
    
    Tacticals.tclTHEN rewrites unfolds
  end

let fsimpl_star () =
  Proofview.Goal.enter begin fun gl ->    
    let goal = Proofview.Goal.concl gl in    
    let hyps : EConstr.t list = 
      gl
      |> Proofview.Goal.hyps 
      |> List.concat_map 
           (fun (binding : (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt) -> 
             match binding with
             | Context.Named.Declaration.LocalAssum (_, ty) -> [ty]                
             | Context.Named.Declaration.LocalDef (_, tm, ty) -> [tm;ty])
    in
    let env = Proofview.Goal.env gl in        
    let evar_map = Evd.from_env env in

    let goal_names = Termutils.constants_in_econstr evar_map goal in   
    let hyps_names = hyps |> List.concat_map (Termutils.constants_in_econstr evar_map) in
    let all_names = goal_names @ hyps_names in
    
    let handlers = extract_handlers_names all_names in    

    let computational_axioms = handlers_to_computational_axiom handlers in       
    
    let case_definitions = handlers_to_case_definitions handlers in           
    
    let rewrites = generate_rewrites computational_axioms in   
      
    let unfolds = generate_unfolds "__funfold_star" case_definitions in   

    let names = 
      computational_axioms
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in 
    Feedback.msg_info (Pp.str names) ;    

    let names = 
      case_definitions
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in    
    Feedback.msg_info (Pp.str names) ;    
    
    Tacticals.tclTHEN rewrites unfolds
  end

let fsimpl_in h =
  Proofview.Goal.enter begin fun gl ->        
    let hyps : EConstr.t list = 
      gl
      |> Proofview.Goal.hyps 
      |> List.filter_map
           (fun (binding : (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt) -> 
             match binding with
             | Context.Named.Declaration.LocalAssum ({ binder_name; _ }, ty) when Names.Id.equal binder_name h -> Some [ty]
             | Context.Named.Declaration.LocalDef ({ binder_name; _ }, tm, ty) when Names.Id.equal binder_name h -> Some [tm;ty]
             | _ -> None)                 
      |> List.concat                             
    in
    let env = Proofview.Goal.env gl in        
    let evar_map = Evd.from_env env in
    
    let hyps_names = hyps |> List.concat_map (Termutils.constants_in_econstr evar_map) in    
    
    let handlers = extract_handlers_names hyps_names in    

    let computational_axioms = handlers_to_computational_axiom handlers in       
    
    let case_definitions = handlers_to_case_definitions handlers in
    
    let rewrites = 
       let open Ltac_plugin in 
      let each_rewrite_tactic (each_eq : Libnames.qualid) = 
        let each_eq =
          (Tacexpr.TacCall
             (CAst.make
                ( each_eq,
                  [] )))      
        in
        let h =
          (Tacexpr.TacCall
             (CAst.make
                ( Libnames.qualid_of_ident h,
                  [] )))      
        in
        let tactic = 
           CAst.make
           (Tacexpr.TacArg
              (Tacexpr.TacCall
                 (CAst.make
                    ( Libnames.qualid_of_ident
                        (Names.Id.of_string "__frewrite_in"),
                      [ each_eq; h ] ))))
        in 
        Tacinterp.interp tactic
      in 
      let all_rewrite_tactics = List.map each_rewrite_tactic computational_axioms in       
      let union_rewrites = 
        List.fold_right (fun l r -> Tacticals.tclTHEN l r) all_rewrite_tactics idtac        
      in
      union_rewrites
   in 
                             
   let unfolds  = 
      let open Ltac_plugin in 
      let each_rewrite_tactic (each_eq : Libnames.qualid) = 
        let each_eq =
          (Tacexpr.TacCall
             (CAst.make
                ( each_eq,
                  [] )))      
        in
        let h =
          (Tacexpr.TacCall
             (CAst.make
                ( Libnames.qualid_of_ident h,
                  [] )))      
        in
        let tactic = 
           CAst.make
           (Tacexpr.TacArg
              (Tacexpr.TacCall
                 (CAst.make
                    ( Libnames.qualid_of_ident
                        (Names.Id.of_string "__funfold_in"),
                      [ each_eq; h ] ))))
        in 
        Tacinterp.interp tactic
      in 
      let all_unfold_tactics = List.map each_rewrite_tactic case_definitions in       
      let union_unfolds = 
        List.fold_right (fun l r -> Tacticals.tclTHEN l r) all_unfold_tactics idtac        
      in
      union_unfolds
   in     

    let names = 
      computational_axioms
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in 
    Feedback.msg_info (Pp.str names) ;    

    let names = 
      case_definitions
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in    
    Feedback.msg_info (Pp.str names) ;    
    
    Tacticals.tclTHEN rewrites unfolds
  end

(* fsimpl in H *)
(* fsimpl in * *)

(* finjection *)
(* fdiscriminate *)
(* fconstructor *)
