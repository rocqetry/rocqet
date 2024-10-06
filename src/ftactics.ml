(* Custom tactics for family polymorphism *)

open Types

(*
let get_hyps_as_econstr_list (gl : Proofview.Goal.t) : EConstr.t list =
  let sigma = Proofview.Goal.sigma gl in
  let hyps = Proofview.Goal.hyps gl in
  List.map 
    (fun decl -> Context.Named.Declaration.get_type decl) 
    (Context.Named.to_vars hyps) *)

open Env

(* fsimpl *)
let fsimpl () =
  Proofview.Goal.enter begin fun gl ->    
    let goal = Proofview.Goal.concl gl in    
    let _hyps : EConstr.named_context = Proofview.Goal.hyps gl in
    let env = Proofview.Goal.env gl in        
    let evar_map = Evd.from_env env in

    let goal_names = Termutils.constants_in_econstr evar_map goal in   
    
    let is_self_name name = 
      name |> Names.Id.to_string |> String.starts_with ~prefix:"self__"
    in 

    let remove_self_qualid name = 
       let rec remove_self_qual = function 
           | [] -> Errors.fail ~info:"remove_self_qual: empty list"
           | p :: path when is_self_name p -> Naming.list_to_path path
           | _ :: path -> remove_self_qual path                             
       in 
       remove_self_qual (Naming.path_to_list name)
    in 
    
    let is_self_qualid path = 
      path |> Naming.path_to_list |> List.exists is_self_name
    in

    (* TODO: This can merged into one *)
    let context = Context.get () in 
    let handlers =       
      goal_names
      (* filter self names and extract the unqualified name *)                             
      |> List.filter_map (fun name -> 
            if is_self_qualid name then Some (remove_self_qualid name)
            else None)
      (* lookup linkage element *)                             
      |> List.filter_map (fun name -> 
           name |> Context.lookup_linkage_elem context |> Option.map fst)
      (* extract inductive path *)                             
      |> List.filter_map (function 
           | LinkageElem.RecursorDefinition { names; handlers; _} -> Some (names, handlers)
           | _ -> None)      
    in

    let computational_axioms = 
      handlers 
      (* Now we create the computational axiom *)
      |> List.concat_map (fun (names, handlers) -> 
           let recursor_name = List.hd names in
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
    in 
    
    let all_case_definitions = 
      (* Now we create the handler case definitions *)
      handlers
      |> List.concat_map (fun (names, handlers) -> 
           let recursor = List.hd names in
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
    in

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
    in

    (* repeat ( rewrite ... in * || ...) *)
    let rewrites = 
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
   in
   
   (* (unfold ... ) ...  *)
   let unfolds = 
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
                        (Names.Id.of_string "__funfold"),
                      [ each_eq ] ))))
        in 
        Tacinterp.interp tactic
      in 
      let all_unfold_tactics = List.map each_rewrite_tactic all_case_definitions in       
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
      all_case_definitions
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in    
    Feedback.msg_info (Pp.str names) ;    
    
    Tacticals.tclTHEN rewrites unfolds
  end

(* finjection *)
(* fdiscriminate *)
(* fconstructor *)
