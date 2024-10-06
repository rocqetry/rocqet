(* Custom tactics for family polymorphism *)
open Env
open Types

(* fsimpl *)
let fsimpl () =
  Proofview.Goal.enter begin fun gl ->    
    let goal = Proofview.Goal.concl gl in    
    (* let hyps = Proofview.Goal.hyps gl in*)
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
    let computational_axioms = 
      let context = Context.get () in 
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
        rewrite_tacatom in 
      let all_rewrite_tactics = List.map each_rewrite_tactic computational_axioms in 
      let tacfail = 
        CAst.make (Tacexpr.TacFail (TacLocal,Locus.ArgArg 0,[]))
      in 
      let union_rewrites = 
        List.fold_right (fun l r -> CAst.make (Tacexpr.TacOrelse (l,r))) all_rewrite_tactics tacfail
      in 
      (* let repeat_union_rewrites = CAst.make (TacRepeat union_rewrites) in  *)
      Tacinterp.interp union_rewrites
   in

    let names = 
      computational_axioms
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in 
    
    Feedback.msg_info (Pp.str names) ;    
    
    rewrites
  end

(* finjection *)
(* fdiscriminate *)
(* fconstructor *)
