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

    let names = 
      computational_axioms
      |> List.map Pretty.pretty_qualid
      |> String.concat "\n"                             
    in 
    
    Feedback.msg_info (Pp.str names) ;    
    
    Proofview.tclUNIT ()
  end

(* finjection *)
(* fdiscriminate *)
(* fconstructor *)
