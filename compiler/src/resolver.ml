(* Resolving variable names to self-qualified names.

   Ideally the compiler should know which variables refer to which
   particular "self".

   In particular when a user enters a variable such as `expr`, we want to
   be able to automatically infer the "self" used here.
   
   Consider the following program:
   ```
       Family IR. 
           FInductive expr := expr_int | expr_binary 
           FInductive stmt := stmt_skip | stmt_assign | 
           Family Semantics. 
               FInductive state := state_return : stmt ... | state_call | body_state
               FInductive step : state -> state -> Type := 
                   | exec_skip : ... 
                   | exec_assign : expr ...
           FEnd Semantics.
       FEnd IR.
   ```
   We should we able to infer/resolve all names like so: 
   ```
       Family IR. 
           FInductive expr := expr_int | expr_binary 
           FInductive stmt := stmt_skip | stmt_assign | 
           Family Semantics. 
               FInductive state := state_return : self__IR.stmt ... | state_call | body_state
               FInductive step : self__Semantics.state -> self__Semantics.state -> Type := 
                   | exec_skip : ... 
                   | exec_assign : self__IR.expr ...
           FEnd Semantics.
       FEnd IR.
   ```
*)
open Types
open Bwd

(* Creates a `field name -> family name` mapping *)
let rec linear_ctx_mapping context = 
  let f (linkage : Linkage.t) (name, elem) = 
    match elem with 
    | LinkageElem.InductiveDefinition { inductive; _ } ->
       let names = 
         inductive 
         |> VernacInductive.extract_all_names_with_type
         |> List.concat_map (fun (_, constrs) -> 
                constrs 
                |> List.map (fun (name, _) -> (name, Naming.self_version linkage.name)))
       in 
       (name, Naming.self_version linkage.name) :: names 
    | _ -> [name, Naming.self_version linkage.name]
  in 
  match context with 
  | LinkageCtx.Toplevel linkage -> 
     linkage.fields 
     |> Bwd.to_list
     |> List.concat_map (f linkage)
  | LinkageCtx.Nested (upper, linkage) -> 
     let upper_result = linear_ctx_mapping upper in 
     let linkage_result = 
       linkage.fields 
       |> Bwd.to_list
       |> List.concat_map (f linkage)
     in
     upper_result @ linkage_result


let rec replace_qualid_path dict r =
    let open Constrexpr_ops in 
    let open Constrexpr in 
    let open Libnames in 
    let take_root_of_path (t : qualid) : Names.Id.t =
      fst (Naming.to_name_optionqualid t) 
    in
    match r with
    | { CAst.loc = _; v = CRef (qid,us) } as x when (not (Libnames.qualid_is_ident qid))  ->
        (* rename the root *)
      (match List.assoc_opt (take_root_of_path qid) dict with 
      | Some new_root -> 
          let newqid = Naming.point_qualid new_root qid in 
            CAst.make (CRef (newqid, us))
      | None -> x
      )
    | { CAst.loc = _; CAst.v = CRef (qid,us) } as x when (Libnames.qualid_is_ident qid)  ->
        (* rename the var *)
      (match List.assoc_opt (qualid_basename qid) dict with 
      | Some new_root -> 
          let newqid = Naming.point_qualid new_root qid in 
          CAst.make (CRef (newqid, us))
      | None -> x
      )
      (* now it is capture-avoiding substitution *)
    | cn -> map_constr_expr_with_binders 
              (fun n dict ->  List.remove_assoc n dict) 
              replace_qualid_path dict cn

let resolve_constrexpr ~(context : LinkageCtx.t) ~expression = 
  let mapping = linear_ctx_mapping context in 
  replace_qualid_path mapping expression

let resolve_inductive ~context ~inductive = 
  let resolve_constructor ((u, paramty, tyty, cstrty) : Vernacexpr.inductive_expr) : Vernacexpr.inductive_expr = 
    (* TODO: also take care of paramty later *)
    let tyty = Option.map (fun expression -> resolve_constrexpr ~context ~expression) tyty in 
    let cstrty = 
      match cstrty with 
      | Vernacexpr.Constructors l -> 
         Vernacexpr.Constructors (List.map (fun (h, (a, c)) -> (h, (a, resolve_constrexpr ~context ~expression:c))) l) 
      | _ -> Errors.fail ~info:"Record types are not yet implemented"
    in 
    (u, paramty, tyty, cstrty)
  in 
  List.map (fun (a,b) -> (resolve_constructor a, b)) inductive
  
