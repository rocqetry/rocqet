(*
    self-name resolution.

    The compiler "knows" which self-name a variable is qualified by.

    In particular, when a user enters a variable such as `expr`, we want to
    be able to automatically infer the "self" used here. In this case, `expr`
    will be transformed to `self__XXX.expr`, where `XXX` is the name of the
    family in the current context which `expr` is bound.
*)
open Types
open Bwd

(* Creates a `field name -> family name` mapping *)
let rec linear_ctx_mapping context =
  let f (linkage : Linkage.t) (name, elem) =
    match elem with
    | LinkageElem.RecursorDefinition { names; handlers; _ } ->
        let recursor = names |> List.hd in
        let names =
          handlers
          |> List.map (fun case -> Naming.handler_name ~recursor ~case)
          |> List.map (fun name -> (name, Naming.self_version linkage.name))
        in
        (recursor, Naming.self_version linkage.name) :: names
    | LinkageElem.InductiveDefinition { inductive; _ } ->        
        let names =
          inductive
          |> VernacInductive.extract_all_names_with_type
          |> List.concat_map (fun (_, constrs) ->
                 constrs
                 |> List.map (fun (name, _) ->
                        (name, Naming.self_version linkage.name)))
        in        
        (name, Naming.self_version linkage.name) :: names
    | _ -> [ (name, Naming.self_version linkage.name) ]
  in
  match context with
  | LinkageCtx.Toplevel linkage ->
      linkage.fields |> Bwd.to_list |> List.concat_map (f linkage)
  | LinkageCtx.Nested (upper, linkage) ->
      let upper_result = linear_ctx_mapping upper in
      let linkage_result =
        linkage.fields |> Bwd.to_list |> List.concat_map (f linkage)
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
  | { CAst.loc = _; v = CRef (qid, us) } as x
    when not (Libnames.qualid_is_ident qid) -> (
      (* rename the root *)
      match List.assoc_opt (take_root_of_path qid) dict with
      | Some new_root ->
          let newqid = Naming.point_qualid new_root qid in
          CAst.make (CRef (newqid, us))
      | None -> x)
  | { CAst.loc = _; v = CRef (qid, us) } as x when Libnames.qualid_is_ident qid
    -> (
      (* rename the var *)
      match List.assoc_opt (qualid_basename qid) dict with
      | Some new_root ->
          let newqid = Naming.point_qualid new_root qid in
          CAst.make (CRef (newqid, us))
      | None -> x (* now it is capture-avoiding substitution *))
  | cn ->
      map_constr_expr_with_binders
        (fun n dict -> List.remove_assoc n dict)
        replace_qualid_path dict cn

let resolve_qualid ~(context : LinkageCtx.t) ~qualid =
  let dict = linear_ctx_mapping context in
  let name =
    if Libnames.qualid_is_ident qualid then Libnames.qualid_basename qualid
    else qualid |> Naming.to_name_optionqualid |> fst
  in
  match List.assoc_opt name dict with
  | Some new_root -> Naming.point_qualid new_root qualid
  | None -> qualid

let resolve_constrexpr ~(context : LinkageCtx.t) ~expression =
  let mapping = linear_ctx_mapping context in
  replace_qualid_path mapping expression

let resolve_constrexpr_list ~(context : LinkageCtx.t) ~expressions =
  expressions
  |> List.map (fun expression -> resolve_constrexpr ~context ~expression)

let resolve_inductive ~context ~inductive =
  let resolve_constructor
      ((u, paramty, tyty, cstrty) : Vernacexpr.inductive_expr) :
      Vernacexpr.inductive_expr =
    (* TODO: handle `paramty` *)
    let tyty =
      Option.map
        (fun expression -> resolve_constrexpr ~context ~expression)
        tyty
    in
    let cstrty =
      match cstrty with
      | Vernacexpr.Constructors l ->
          Vernacexpr.Constructors
            (List.map
               (fun (h, (a, c)) ->
                 (h, (a, resolve_constrexpr ~context ~expression:c)))
               l)
      | _ -> Errors.fail ~info:"Record types are not yet implemented"
    in
    (u, paramty, tyty, cstrty)
  in
  List.map (fun (a, b) -> (resolve_constructor a, b)) inductive
