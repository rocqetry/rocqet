open Types
open Env

(* Does this family have a base family? *)
let judgement_has_base judgement =
  let InhJudgement.{ base; derived; _ } = judgement in
  Names.Id.equal base.name derived.name |> not

let top_uninherited_fields judgement =
  let InhJudgement.{ base; derived; _ } = judgement in
  (* we need to reverse base and derived because they are backward lists *)
  let rec compute_difference ~(base : (Names.Id.t * FamilyTypeElem.t) list)
      ~(derived : (Names.Id.t * FamilyTypeElem.t) list) :
      (Names.Id.t * FamilyTypeElem.t) list =
    match (base, derived) with
    | [], [] -> []
    | (bname, belem) :: base', (dname, delem) :: derived' ->
        if Names.Id.equal bname dname then
          compute_difference ~base:base' ~derived:derived'
        else (bname, belem) :: compute_difference ~base:base' ~derived
    | _ :: _, [] -> base
    | [], _ :: _ -> []
  in
  compute_difference
    ~base:(base.FamilyType.body |> List.rev)
    ~derived:(derived.FamilyType.body |> List.rev)

let inherit_all_remained () =
  InhJudgements.ensure_open_judgememt ();
  let name, judgement = InhJudgements.peek () |> Option.get in
  let inherited_fields = top_uninherited_fields judgement in
  let types, judgements =
    List.fold_left
      (fun (types, judgements) (fname, elem) ->
        ((fname, elem) :: types, (fname, InhElement.CInhInherit) :: judgements))
      ([], []) inherited_fields
  in
  let derived =
    FamilyType.
      { name = judgement.derived.name; body = types @ judgement.derived.body }
  in
  let body = judgements @ judgement.body in
  let judgement = InhJudgement.{ judgement with derived; body } in
  InhJudgements.push ~name ~judgement

(* Get a family term from a judgement: basically from the expected type
   and the inheritance op, we can get the family term *)
(* This is for a new family which does not have a base family, so all we
   need to generate the family term is in the judgement *)
let family_term_of_judgement ~(judgement : InhJudgement.t) : FamilyTerm.t =
  let compute_family_term_elem (name, ty, inh) =
    match (inh, ty) with
    | InhElement.CInhNew compiled, FamilyTypeElem.FInductive _ ->
        (name, FamilyTermElem.CompiledDefinition compiled)
    | InhElement.CInhInherit, _ -> Errors.fail ~info:"This doesn't inherit"
    | InhElement.CInhExtendInd _, _ -> Errors.fail ~info:"This doesn't inherit"
  in
  let family_term_body =
    judgement |> InhJudgement.family_type_inh_op
    |> List.map compute_family_term_elem
  in
  FamilyTerm.{ body = family_term_body }

let apply_judgement_to_family_term ~(judgement : InhJudgement.t)
    ~(family_term : FamilyTerm.t) : FamilyTerm.t =
  let compute_family_term_elem (name, type_elem, inh_elem) =
    (* This is O(n^2) *)
    let _term_elem =
      family_term.body |> List.map fst |> List.find_opt (Names.Id.equal name)
    in
    match (inh_elem, type_elem) with
    | InhElement.CInhNew compiled, FamilyTypeElem.FInductive _ ->
        (name, FamilyTermElem.CompiledDefinition compiled)
    | InhElement.CInhInherit, FamilyTypeElem.FInductive { compiled_impl; _ } ->
        (name, FamilyTermElem.CompiledDefinition compiled_impl)
    | InhElement.CInhExtendInd _, FamilyTypeElem.FInductive { compiled_impl; _ }
      ->
        (name, FamilyTermElem.CompiledDefinition compiled_impl)
  in
  let body =
    judgement |> InhJudgement.family_type_inh_op
    |> List.map compute_family_term_elem
  in
  FamilyTerm.{ body }

(* Apply the judgements in a derived family to the base family, to produce an
   apprpriate family term *)
let apply_derived_judgement_to_base ~(judgement : InhJudgement.t)
    ~(base_family : FamilyRef.t option) : FamilyTerm.t =
  match base_family with
  | None -> family_term_of_judgement ~judgement
  | Some (FamilyRef.ToplevelRef (_, family_term, _)) ->
      apply_judgement_to_family_term ~judgement ~family_term

let compile_family_term_module ~(family_term : FamilyTerm.t)
    ~(name : Names.Id.t) : CompiledModule.t =
  let open Codegen.VernacBackend in
  let open Codegen in
  let FamilyTerm.{ body } = family_term in
  let rec famterm_internal_include (body : (Names.Id.t * FamilyTermElem.t) list)
      (ctx : ModuleTerm.t list) =
    match body with
    | [] -> return ()
    | (name, FamilyTermElem.CompiledDefinition compiled) :: body_rest ->
        let* _ = famterm_internal_include body_rest ctx in
        let module_expr = Termutils.ident_to_module_expr compiled in
        let* _ = include_module ~module_expr in
        return ()
  in
  define_module ~module_name:name ~parameters:[]
    ~body:(famterm_internal_include body)
  |> run

let close_current_inheritance_judgement () =
  let open FamilyType in
  InhJudgements.ensure_open_judgememt ();
  let _, judgement = InhJudgements.pop () |> Option.get in
  let InhJudgement.{ base = base_family_type; derived = derived_family_type; _ }
      =
    judgement
  in
  let base_family =
    if judgement_has_base judgement then GlobalCtx.lookup base_family_type.name
    else None
  in
  let derived_family_term =
    apply_derived_judgement_to_base ~judgement ~base_family
  in
  compile_family_term_module ~family_term:derived_family_term
    ~name:derived_family_type.name
  |> ignore;
  GlobalCtx.push ~name:derived_family_type.name ~family_type:derived_family_type
    ~family_term:derived_family_term

let open_new_inheritance_judgement name =
  let family_type = FamilyType.{ name; body = [] } in
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  InhJudgements.push ~name ~judgement

let open_derived_inheritance_judgement ~base ~derived =
  let family_type = FamilyType.{ name = derived; body = [] } in
  let base_family_type =
    match GlobalCtx.lookup base with
    | None ->
        Errors.fail ~info:("Unbound family name: " ^ Names.Id.to_string base)
    | Some (FamilyRef.ToplevelRef (_, _, base_family_type)) -> base_family_type
  in
  let judgement =
    InhJudgement.empty ~base:base_family_type ~derived:family_type
  in
  InhJudgements.push ~name:derived ~judgement

let infer_field_inh_kind name =
  InhJudgements.ensure_open_judgememt ();
  let _, judgement = InhJudgements.peek () |> Option.get in
  if judgement_has_base judgement then
    let base_name = judgement.base.name in
    match GlobalCtx.lookup base_name with
    | None ->
        Errors.fail ~info:("Unbound family name " ^ Names.Id.to_string base_name)
    | Some (FamilyRef.ToplevelRef (_, _, family_type)) -> (
        let base_field =
          family_type.body
          |> List.find_opt (fun (found_name, _) ->
                 Names.Id.equal name found_name)
        in
        match base_field with
        | None -> FieldInhKind.New
        | Some (_, elem) -> FieldInhKind.Extend elem)
  else FieldInhKind.New
