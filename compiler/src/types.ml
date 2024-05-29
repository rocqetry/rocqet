module VernacInductive = struct
  type t =
    (Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) list

  (* This returns (inductive type name, inductive type sort) and
                  (constructor name * consructor type)  list*)
  let extract_type_and_cstrs (inductive : Vernacexpr.inductive_expr) =
    let ind_type_name, ind_params, indtype, cstrlist = inductive in
    (* assert_cerror ~einfo:"Doesn't Support Inductive Parameter yet"
       (fun _ -> fst ind_params = [] && snd ind_params = None); *)
    let _, (ind_type_name, _) = ind_type_name in
    let ind_type_name = CAst.with_val (fun x -> x) ind_type_name in
    let each_constr ((_, (cname, cty)) : Vernacexpr.constructor_expr) =
      let cname = CAst.with_val (fun x -> x) cname in
      (cname, cty)
    in
    match cstrlist with
    | Vernacexpr.Constructors cstrlist ->
        ((ind_type_name, indtype), List.map each_constr cstrlist)
    | Vernacexpr.RecordDecl _ -> Errors.fail ~info:"Records not yet supported"

  let extract_all_ident ind_def =
    let all_names =
      ind_def
      |> List.map (fun (ind_expr, _) -> ind_expr |> extract_type_and_cstrs)
    in
    let type_names = all_names |> List.map (fun x -> x |> fst |> fst) in
    let cstr_names = all_names |> List.concat_map snd |> List.map fst in
    type_names @ cstr_names

  (* Get the name of an inductive definition *)
  let extract_type_ident ind_def =
    ind_def
    |> List.map @@ fun (ind_expr, _) ->
       ind_expr |> extract_type_and_cstrs
       |> fst (* get the type name, type sort *)
       |> fst (* get just the type name *)

  (* Get the constructors in an inductive definition *)
  let extract_cstrs_ident ind_def =
    ind_def
    |> List.map (fun (ind_expr, _) -> ind_expr |> extract_type_and_cstrs)
    |> List.concat_map (fun (_, cstrs) -> cstrs |> List.map fst)

  (* Create a "definition mapping" *)
  let definition_mapping ~prefix ind_def =
    let all_names_with_type =
      ind_def |> List.map (fun (ind_expr, _) -> extract_type_and_cstrs ind_expr)
    in
    let prefix_with_internal (name : Names.Id.t) =
      Nameops.add_prefix prefix name
    in
    let all_original_names =
      all_names_with_type
      |> List.concat_map (fun ((ind_name, _), cstrs) ->
             ind_name :: List.map fst cstrs)
    in
    let all_new_names = List.map prefix_with_internal all_original_names in
    let definition_mapping = List.combine all_original_names all_new_names in
    let map_name_newname =
      List.fold_right
        (fun (original_name, new_name) map ->
          Names.Id.Map.add original_name new_name map)
        definition_mapping Names.Id.Map.empty
    in
    let apply_subst_expr =
      Constrexpr_ops.replace_vars_constr_expr map_name_newname
    in
    (* TODO: Rename the variables in this function *)
    let apply_subst_inductive_expr (((a, (b, c)), d, e, f), g) =
      let b = CAst.map prefix_with_internal b in
      let e = Option.map apply_subst_expr e in
      match f with
      | Vernacexpr.Constructors csts ->
          let csts =
            List.map
              (fun (z, (x, y)) ->
                (z, (CAst.map prefix_with_internal x, apply_subst_expr y)))
              csts
          in
          let f = Vernacexpr.Constructors csts in
          (((a, (b, c)), d, e, f), g)
      | _ -> Errors.fail ~info:"Records not yet supported"
    in
    (* Use option to extract the type *)
    let all_names_with_type =
      List.concat_map
        (fun ((x, y), z) -> (x, Option.get y) :: z)
        all_names_with_type
    in
    (* Exporting the names *)
    let alias_all_name_term_type_decl =
      List.map
        (fun (name, ty) ->
          (name, Constrexpr_ops.mkIdentC (prefix_with_internal name), ty))
        all_names_with_type
    in
    let modified_ind_def = List.map apply_subst_inductive_expr ind_def in
    (modified_ind_def, alias_all_name_term_type_decl)
end

module FamilyId = struct
  type t = int

  let fresh =
    let store = ref 0 in
    fun () ->
      incr store;
      !store
end

(* Module naming *)
(* This should really be Names.ModPath.t *)
module CompiledModule = struct
  type t = Libnames.qualid
end

module CompiledModuleType = struct
  type t = Libnames.qualid
end

module rec FamilyTypeElem : sig
  type t =
    | FInductive of {
        original_inductive : VernacInductive.t;
        constructor_names : Names.Id.t list;
        compiled_signature : CompiledModuleType.t;
        compiled_impl : CompiledModule.t;
        compiled_ctx : CompiledModuleType.t;
      }
end =
  FamilyTypeElem

and FamilyType : sig
  type t = { name : Names.Id.t; body : (Names.Id.t * FamilyTypeElem.t) list }

  val extend : name:Names.Id.t -> elem:FamilyTypeElem.t -> t -> t
end = struct
  type t = { name : Names.Id.t; body : (Names.Id.t * FamilyTypeElem.t) list }

  let extend ~name ~elem family_type =
    let { body; _ } = family_type in
    { family_type with body = (name, elem) :: body }
end

(* `FamilyContext.t` is a "focused" view of `InhJudgemen.t`*)
and FamilyContext : sig
  type t = Toplevel of Names.Id.t * FamilyType.t
end =
  FamilyContext

module rec FamilyRef : sig
  type t = ToplevelRef of Names.Id.t * FamilyTerm.t * FamilyType.t
end =
  FamilyRef

and FamilyTermElem : sig
  type t = CompiledDefinition of CompiledModule.t
end =
  FamilyTermElem

and FamilyTerm : sig
  type t = { body : (Names.Id.t * FamilyTermElem.t) list }
end =
  FamilyTerm

and InhElement : sig
  type t =
    | CInhNew of CompiledModule.t
    | CInhExtendInh of InhJudgement.t
    | CInhInherit
end =
  InhElement

and InhJudgement : sig
  type t = {
    base : FamilyType.t;
        (** This is the family that is being extended -- This is our "input" *)
    derived : FamilyType.t;
        (** This is the resulting family of that extension -- This is our "output" *)
    body : (Names.Id.t * InhElement.t) list;
        (** More about `derived` extends particular fields in `base` *)
  }

  val empty : base:FamilyType.t -> derived:FamilyType.t -> t

  val family_type_inh_op :
    t -> (Names.Id.t * FamilyTypeElem.t * InhElement.t) list
end = struct
  type t = {
    base : FamilyType.t;
    derived : FamilyType.t;
    body : (Names.Id.t * InhElement.t) list;
  }

  (* The empty family context here is not really right
     becuase once we have an inheritnce judgement, we can't
     have an empty family context. We can have a context which
     the family type contains no field though. *)
  let empty ~base ~derived = { base; derived; body = [] }

  let family_type_inh_op judgement =
    let { derived; body = judgement_body; _ } = judgement in
    let FamilyType.{ body = family_type_body; _ } = derived in
    Printf.printf "Judgement length: %d\n" (List.length judgement_body);
    Printf.printf "Family type length: %d\n" (List.length family_type_body);
    family_type_body
    |> List.iter (fun (name, _) ->
           Printf.printf "%s\n" (Names.Id.to_string name));
    let family_type_inh_op = List.combine family_type_body judgement_body in
    family_type_inh_op
    |> List.map (fun ((name1, family_type_elem), (name2, inh_elem)) ->
           (* Assert that name1 == name2 *)
           (name1, family_type_elem, inh_elem))
end
(* InhJudgement and FamilyContext should be merged into one type really *)

(* A single plugin command *)
(* e.g Family A. ... *)
module PluginCmd = struct
  type t = Family
end

(* A scope is a plugin command enriched with a name and a "closing" handler *)
(* `close` is a generic handle that is called to close the scope *)
module PluginCmdScope = struct
  type t = { command : PluginCmd.t; name : Names.Id.t; close : unit -> unit }
end

(*
module NestedFamilyContext = struct 
  type t = 
    | Top of FamilyContext.t
    | Level of FamilyContext.t * t
end

module F = struct
  type t =
    | Toplevel of Names.Id.t * FamilyType.t
    | Nestedlevel of Names.Id.t * FamilyType.t * t
end

let name ty = match ty with
  | F.Toplevel (name, ty) -> failwith ""
  | F.Nestedlevel (name, ty, upper) -> failwith ""



(* Field inheritance kind *)
module FieldInheritanceKind = struct 
  type t = New | Extend
end

module FamilyDefinitionContext = struct 
  type t =
    | InitialInhBase of Family.Ref.t option (* A toplevel family *)
end


(* Try to integrate Logs library for logging *)
(* Log to file, Log to output *)



(* inherits_all_remained *)
(* close_current_inh_judgement *)
(* ontopinh *)
(* inhnewind *)
type t = FamCtx of (Names.Id.t * FamilyType.t) list  
*)
