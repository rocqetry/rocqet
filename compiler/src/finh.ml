open Ftypes
open Fenv

module ScopeClosing = struct
  let inherit_all_remained () = ()

  (* Get a family term from a judgement: basically from the expected type
     and the inheritance op, we can get the family term *)
  (* This is for a new family which does not have a base family, so all we
     need to generate the family term is in the judgement *)
  let family_term_of_judgement ~(judgement : InhJudgement.t) : FamilyTerm.t =
    let compute_family_term_elem (name, ty, inh) =
      match (inh, ty) with
      | InhElement.CInhNew compiled, FamilyTypeElem.FInductive _ ->
          (name, FamilyTermElem.CompiledDefinition compiled)
      | InhElement.CInhExtendInh _, _ -> Ferror.fail ~info:"Not yet implemented"
    in
    let family_term_body =
      judgement |> InhJudgement.family_type_inh_op
      |> List.map compute_family_term_elem
    in
    FamilyTerm.{ body = family_term_body }

  (* Apply the judgements in a derived family to the base family, to produce an
     apprpriate family term *)
  let apply_derived_judgement_to_base ~(judgement : InhJudgement.t)
      ~(base_family : FamilyRef.t option) : FamilyTerm.t =
    match base_family with
    | None -> family_term_of_judgement ~judgement
    | Some _ -> Ferror.fail ~info:"No support for extending families yet"

  let compile_family_term_module ~(family_term : FamilyTerm.t) ~(name: Names.Id.t):
      CompiledModule.t =
    let open Fcodegen.VernacBackend in
    let open Fcodegen in
    let FamilyTerm.{ body } = family_term in
    let rec famterm_internal_include
        (body : (Names.Id.t * FamilyTermElem.t) list) (ctx : ModuleTerm.t list)
        =
      match body with
      | [] -> return ()
      | (name, FamilyTermElem.CompiledDefinition compiled) :: body_rest ->
          let* _ = famterm_internal_include body_rest ctx in
          let module_expr = Ftermutils.ident_to_module_expr compiled in
          let* _ = include_module ~module_expr in
          return ()
    in
    define_module
      ~module_name:name
      ~parameters:[]
      ~body:(famterm_internal_include body)
    |> run

  let close_current_inheritance_judgement () =
    InhJudgements.ensure_open_judgememt ();
    let _ctx = InhJudgements.current_output_ctx () in
    (* The `Option.get` below is safe because of the above assertion *)
    let name, judgement = Fenv.InhJudgements.pop () |> Option.get in
    let InhJudgement.{ derived = family_type; _ } = judgement in
    let family_term =
      apply_derived_judgement_to_base ~judgement ~base_family:None
    in
    compile_family_term_module ~family_term ~name |> ignore;
    GlobalCtx.push ~family_type ~family_term
end

let add_new_family name =
  let id = FamilyId.fresh () in
  let family_name = FamilyName.{ name; id } in
  let family_type = FamilyType.{ name = family_name; body = [] } in
  (* A trvial self judgmemt *)
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  Fenv.InhJudgements.push ~name ~judgement

(* Compile a context *)
let compile_context ~ctx ~module_name =
  let (FamilyContext.Toplevel (name, ty)) = ctx in
  let FamilyType.{ body; _ } = ty in
  let open Fcodegen.VernacBackend in
  match body with
  | [] ->
      define_moduletype ~module_name:(Fcodegen.fresh_name ~prefix:"EmptySig")
        ~parameters:[] ~body:(fun _arguments -> return ())
      |> run
  | (_, FamilyTypeElem.FInductive { compiled_signature; compiled_ctx; _ }) :: _
    ->
      let module_name_ctx = Nameops.add_suffix module_name "Ctx" in
      define_moduletype ~module_name:module_name_ctx ~parameters:[]
        ~body:(fun _arguments ->
          let* () =
            include_module
              ~module_expr:(Ftermutils.ident_to_module_expr compiled_ctx)
          in
          let* () =
            include_module
              ~module_expr:(Ftermutils.ident_to_module_expr compiled_signature)
          in
          return ())
      |> run

(* Retrn the name of the compiled family field and return its compiled context's name *)
let inductive_to_famtype ~(ind_def : Ftypes.VernacInductive.t)
    ~(ctx : CompiledModuleType.t) : CompiledModuleType.t =
  let ind_cstrs =
    ind_def
    |> List.map (fun ind ->
           ind |> fst |> VernacInductive.extract_type_and_cstrs)
    |> List.map (fun ((ind_name, ty), cstrs) ->
           ((ind_name, Option.get ty), cstrs))
  in
  let type_decls = ind_cstrs |> List.map fst in
  let original_ind_name = type_decls |> List.hd |> fst in
  let module_name =
    Fcodegen.fresh_name ~prefix:(original_ind_name |> Names.Id.to_string)
  in
  let constr_decls = List.concat_map snd ind_cstrs in
  let module Backend = Fcodegen.VernacBackend in
  let declare_typedecls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) type_decls
  in
  let declare_csts_decls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) constr_decls
  in
  let all_decls = declare_typedecls @ declare_csts_decls in
  let parameters =
    [
      ( Nameops.add_prefix "self__" original_ind_name,
        Ftermutils.ident_to_module_expr ctx );
    ]
  in
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name ~parameters ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

(* This is the instantiation of an inductive type and it's recursors *)
let inductive_to_famterm_and_recursor_type ~(ind_def : Ftypes.VernacInductive.t)
    ~(ctx : Ftypes.CompiledModuleType.t) : Ftypes.CompiledModule.t =
  let open Ftypes in
  let all_names_with_type =
    ind_def
    |> List.map (fun (ind_expr, _) ->
           VernacInductive.extract_type_and_cstrs ind_expr)
  in
  let original_type_name =
    all_names_with_type
    |> List.map (fun ((ind_name, _), _) -> ind_name)
    |> List.hd
  in
  (* Generate a definition mapping of the inductive type and
     return the new inductive definition and the export of the correct names *)
  let modified_indcstrs, alias_all_name_term_type_decl =
    VernacInductive.definition_mapping ~prefix:"__internal_" ind_def
  in
  let module_name =
    Fcodegen.fresh_name ~prefix:(original_type_name |> Names.Id.to_string)
  in
  let open Fcodegen.VernacBackend in
  let parameters =
    [
      ( Nameops.add_prefix "self__" original_type_name,
        Ftermutils.ident_to_module_expr ctx );
    ]
  in
  let module_name =
    run
    @@ define_module ~module_name ~parameters ~body:(fun _ ->
           let* () = define_inductive modified_indcstrs in
           (* Some stuff with the recursors here *)
           let alias_all =
             List.map
               (fun (original_name, new_name, ty) ->
                 define_term ~name:original_name ~expr:new_name ~ty)
               alias_all_name_term_type_decl
           in
           let* _ = flatmap alias_all in
           return ())
  in
  module_name

let compile_inductive_definition ~(judgement : Ftypes.InhJudgement.t)
    ~(ind_def_name : Names.Id.t) ~(ind_def : Ftypes.VernacInductive.t)
    ~(ctx : Ftypes.FamilyContext.t) : Ftypes.InhJudgement.t =
  let InhJudgement.{ derived; body; _ } = judgement in
  let constructor_names = VernacInductive.extract_all_ident ind_def in
  let compiled_ctx = compile_context ~ctx ~module_name:ind_def_name in
  let compiled_signature = inductive_to_famtype ~ind_def ~ctx:compiled_ctx in
  let compiled_impl =
    inductive_to_famterm_and_recursor_type ~ind_def ~ctx:compiled_ctx
  in
  let ctx_elem =
    FamilyTypeElem.FInductive
      {
        original_inductive = ind_def;
        constructor_names;
        compiled_signature;
        compiled_impl;
        compiled_ctx;
      }
  in
  let derived_with_elem =
    FamilyType.extend ~name:ind_def_name ~elem:ctx_elem derived
  in
  let inh_elem = InhElement.CInhNew compiled_impl in
  {
    judgement with
    derived = derived_with_elem;
    body = (ind_def_name, inh_elem) :: body;
  }

let add_inductive_definition ind_def =
  Fenv.InhJudgements.ensure_open_judgememt ();
  let all_names = Ftypes.VernacInductive.extract_all_ident ind_def in
  let ind_def_name = List.hd all_names in
  let ctx = Fenv.InhJudgements.current_output_ctx () in

  (* Type checking of the inductive definition: *)
  (* let _ = inductive_to_famtype ([ind_def], current_ctx) in *)
  (* let _ = inductive_to_famterm_and_recursor_type ([ind_def], current_ctx) in *)
  match Fenv.InhJudgements.pop () with
  | None -> Ferror.fail ~info:"Expected a non empty inh context"
  | Some (family_name, judgement) ->
      let judgement =
        compile_inductive_definition ~judgement ~ind_def_name ~ind_def ~ctx
      in
      Fenv.InhJudgements.push ~name:family_name ~judgement

(* TODO:
   1. Compile output to a file
   2. Compiling recursors
   3. We need to start adding debug functions
   (e.g Print Family Context. Print Inheritance Judgement.
        Print Family Type <name>. )
   4. Test
   5. Closing families *)
