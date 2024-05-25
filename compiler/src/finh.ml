open Ftypes
open Fenv

module ScopeClosing = struct
  let inherit_all_remained () = ()

  let inh_apply_standalone ~(judgement : InhJudgement.t) : FamilyTerm.t =
    let f (name, ty, inh) =
      match (inh, ty) with
      | InhElement.CInhNew compiled, FamilyTypeElem.FInductive _ ->
          (name, FamilyTermElem.CompiledDefinition compiled)
      | InhElement.CInhExtendInh _, _ -> Ferror.fail ~info:"Not yet implementes"
    in
    let family_term_body =
      judgement |> InhJudgement.family_type_inh_op |> List.map f
    in
    FamilyTerm.{ body = family_term_body }

  let inh_apply_famref ~(judgement : InhJudgement.t)
      ~(base_family : FamilyRef.t option) : FamilyTerm.t =
    match base_family with
    | None -> inh_apply_standalone ~judgement
    | Some _ -> Ferror.fail ~info:"No support for extending families yet"

  (* We need to know the provenance of a context *)
  let standalone_famterm_to_mod ~(family_term : FamilyTerm.t) : CompiledModule.t
      =
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
      ~module_name:(Fcodegen.fresh_name ~prefix:"__")
      ~parameters:[]
      ~body:(famterm_internal_include body)
    |> run

  let close_current_inheritance_judgement () =
    InhJudgements.ensure_open_judgememt ();
    (* The `Option.get` below is safe because of the above assertion *)
    let name, judgement = Fenv.InhJudgements.pop () |> Option.get in
    (* I don't know if this is the right ctx *)
    let _ctx = InhJudgements.current_output_ctx () in
    let InhJudgement.{ derived = _; _ } = judgement in
    let family_term = inh_apply_famref ~judgement ~base_family:None in
    let module_instantiation = standalone_famterm_to_mod ~family_term in
    let module_expr = Ftermutils.ident_to_module_expr module_instantiation in
    let open Fcodegen.VernacBackend in
    define_module ~module_name:name ~parameters:[] ~body:(fun _ ->
        include_module ~module_expr)
    |> run |> ignore
end

let add_new_family name =
  let id = FamilyId.fresh () in
  let family_name = FamilyName.{ name; id } in
  let family_type = FamilyType.{ name = family_name; body = [] } in
  (* A trvial self judgmemt *)
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  Fenv.InhJudgements.push ~name ~judgement

(* `famctx_to_parameters` and `famty_to_modsig` functions work in lock-step to
   produce an algorithm for the compilation of "context" modules *)

(** This function is the entry point to the compilation of contexts *)
let rec famctx_to_parameters ~(ctx : Ftypes.FamilyContext.t) :
    (Names.Id.t * Constrexpr.module_ast) list =
  let open Ftypes in
  match ctx with
  | FamilyContext.Toplevel (family_name, family_type) ->
      let compiled_family_name =
        famty_to_modsig
          ~current_path:(family_name |> Libnames.qualid_of_ident)
          ~family_type
      in
      let family_module_expr =
        Ftermutils.ident_to_module_expr compiled_family_name
      in
      let self__family_name =
        Names.Id.of_string @@ "self__" ^ Names.Id.to_string family_name
      in
      [ (self__family_name, family_module_expr) ]

(** This function is responsible for compiling the body of the context module,
    which contains the appriopiate "Include ..." *)
and famty_to_modsig ~(current_path : Ftypes.CompiledModuleType.t)
    ~(family_type : Ftypes.FamilyType.t) : Ftypes.CompiledModuleType.t =
  let open Ftypes in
  match family_type with
  | FamilyType.{ body = []; _ } ->
      let module Backend = Fcodegen.VernacBackend in
      let open Backend in
      run
      @@ define_moduletype ~module_name:(Fcodegen.fresh_name ~prefix:"EmptySig")
           ~parameters:[] ~body:(fun _arguments -> return ())
  | { name = family_name; body = (field_name, field_elem) :: body_rest } -> (
      match field_elem with
      | FamilyTypeElem.FInductive { compiled_signature; compiled_impl; _ } ->
          let finductive_ctx_sig_name =
            Fcodegen.fresh_name ~prefix:(field_name |> Names.Id.to_string)
          in
          (* The context for this finductive type *)
          let finductive_ctx =
            famty_to_modsig ~current_path
              ~family_type:FamilyType.{ name = family_name; body = body_rest }
          in
          let finductive_ctx_expr =
            Ftermutils.ident_to_module_expr finductive_ctx
          in
          let finductive_signature_expr =
            Ftermutils.ident_to_module_expr compiled_signature
          in
          let module Backend = Fcodegen.VernacBackend in
          let open Backend in
          run
          @@ define_moduletype ~module_name:finductive_ctx_sig_name
               ~parameters:[] ~body:(fun _arguments ->
                 let* () = include_module ~module_expr:finductive_ctx_expr in
                 let* () =
                   include_module ~module_expr:finductive_signature_expr
                 in
                 return ()))

let inductive_to_famtype ~(ind_def : Ftypes.VernacInductive.t)
    ~(ctx : Ftypes.FamilyContext.t) : Ftypes.CompiledModuleType.t =
  let open Ftypes in
  let ind_cstrs =
    ind_def
    |> List.map (fun ind ->
           ind |> fst |> VernacInductive.extract_type_and_cstrs)
    |> List.map (fun ((ind_name, ty), cstrs) ->
           ((ind_name, Option.get ty), cstrs))
  in
  let type_decls = ind_cstrs |> List.map fst in
  let module_name =
    Fcodegen.fresh_name
      ~prefix:(type_decls |> List.hd |> fst |> Names.Id.to_string)
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
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name
       ~parameters:(famctx_to_parameters ~ctx) ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

(* This is the instantiation of an inductive type and it's recursors *)
let inductive_to_famterm_and_recursor_type ~(ind_def : Ftypes.VernacInductive.t)
    ~(ctx : Ftypes.FamilyContext.t) : Ftypes.CompiledModule.t =
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
  let module_name =
    run
    @@ define_module ~module_name ~parameters:(famctx_to_parameters ~ctx)
         ~body:(fun _ ->
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
  let open Ftypes in
  let InhJudgement.{ derived; body; _ } = judgement in
  let all_fields = VernacInductive.extract_all_ident ind_def in
  let compiled_signature = inductive_to_famtype ~ind_def ~ctx in
  let compiled_impl = inductive_to_famterm_and_recursor_type ~ind_def ~ctx in
  let ctx_elem =
    FamilyTypeElem.FInductive
      {
        original_inductive = ind_def;
        constructor_names = all_fields;
        compiled_signature;
        compiled_impl;
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
  (*  We do type checking by tranpiling to Coq  *)
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
