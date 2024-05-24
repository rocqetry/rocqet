let add_new_family name =
  let open Ftypes in
  let id = FamilyId.fresh () in
  let family_name = FamilyName.{ name; id } in
  let family_type = FamilyType.{ name = family_name; body = [] } in
  (* A trvial self judgmemt *)
  let judgement = InhJudgement.empty ~base:family_type ~derived:family_type in
  Fenv.InhJudgements.push ~name ~judgement

(* `famctx_to_parameters` and `famty_to_modsig` functions work in lock-step to
   produce an algorithm for the compilation of "context" modules *)

(** This function is the entry point to the compilation *)
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
      [ (family_name, family_module_expr) ]

(** This function is responsible for the "includes"
 which is the main logic of the compilation *)
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
            CAst.make (Constrexpr.CMident finductive_ctx)
          in
          let finductive_signature_expr =
            CAst.make (Constrexpr.CMident compiled_signature)
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
    List.map (fun (name, ty) -> Backend.assume_parameter ~name ~ty) type_decls
  in
  let declare_csts_decls =
    List.map (fun (name, ty) -> Backend.assume_parameter ~name ~ty) constr_decls
  in
  let all_decls = declare_typedecls @ declare_csts_decls in
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name
       ~parameters:(famctx_to_parameters ~ctx) ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

let inductive_to_famterm_and_recursor_type ~(ind_def : Ftypes.VernacInductive.t)
    ~(ctx : Ftypes.FamilyContext.t) : Ftypes.CompiledModule.t =
  failwith ""

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
   2. Remove nested contexts since we don't yet have nested families
   3. Do we *really* need to define the compilation by memoized mutual recursion?
   4. Test
   5. Closing families *)
