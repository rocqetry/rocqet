open Types
open Bwd
open Bwd.Infix
module B = Backend.Vernac

(* Given
    Module A (ctxs : Ctxs ...). End A.

   return a new module that wraps inner part
      into a module
   Module A_ (ctxs : Ctxs ...).
        Module A'.
        Include A(ctxs).
        End A'.
   End A_.
*)
let wrap_module ~(module_name : Names.Id.t) ~(inner_module : CompiledModule.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) : CompiledModule.t =
  let open B in
  let temp_module_name =
    Naming.fresh_name ~prefix:(Names.Id.to_string module_name)
  in
  run
  @@ define_module ~module_name:temp_module_name ~parameters:ctx
       ~body:(fun ctx ->
         let* _ =
           B.define_module ~module_name ~parameters:[] ~body:(fun _ ->
               let module_expr =
                 Termutils.apply_module
                   ~functor_expr:(Termutils.ident_to_module_expr inner_module)
                   ~arguments:ctx
               in
               B.include_module ~module_expr)
         in
         return ())

let compile_inductive_signature ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModuleType.t =
  let module_name =
    let inductive_name = ind_def |> VernacInductive.extract_inductive_name in
    Naming.module_name_of ~family_name inductive_name
  in
  let all_decls =
    let type_decls, constr_decls =
      ind_def |> VernacInductive.extract_all_names_with_type |> List.split
    in
    type_decls @ List.concat constr_decls
    |> List.map (fun (name, ty) -> B.postulate_axiom ~name ~ty)
  in
  B.(
    run
    @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
           let* () = flatmap all_decls in
           return ()))

let compile_inductive_implementation ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModule.t
    * (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t =
  (* Generate a definition mapping of the inductive type and
     return the new inductive definition and the export of the correct names *)
  let modified_indcstrs, alias_all_name_term_type_decl =
    VernacInductive.definition_mapping ind_def
  in
  let type_names, constr_names =
    ind_def |> VernacInductive.extract_all_names |> List.split
  in
  let module_name =
    let original_ind_name = List.hd type_names in
    Naming.module_name_of ~family_name original_ind_name
  in

  (* Stuff for collecting recursors *)
  let possible_suffixes = RecKind.[ Ind; IndComplete; Rec; Rect ] in
  let defined_recursors :
      (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t ref =
    ref RecursorStore.empty
  in
  let remove_internal_prefix_map =
    let all_names = type_names @ List.concat constr_names in
    Naming.inv_name_map_with Naming.internal_name all_names
  in
  let collect_recursors_for ind_name () : unit B.t =
    let internal_name = Naming.internal_name ind_name in
    possible_suffixes
    |> List.iter (fun suffix ->
           (* This is only a potential recursor name, since _rec and _rect may not exist.
              For instance, if the type is Prop, _rec and _rect are impossible to derive. *)
           let potential_recursor =
             Nameops.add_suffix internal_name (RecKind.to_string suffix)
           in
           if Constrintern.is_global potential_recursor then
             let recursor_name =
               potential_recursor |> Constrexpr_ops.mkIdentC
             in
             let _ =
               B.run
               @@ B.define_term
                    ~name:
                      (Nameops.add_suffix ind_name (RecKind.to_string suffix))
                    recursor_name
             in
             let recursor_type =
               recursor_name |> Termutils.checked_type_of
               |> Termutils.reflect_checked_term
               |> Constrexpr_ops.replace_vars_constr_expr
                    remove_internal_prefix_map
             in
             defined_recursors :=
               RecursorStore.add suffix
                 ([ ind_name ], recursor_type)
                 !defined_recursors);
    B.return ()
  in
  let compiled_impl =
    B.(
      run
      @@ define_module ~module_name ~parameters:ctx ~body:(fun _ ->
             let* () = define_inductive modified_indcstrs in
             (* The default _ind principle is declared as if with `Scheme Minimality`,
                so we define "complete" principles that use `Scheme Induction` and are
                thus in line with _rec and _rect. *)
             let all_ind_comp_schemes =
               List.map
                 (fun ind_name ->
                   let internal_name = Naming.internal_name ind_name in
                   define_inductive_scheme
                     [
                       ( Nameops.add_suffix internal_name
                           RecKind.(to_string IndComplete),
                         internal_name,
                         Sorts.InProp );
                     ])
                 type_names
             in
             let* () = flatmap all_ind_comp_schemes in
             (* Now, we read from the environment all defined recursors and get their types. *)
             let collect_thunks =
               type_names
               |> List.map (fun ind_name ->
                      thunk (collect_recursors_for ind_name))
             in
             let* () = flatmap collect_thunks in

             let alias_all =
               List.map
                 (fun (original_name, new_name, ty) ->
                   define_term ~ty ~name:original_name new_name)
                 alias_all_name_term_type_decl
             in
             let* () = flatmap alias_all in
             return ()))
  in
  (compiled_impl, !defined_recursors)

let compile_recursors ~(ind_def : VernacInductive.t)
    ~(recursors : (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name =
  let all_names = ind_def |> VernacInductive.extract_all_names in
  let all_type_names = all_names |> List.map fst in
  let path_to_add = Naming.self_version family_name in
  let compile_one_recursor suffix (inductive_names, recursor) =
    (* Future-proofing for mutually inductive types *)
    let type_name = inductive_names |> Naming.concat_names in
    let recursor_name =
      Nameops.add_suffix type_name (RecKind.to_string suffix)
    in
    let module_name = Naming.module_name_of ~family_name recursor_name in
    let relevant_cstrs =
      inductive_names |> List.concat_map (fun n -> List.assoc n all_names)
    in
    let recursor =
      let name_set = all_type_names @ relevant_cstrs |> Names.Id.Set.of_list in
      Naming.add_path_constr_expr path_to_add name_set recursor
    in
    let handlers =
      (* Copied from FPOP almost verbatim: *)
      let from_recursor_type_to_subcase_handlers_constructor
          (cstname : Names.Id.t list) (recursor : Constrexpr.constr_expr) :
          (Names.Id.t * Constrexpr.constr_expr) list =
        let open Constrexpr in
        let open Constrexpr_ops in
        let isArrow { CAst.v = t; _ } =
          match t with CNotation (_, (_, "_ -> _"), _) -> true | _ -> false
        in
        let destDepProd { CAst.v = t; _ } =
          match t with
          | CProdN (al, b) -> (al, b)
          | _ -> Errors.fail ~info:"unexpected"
        in
        let destArrow { CAst.v = t; _ } =
          match t with
          | CNotation (_, (_, "_ -> _"), ([ domain; codomain ], _, _, _)) ->
              (domain, codomain)
          | _ -> Errors.fail ~info:"unreachable"
        in
        let _inputP, _body = destDepProd recursor in
        let rec collect_handler cstname f =
          match (cstname, f) with
          | _ :: t, f when isArrow f ->
              let currentT, remained_f = destArrow f in
              let ret, otherparts = collect_handler t remained_f in
              (ret, currentT :: otherparts)
          | [], f -> (f, [])
          | _, _ -> Errors.fail ~info:"unexpected"
        in
        let _, all_recursor_handlers = collect_handler cstname _body in
        let cst_name_corresponding_recursor_handlers_sig =
          List.combine cstname
            (* decorate each ai case with a _inputP *)
            (List.map
               (fun body -> mkLambdaCN _inputP body)
               all_recursor_handlers)
        in
        cst_name_corresponding_recursor_handlers_sig
      in
      from_recursor_type_to_subcase_handlers_constructor relevant_cstrs recursor
    in
    let compiled_handlers =
      handlers
      |> List.map (fun (case_name, raw_ty) ->
             let handler_type_name = Naming.handler_type case_name in
             let module_name =
               Nameops.add_prefix
                 (Names.Id.to_string type_name)
                 handler_type_name
               |> Naming.module_name_of ~family_name
             in
             let compiled_mod =
               B.run
               @@ B.define_module ~module_name ~parameters:ctx ~body:(fun _ ->
                      B.define_term ~name:handler_type_name raw_ty)
             in
             (case_name, compiled_mod))
    in
    let compiled_recursor =
      B.(
        run
        @@ define_module ~module_name ~parameters:ctx ~body:(fun _ ->
               let* () =
                 define_term
                   ~name:(Nameops.add_prefix "__recursor_type_" recursor_name)
                   recursor
               in
               return ()))
    in
    CompiledRecursor.{ inductive_names; compiled_recursor; handlers; compiled_handlers }
  in
  recursors |> RecursorStore.mapi compile_one_recursor

let compile_principle_signature ~(ind_def : VernacInductive.t)
    ~(recursors : (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name =
  let all_names = ind_def |> VernacInductive.extract_all_names in
  let all_type_names = all_names |> List.map fst in
  let path_to_add = Naming.self_version family_name in
  let compile_one_principle suffix (type_names, recursor) =
    (* Future-proofing for mutually inductive types *)
    let type_name = type_names |> Naming.concat_names in
    let recursor_name =
      Nameops.add_suffix type_name (RecKind.to_string suffix)
    in
    let module_name = Naming.module_name_of ~family_name recursor_name in
    let relevant_cstrs =
      type_names |> List.concat_map (fun n -> List.assoc n all_names)
    in
    let recursor =
      let name_set = all_type_names @ relevant_cstrs |> Names.Id.Set.of_list in
      Naming.add_path_constr_expr path_to_add name_set recursor
    in
    B.(
      run
      @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
             let* () = postulate_axiom ~name:recursor_name ~ty:recursor in
             return ()))
  in
  let principles = recursors |> RecursorStore.mapi compile_one_principle in
  let module_name =
    Naming.fresh_name ~prefix:(Names.Id.to_string family_name)
  in
  B.(
    run
    @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun arguments ->
           let* _ =
             principles |> RecursorStore.to_list
             |> List.map (fun (_, principle) ->
                    let module_expr =
                      Termutils.apply_module
                        ~functor_expr:(Termutils.ident_to_module_expr principle)
                        ~arguments
                    in
                    let* _ = include_module ~module_expr in
                    return ())
             |> flatmap
           in
           return ()))

let compile_principle_implementation ctx =
  let module_name = Naming.fresh_name ~prefix:"PrincipleImpl" in
  B.run
    (B.define_module ~module_name ~parameters:ctx ~body:(fun _ -> B.return ()))

let compile_motives ~(names : Names.Id.t list)
    ~(motives : Constrexpr.constr_expr list)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModule.t =
  let module_name =
    Naming.module_name_of ~family_name
      (Nameops.add_prefix "motive_of" (Naming.concat_names names))
  in
  B.run
  @@ B.define_module ~module_name ~parameters:ctx ~body:(fun _ ->
         List.combine names motives
         |> List.map (fun (name, motive) ->
                let name = Naming.motive_of name in
                B.define_term ~name motive)
         |> B.flatmap)

let compile_recursive_definition_signature 
    ~(names : Names.Id.t list)
    ~(motive_module : CompiledModule.t) ~(handler_cases : CompiledModule.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)    
    ~family_name
    ~(computational_behaviour : [ `Exposed | `Hidden ])
    ~(computational_axioms : (Names.Id.t * Constrexpr.constr_expr) list) :
    CompiledModuleType.t =  
  let module_name =
    Naming.module_name_of ~family_name (Naming.concat_names names)
  in
  let rec get_product_parameter_count (t : Constr.constr) : int =
    if Constr.isProd t then
      let _, _, body = Constr.destProd t in
      1 + get_product_parameter_count body
    else 0
  in
  motive_module |> ignore;
  B.(
    run
    @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun ctx ->
           let handler_cases =
             Termutils.apply_module
               ~functor_expr:(Termutils.ident_to_module_expr handler_cases)
               ~arguments:ctx
           in
           let* _ = include_module ~module_expr:handler_cases in
           let* _ =
             names
             |> List.map (fun name ->
                    let open Constrexpr_ops in
                    let motiveT = Naming.motive_of name |> mkIdentC in
                    (* This is evaluated inside the module, hence the thunk *)
                    thunk (fun () ->
                        let parameter_count =
                          motiveT |> Termutils.checked_type_of
                          |> get_product_parameter_count
                        in
                        let vars =
                          List.init parameter_count (fun x -> x + 1)
                          |> List.map (fun x ->
                                 "v" ^ string_of_int x |> Names.Id.of_string)
                        in
                        let binders =
                          vars
                          |> List.map (fun var ->
                                 let open Constrexpr in
                                 CLocalAssum
                                   ( [ CAst.make @@ Names.Name.mk_name var ],
                                     Default Glob_term.Explicit,
                                     CAst.make @@ CHole None ))
                        in
                        let func_body =
                          mkAppC (motiveT, vars |> List.map mkIdentC)
                        in
                        let prod_type = mkProdCN binders func_body in
                        assume_parameter ~name ~ty:prod_type))
             |> flatmap
           in
           (* Computational Axioms *)
           let* () =
             match computational_behaviour with
             | `Exposed ->
                 let* _ =
                   thunk (fun () ->
                       computational_axioms
                       |> List.map (fun (name, ty) -> postulate_axiom ~name ~ty)
                       |> flatmap |> run;
                       return ())
                 in
                 return ()
             | `Hidden -> return ()
           in
           return ()))

(* Return the compiled module and the generated computation behaviour *)
let compile_recursive_definition_implementation 
     ~inductive
    ~(provenance : Linkage.t) 
    ~recursor_name 
    ~handlers 
    ~(rec_principle_prefix : Libnames.qualid option)
    ~suffix ~ctx
    ~(handler_cases : CompiledModule.t) :
    CompiledModule.t * (Names.Id.t * Constrexpr.constr_expr) list =
  let module_name = Naming.fresh_name ~prefix:"RecImpl" in
  let computational_axioms = ref [] in
  let f ctx =
    let module_expr = Termutils.ident_to_module_expr handler_cases in
    let module_expr =
      Termutils.apply_module ~functor_expr:module_expr ~arguments:ctx
    in
    let inductive_name = inductive |> VernacInductive.extract_inductive_name in
    let handlers =
      handlers
      |> List.map (fun handler ->
             Naming.handler_name ~recursor:recursor_name ~case:handler)
      |> List.map Libnames.qualid_of_ident
      |> List.map Constrexpr_ops.mkRefC
    in
    let recursor =
      let recursor =
        Nameops.add_suffix inductive_name (RecKind.to_string suffix)
      in
      let recursor_path = Naming.qualid_point rec_principle_prefix recursor in
      (*let recursor_path =
        let prefix =
          Names.DirPath.make [ Naming.self_version provenance.name ]
        in
        Libnames.make_qualid prefix recursor
      in*)
      let motive =
        recursor_name |> Naming.motive_of |> Libnames.qualid_of_ident
        |> Constrexpr_ops.mkRefC
      in
      Constrexpr_ops.mkAppC
        (Constrexpr_ops.mkRefC recursor_path, motive :: handlers)
    in
    let open B in
    let* _ = include_module ~module_expr in
    let* _ = define_term ~name:recursor_name recursor in

    (* Generate the computational behaviour: *)
    let constructors =
      let _, constructors =
        inductive |> List.hd |> fst |> VernacInductive.extract_type_and_cstrs
      in
      constructors |> List.map fst
    in
    let auto_tactic (* : Tacexpr.raw_tactic_expr*) =
      let open Ltac_plugin in
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 (Libnames.qualid_of_ident (Names.Id.of_string "eauto"), []))))
    in
    let* () =
      thunk (fun () ->
          let result =
            Termutils.generate_computational_axioms 
              ~prefix:rec_principle_prefix
              ~provenance:provenance.name
              ~constructors ~recursor:recursor_name
          in
          computational_axioms := result;
          result
          |> List.map (fun (name, ty) ->
                 construct_term_using_proof ~name ~proof:auto_tactic ~ty ())
          |> flatmap |> run;
          return ())
    in
    return ()
  in
  let compiled_module =
    B.run (B.define_module ~module_name ~parameters:ctx ~body:f)
  in
  (compiled_module, !computational_axioms)

let compile_theorem_implementation ~(name : Names.Id.t)
    ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
    ~(compiled_handlers : CompiledModule.t) ~(motive_name : Names.Id.t)
    ~(inductive_name : Names.Id.t) ~(suffix : RecKind.t)
    ~(goal : Constrexpr.constr_expr) ~(provenance : Linkage.t)
    ~(handler_names : Names.Id.t list) =
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let open Constrexpr_ops in
  B.(
    run
    @@ define_module ~module_name ~parameters ~body:(fun ctx ->
           let module_expr =
             Termutils.apply_module
               ~functor_expr:(Termutils.ident_to_module_expr compiled_handlers)
               ~arguments:ctx
           in
           let* _ = B.include_module ~module_expr in
           let handler_names =
             handler_names
             |> List.map (fun handler ->
                    Naming.handler_name ~recursor:name ~case:handler)
           in
           let handler_names =
             handler_names
             |> List.map Libnames.qualid_of_ident
             |> List.map mkRefC
           in
           (* let inductive_principle =
                Naming.principle_name ~inductive:inductive_name
                  ~kind:(RecKind.to_string suffix)
                |> Libnames.qualid_of_ident |> mkRefC
              in*)
           let recursor =
             let recursor =
               Nameops.add_suffix inductive_name (RecKind.to_string suffix)
             in
             let recursor_path =
               let prefix =
                 Names.DirPath.make [ Naming.self_version provenance.name ]
               in
               Libnames.make_qualid prefix recursor
             in
             let motive =
               name |> Naming.motive_of |> Libnames.qualid_of_ident
               |> Constrexpr_ops.mkRefC
             in
             Constrexpr_ops.mkAppC
               (Constrexpr_ops.mkRefC recursor_path, motive :: handler_names)
           in
           (* let inductive_proof = mkAppC (inductive_principle, args) in *)
           goal |> ignore;
           motive_name |> ignore;
           let* _ = define_term ~name (* ~ty:goal*) recursor in
           return ()))

let compile_linkage_context ~field_name (context : LinkageCtx.t) :
    CompiledModuleType.t * (Names.Id.t * Constrexpr.module_ast) list =
  let linkage =
    match context with
    | LinkageCtx.Toplevel linkage -> linkage
    | LinkageCtx.Nested (_, linkage) -> linkage
  in
  let Linkage.{ fields; _ } = linkage in
  let module_name_ctx =
    Naming.fresh_name
      ~prefix:(Nameops.add_suffix field_name "Ctx" |> Names.Id.to_string)
  in
  (* Invariant: linkage.context contains self prefixed paths *)
  let parameters = Linkage.context_parameters linkage in
  match fields with
  | Bwd.Emp ->
      let signature_name =
        B.run
        @@ B.define_moduletype ~module_name:module_name_ctx
             ~parameters:(Bwd.to_list linkage.context) ~body:(fun _arguments ->
               B.return ())
      in
      let signature =
        Termutils.apply_module
          ~functor_expr:(Termutils.ident_to_module_expr signature_name)
          ~arguments:parameters
      in
      ( signature_name,
        linkage.context @> [ (Naming.self_version linkage.name, signature) ] )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.PrincipleDefinition
            { compiled_context; compiled_impl = compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.MetaDataSection
            { compiled_context; compiled_impl = compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.TheoremDefinition
            { compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.FamilyDefinition
            { compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.FieldDefinition
            { compiled_context; compiled_impl = compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.InductiveDefinition
            (* Exposed parameter *)
            { compiled_context; compiled_impl = compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.RecursorDefinition
            { compiled_context; compiled_signature; _ } ) ) ->
      let signature_name =
        B.(
          run
          @@ define_moduletype ~module_name:module_name_ctx
               ~parameters:(Bwd.to_list linkage.context)
               ~body:(fun _arguments ->
                 let ctx =
                   Termutils.apply_module
                     ~functor_expr:
                       (Termutils.ident_to_module_expr compiled_context)
                     ~arguments:parameters
                 in
                 let* () = include_module ~module_expr:ctx in
                 let signature =
                   Termutils.apply_module
                     ~functor_expr:
                       (Termutils.ident_to_module_expr compiled_signature)
                     ~arguments:parameters
                 in
                 let* () = include_module ~module_expr:signature in
                 return ()))
      in
      let signature =
        Termutils.apply_module
          ~functor_expr:(Termutils.ident_to_module_expr signature_name)
          ~arguments:parameters
      in
      ( signature_name,
        linkage.context @> [ (Naming.self_version linkage.name, signature) ] )

let compile_linkage (linkage : Linkage.t) =
  let Linkage.{ context; name; fields; _ } = linkage in
  let rec compile_fields fields (ctx : CompiledModule.t list) =
    match fields with
    | Bwd.Emp -> B.return ()
    | Bwd.Snoc (fields, (_, LinkageElem.RecursorDefinition { compiled_impl; _ }))
    | Bwd.Snoc (fields, (_, LinkageElem.TheoremDefinition { compiled_impl; _ }))
    | Bwd.Snoc (fields, (_, LinkageElem.FamilyDefinition { compiled_impl; _ }))
    | Bwd.Snoc (fields, (_, LinkageElem.MetaDataSection { compiled_impl; _ }))
    | Bwd.Snoc
        (fields, (_, LinkageElem.PrincipleDefinition { compiled_impl; _ }))
    | Bwd.Snoc (fields, (_, LinkageElem.FieldDefinition { compiled_impl; _ }))
    | Bwd.Snoc
        (fields, (_, LinkageElem.InductiveDefinition { compiled_impl; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in
        let module_expr = Termutils.ident_to_module_expr compiled_impl in
        let module_expr =
          Termutils.apply_module ~functor_expr:module_expr
            ~arguments:(Linkage.context_parameters linkage)
        in
        let* _ = include_module ~module_expr in
        return ()
  in
  B.run
  @@ B.define_module ~module_name:name ~parameters:(Bwd.to_list context)
       ~body:(compile_fields fields)

let compile_nested_linkage (linkage : Linkage.t) =
  let prefix = Names.Id.to_string (Nameops.add_suffix linkage.name "Impl") in
  let body =
    compile_linkage { linkage with name = Naming.fresh_name ~prefix }
  in
  let wrapper = Naming.fresh_name ~prefix in
  B.(
    run
    @@ define_module ~module_name:wrapper
         ~parameters:(Bwd.to_list linkage.context) ~body:(fun _ctx ->
           let* _ =
             define_module ~module_name:linkage.name ~parameters:[]
               ~body:(fun _ ->
                 let arguments =
                   linkage.context |> Bwd.to_list |> List.map fst
                   |> List.map Libnames.qualid_of_ident
                 in
                 let module_expr =
                   Termutils.apply_module
                     ~functor_expr:(Termutils.ident_to_module_expr body)
                     ~arguments
                 in
                 let* _ = include_module ~module_expr in
                 return ())
           in
           return ()))

let compile_linkage_signature linkage =
  let Linkage.{ name; fields; context; _ } = linkage in
  let helper = Naming.fresh_name ~prefix:"HelperSig" in
  let helper_module =
    match fields with
    | Bwd.Emp ->
        B.(
          run
          @@ define_moduletype ~module_name:helper
               ~parameters:(Bwd.to_list context) ~body:(fun _ctx -> return ()))
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.FamilyDefinition
              { compiled_context; compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.MetaDataSection
              { compiled_context; compiled_impl = compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.FieldDefinition
              { compiled_context; compiled_impl = compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            (* Exposed parameter *)
            LinkageElem.InductiveDefinition
              { compiled_context; compiled_impl = compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.PrincipleDefinition
              { compiled_context; compiled_impl = compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.TheoremDefinition
              { compiled_context; compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.RecursorDefinition
              { compiled_context; compiled_signature; _ } ) ) ->
        B.(
          run
          @@ define_moduletype ~module_name:helper
               ~parameters:(Bwd.to_list context) ~body:(fun ctx ->
                 let context_module_expr =
                   Termutils.apply_module
                     ~functor_expr:
                       (Termutils.ident_to_module_expr compiled_context)
                     ~arguments:ctx
                 in
                 let* _ = include_module ~module_expr:context_module_expr in
                 let signature_module_expr =
                   Termutils.apply_module
                     ~functor_expr:
                       (Termutils.ident_to_module_expr compiled_signature)
                     ~arguments:ctx
                 in
                 let* _ = include_module ~module_expr:signature_module_expr in
                 return ()))
  in
  let sig_final = Naming.fresh_name ~prefix:"Sig" in
  B.(
    run
    @@ define_moduletype ~module_name:sig_final
         ~parameters:(Bwd.to_list context) ~body:(fun ctx ->
           let helper_module_expr =
             Termutils.apply_module
               ~functor_expr:(Termutils.ident_to_module_expr helper_module)
               ~arguments:ctx
           in
           (* Declare Name : Helper *)
           let* _ = declare_module ~module_name:name helper_module_expr in
           return ()))

let compile_definition ~(name : Names.Id.t)
    ?(body_type : Constrexpr.constr_expr option)
    ~(body_expr : Constrexpr.constr_expr) parameters =
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  B.(
    run
    @@ define_module ~module_name ~parameters ~body:(fun _ ->
           let* () = define_term ~name ?ty:body_type body_expr in
           return ()))

let include_handler_types (provenance : Linkage.t)
    (recursor : CompiledRecursor.t) =
  let open B in
  recursor.compiled_handlers
  |> List.map (fun (_case_name, handler_module) ->
         let arguments =
           let family =
             provenance.name |> Naming.self_version |> Libnames.qualid_of_ident
           in
           Linkage.context_parameters provenance @ [ family ]
         in
         let module_expr =
           Termutils.apply_module
             ~functor_expr:(Termutils.ident_to_module_expr handler_module)
             ~arguments
         in
         let* _ = include_module ~module_expr in
         return ())
  |> flatmap

let compile_handler_cases ~name ~(context : LinkageCtx.t) ~parameters ~motive
    ~(handler_cases : (Names.Id.t * Constrexpr.constr_expr) list)
    ~(handler_types : (Names.Id.t * Constrexpr.constr_expr) list)
    ~(compiled_handler_types : CompiledModule.t) ~(provenance : Linkage.t)
    ~(recursor : CompiledRecursor.t) =
  let family = context |> Env.Context.family_name |> Names.Id.to_string in
  let module_name =
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Cases" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let open B in
  run
  @@ define_module ~module_name ~parameters ~body:(fun arguments ->
         let applied_motive =
           Termutils.apply_module
             ~functor_expr:(Termutils.ident_to_module_expr motive)
             ~arguments
         in
         let applied_compilerd_handler_types =
           Termutils.apply_module
             ~functor_expr:
               (Termutils.ident_to_module_expr compiled_handler_types)
             ~arguments
         in
         let* _ = include_module ~module_expr:applied_motive in
         let* _ = include_module ~module_expr:applied_compilerd_handler_types in
         (* let* _ = include_handler_types provenance recursor in *)
         provenance |> ignore;
         recursor |> ignore;
         let* _ =
           handler_cases
           |> List.map (fun (case_name, case) ->
                  match List.assoc_opt case_name handler_types with
                  | None ->
                      Errors.fail
                        ~info:
                          (Printf.sprintf "Couldn't find handler type for %s"
                             (Names.Id.to_string case_name))
                  | Some ty ->
                      let name =
                        Nameops.add_prefix (Names.Id.to_string name) case_name
                      in
                      define_term ~name ~ty case)
           |> flatmap
         in
         return ())

let aggregate_handler_types (recursor : CompiledRecursor.t) parameters =
  let open B in
  let f ctx =
    recursor.compiled_handlers
    |> List.map (fun (_case_name, handler_module) ->
           let module_expr =
             Termutils.apply_module
               ~functor_expr:(Termutils.ident_to_module_expr handler_module)
               ~arguments:ctx
           in
           let* _ = include_module ~module_expr in
           return ())
    |> flatmap
  in
  let module_name = Naming.fresh_name ~prefix:"Handlers" in
  B.run @@ B.define_module ~module_name ~parameters ~body:f

(* We should be keeping track of a context *)
let rec recompute_linkage (linkage : Linkage.t) =
  let lookup (linkage : Linkage.t) name =
    linkage.fields
    |> Bwd.find_map (fun (field_name, elem) ->
           match elem with
           | LinkageElem.FamilyDefinition { linkage; _ }
             when Names.Id.equal name field_name ->
               Some linkage
           | _ -> None)
  in
  let empty_linkage = { linkage with fields = Bwd.Emp } in
  let f linkage (name, field) =
    match field with
    | LinkageElem.PrincipleDefinition _ -> linkage
    | LinkageElem.FieldDefinition { body_expr; body_type; _ } ->
        let compiled_context, parameters =
          compile_linkage_context ~field_name:name (LinkageCtx.Toplevel linkage)
        in
        let compiled_impl =
          compile_definition ~name ?body_type ~body_expr parameters
        in
        let elem =
          LinkageElem.FieldDefinition
            { body_expr; body_type; compiled_context; compiled_impl }
        in
        { linkage with fields = Bwd.Snoc (linkage.fields, (name, elem)) }
    | LinkageElem.MetaDataSection _ ->
        { linkage with fields = Bwd.Snoc (linkage.fields, (name, field)) }
    | LinkageElem.FamilyDefinition { linkage = nested_linkage; _ } ->
        (* Late binding of family names *)
        let nested_linkage =
          match nested_linkage.base with
          | None -> nested_linkage
          | Some base -> (
              match lookup linkage base.name with
              | None -> nested_linkage
              | Some base ->
                  (* We can also imagine this being done for regular
                     base families. But is that needed? *)
                  let base =
                    Linkage.path_subtitution base
                      ~source:(Naming.self_version base.name)
                      ~target:(Naming.self_version nested_linkage.name)
                  in
                  Linkage.concatenate_recursive ~base ~derived:nested_linkage)
        in
        let compiled_context, parameters =
          compile_linkage_context ~field_name:nested_linkage.name
            (LinkageCtx.Toplevel linkage)
        in
        let nested_linkage =
          { nested_linkage with context = Bwd.of_list parameters }
        in
        let nested_linkage = recompute_linkage nested_linkage in
        let signature = compile_linkage_signature nested_linkage in
        let impl = compile_nested_linkage nested_linkage in
        let elem =
          LinkageElem.FamilyDefinition
            {
              linkage = nested_linkage;
              compiled_context;
              compiled_signature = signature;
              compiled_impl = impl;
            }
        in
        { linkage with fields = Bwd.Snoc (linkage.fields, (name, elem)) }
    | LinkageElem.InductiveDefinition { inductive; _ } ->
        let inductive_name = VernacInductive.extract_inductive_name inductive in
        let compiled_context, parameters =
          compile_linkage_context ~field_name:inductive_name
            (LinkageCtx.Toplevel linkage)
        in
        let compiled_signature =
          compile_inductive_signature ~ind_def:inductive ~ctx:parameters
            ~family_name:linkage.name
        in
        let compiled_impl, recursors =
          compile_inductive_implementation ~ind_def:inductive ~ctx:parameters
            ~family_name:linkage.name
        in
        let compiled_recursors =
          ref
            CompiledRecursors.
              { compiled_context; recursors = RecursorStore.empty }
        in
        let elem =
          LinkageElem.InductiveDefinition
            {
              inductive;
              compiled_context;
              compiled_impl;
              compiled_signature;
              compiled_recursors;
            }
        in
        let next_linkage =
          { linkage with fields = Bwd.Snoc (linkage.fields, (name, elem)) }
        in
        let compiled_context, parameters =
          compile_linkage_context ~field_name:inductive_name
            (LinkageCtx.Toplevel next_linkage)
        in
        let principle_signature =
          compile_principle_signature ~ind_def:inductive ~recursors
            ~ctx:parameters ~family_name:linkage.name
        in
        let principle_impl = compile_principle_implementation parameters in
        let principle =
          LinkageElem.PrincipleDefinition
            {
              compiled_context;
              inductive;
              compiled_signature = principle_signature;
              compiled_impl = principle_impl;
            }
        in
        let name = Nameops.add_suffix name "IndPrinciple" in
        let next_linkage =
          {
            next_linkage with
            fields = Bwd.Snoc (next_linkage.fields, (name, principle));
          }
        in
        let recursors =
          compile_recursors ~ind_def:inductive ~recursors ~ctx:parameters
            ~family_name:linkage.name
        in
        (compiled_recursors := CompiledRecursors.{ compiled_context; recursors });
        next_linkage
    | LinkageElem.TheoremDefinition
        { names; motives; inductive; suffix; handlers; _ } ->
        let name = List.hd names in
        let context = LinkageCtx.Toplevel linkage in
        let family_name = Env.Context.family_name context in
        let compiled_context, parameters =
          compile_linkage_context ~field_name:name context
        in
        let compiled_motive =
          compile_motives ~names ~ctx:parameters ~motives ~family_name
        in
        let inductive_name = VernacInductive.extract_inductive_name inductive in
        let inductive, compiled_recursors, provenance =
          Env.Context.lookup_inductive_for_recursion
            ~name:(Libnames.qualid_of_ident inductive_name)
            context
        in
        let recursor = RecursorStore.find suffix compiled_recursors.recursors in
        let handler_type_prefix = Naming.fresh_name ~prefix:"HandlerTypes" in
        let handler_types =
          let prefix x =
            Libnames.make_qualid (Names.DirPath.make [ handler_type_prefix ]) x
          in
          let the_motive =
            name |> Naming.motive_of |> Libnames.qualid_of_ident
            |> Constrexpr_ops.mkRefC
          in
          handlers
          |> List.map (fun (name, _) ->
                 ( name,
                   Constrexpr_ops.mkRefC @@ prefix (Naming.handler_type name) ))
          |> List.map (fun (name, expr) ->
                 (name, Constrexpr_ops.mkAppC (expr, [ the_motive ])))
        in
        let goal =
          Termutils.calculate_inductive_proof_goal ~theorem_name:name
            ~handler_names:(List.map fst handlers) ~handler_type_prefix ~suffix
        in
        let impl_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
        let compiled_handler_types =
          let handler_types = aggregate_handler_types recursor parameters in
          wrap_module ~module_name:handler_type_prefix
            ~inner_module:handler_types ~ctx:parameters
        in
        let compiled_handlers =
          compile_handler_cases ~name ~parameters ~context
            ~motive:compiled_motive ~handler_cases:handlers ~handler_types
            ~compiled_handler_types ~provenance ~recursor
        in
        let compiled_impl =
          compile_theorem_implementation ~name:impl_name ~parameters
            ~compiled_handlers ~motive_name:(Naming.motive_of name)
            ~inductive_name:(VernacInductive.extract_inductive_name inductive)
            ~suffix ~goal ~provenance ~handler_names:(List.map fst handlers)
        in
        let compiled_signature =
          compile_recursive_definition_signature ~names:[ name ]
            ~motive_module:compiled_motive ~handler_cases:compiled_handlers
            ~ctx:parameters
            ~family_name ~computational_behaviour:`Hidden
            ~computational_axioms:[]
        in
        let elem =
          LinkageElem.TheoremDefinition
            {
              names;
              goal;
              inductive;
              compiled_impl;
              compiled_signature;
              compiled_context;
              motives;
              compiled_handlers;
              handlers;
              suffix;
            }
        in
        { linkage with fields = Bwd.Snoc (linkage.fields, (name, elem)) }
    | LinkageElem.RecursorDefinition
        {
          inductive_path;
          handler_cases;
          handler_types;
          names;
          inductive;
          suffix;
          motives;
          arguments;
          _;
        } ->
        let name = List.hd names in
        let context = LinkageCtx.Toplevel linkage in
        let compiled_context, parameters =
          compile_linkage_context ~field_name:name context
        in
        let inductive_name = VernacInductive.extract_inductive_name inductive in
        let inductive, compiled_recursors, provenance =
          Env.Context.lookup_inductive_for_recursion
            ~name:(Libnames.qualid_of_ident inductive_name)
            context
        in
        Typechecking.check_exhaustive ~name ~inductive ~handlers:handler_cases;
        let motive_module =
          compile_motives ~names:[ name ] ~motives ~ctx:parameters
            ~family_name:name
        in
        let recursor = RecursorStore.find suffix compiled_recursors.recursors in
        let handlers = recursor.compiled_handlers |> List.map fst in
        let compiled_handler_types =
          aggregate_handler_types recursor parameters
        in
        let recursor_module =
          compile_handler_cases ~name ~parameters ~handler_cases ~handler_types
            ~compiled_handler_types ~context ~motive:motive_module ~provenance
            ~recursor
        in
        let rec_principle_prefix = Some (Libnames.qualid_of_ident @@ Naming.self_version @@ linkage.name) in 
        let compiled_impl, computational_axioms =
          compile_recursive_definition_implementation
            ~rec_principle_prefix
            ~inductive ~provenance
            ~recursor_name:name ~handlers ~suffix ~ctx:parameters
            ~handler_cases:recursor_module
        in
        let compiled_signature =
          compile_recursive_definition_signature
            ~handler_cases:recursor_module ~names:[ name ] ~motive_module
            ~ctx:parameters ~family_name:name ~computational_behaviour:`Exposed
            ~computational_axioms
        in
        let elem =
          LinkageElem.RecursorDefinition
            {
              handler_cases;
              inductive_path;
              motives;
              names = [ name ];
              inductive;
              recursor_module;
              motive_module;
              compiled_signature;
              compiled_impl;
              compiled_context;
              suffix;
              handler_types;
              arguments;
            }
        in
        { linkage with fields = Bwd.Snoc (linkage.fields, (name, elem)) }
  in
  Bwd.fold_left f empty_linkage linkage.fields
