open Types
open Bwd
open Bwd.Infix
module B = Backend.Vernac

let compile_empty_signature ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) :
    CompiledModuleType.t =
  let module_name = Naming.fresh_name ~prefix:"Empty" in
  B.(
    run
    @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ -> return ()))

let compile_inductive_signature ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModuleType.t =
  let module_name =
    let inductive_name = ind_def |> VernacInductive.extract_inductive_name in
    Naming.module_name_of ~family_name inductive_name
  in
  B.(
    run
    @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ -> return ()))

let compile_inductive_axiom ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) : CompiledModuleType.t =
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  B.run
  @@ B.define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
         B.postulate_axiom ~name ~ty)

let compile_inductive_implementation ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModule.t
    * (Names.Id.t * Constrexpr.constr_expr) list RecursorStore.t
    * Constrexpr.constr_expr RecursorStore.t =
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
  let possible_mutual_suffixes = RecKind.[ Rect; IndComplete ] in
  let defined_recursors :
      (Names.Id.t * Constrexpr.constr_expr) list RecursorStore.t ref =
    ref RecursorStore.empty
  in
  let defined_mutual_recursor : Constrexpr.constr_expr RecursorStore.t ref =
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
             let updater principle_store =
               match principle_store with
               | None -> Some [ (ind_name, recursor_type) ]
               | Some principle_store ->
                   Some ((ind_name, recursor_type) :: principle_store)
             in
             defined_recursors :=
               RecursorStore.update suffix updater !defined_recursors);
    B.return ()
  in
  (* Filter principles not defined on this inductive *)
  let filter_mutual_principle suffixes =
    if Termutils.is_prop_indexed_inductive ind_def then [ RecKind.IndComplete ]
    else
      suffixes
      |> List.filter_map (fun suffix ->
             RecursorStore.find_opt suffix !defined_recursors
             |> Option.map (Fun.const suffix))
  in
  let collect_mutual_recursor () : unit B.t =
    if List.length type_names > 1 then (
      possible_mutual_suffixes |> filter_mutual_principle
      |> List.iter (fun suffix ->
             let one_type_name = List.hd type_names in
             let principle =
               Naming.principle_name ~inductives:type_names
                 ~kind:(RecKind.to_string suffix)
             in
             let principle =
               Names.Id.of_string
                 (Names.Id.to_string one_type_name
                 ^ "_"
                 ^ Names.Id.to_string principle)
             in
             let recursor_type =
               principle |> Constrexpr_ops.mkIdentC |> Termutils.checked_type_of
               |> Termutils.reflect_checked_term
               |> Constrexpr_ops.replace_vars_constr_expr
                    remove_internal_prefix_map
             in
             defined_mutual_recursor :=
               RecursorStore.add suffix recursor_type !defined_mutual_recursor);
      B.return ())
    else B.return ()
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

             (* Mutual Inductive *)
             let define_mutual_inductive () =
               match type_names with
               | [] | [ _ ] -> return ()
               | inductives ->
                   possible_mutual_suffixes |> filter_mutual_principle
                   |> List.map (fun suffix ->
                          define_mutual_inductive_scheme ~inductives ~suffix)
                   |> flatmap
             in

             (* We thunk becuase we want to be aware of the defined principles *)
             let* () = thunk define_mutual_inductive in
             let* () = thunk collect_mutual_recursor in

             let alias_all =
               List.map
                 (fun (original_name, new_name, ty) ->
                   define_term ~ty ~name:original_name new_name)
                 alias_all_name_term_type_decl
             in
             let* () = flatmap alias_all in
             return ()))
  in
  (compiled_impl, !defined_recursors, !defined_mutual_recursor)

let compile_theorem_definition_signature ~(names : Names.Id.t list)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
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
  let return_module =
    B.(
      run
      @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ctx ->
             let* _ =
               names
               |> List.map (fun name ->
                      let open Constrexpr_ops in
                      let motive = Naming.motive_of name in
                      let motiveT =
                        let self =
                          Naming.self_version
                            (Env.Context.family_name (Env.Context.get ()))
                        in
                        let motive = Naming.list_to_path [ self; motive ] in
                        Constrexpr_ops.mkRefC motive
                      in
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
             return ()))
  in
  return_module

(* Return the compiled module and the type of this recursive definition *)
let compile_recursive_definition_signature ~(names : Names.Id.t list)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
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
  let return_module =
    B.(
      run
      @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ctx ->
             let* _ =
               names
               |> List.map (fun name ->
                      let open Constrexpr_ops in
                      (* let motiveT = Naming.motive_of name |> mkIdentC in*)
                      let motive = Naming.motive_of name in
                      let motiveT =
                        let self =
                          Naming.self_version
                            (Env.Context.family_name (Env.Context.get ()))
                        in
                        let motive = Naming.list_to_path [ self; motive ] in
                        Constrexpr_ops.mkRefC motive
                      in
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
             return ()))
  in
  return_module

let compile_finduction_implementation
      ~(recursor_names: Names.Id.t list)
      ~(inductive_paths: Libnames.qualid list)
      ~(suffix: RecKind.t)
      ~(goals: (Names.Id.t * Names.Id.t list) list)
      ~handlers =
  let prefix =
    let inductive_path = List.hd inductive_paths in
    match inductive_path |> Naming.path_to_list |> List.rev with
    | [] | [ _ ] -> None
    | _ :: path -> Some (path |> List.rev |> Naming.list_to_path)
  in
  (* We want to define handlers here *)
  (* Everything has to be in the right order for this to work *)
  let define_handlers =
    goals
    |> List.concat_map (fun (goal_name, handler_names) ->
           let open Constrexpr_ops in
           let implemented_handlers =
             Termutils.extract_handlers_from_inductive_proof handler_names
               (mkIdentC goal_name) suffix
           in
           implemented_handlers
           |> List.map (fun (constructor_name, handler) ->
             let name =
               Naming.handler_name ~recursors:recursor_names ~case:constructor_name
             in
             B.define_term ~name handler
         ))
    |> B.flatmap
  in
  let handlers =
      (* We expect that "inherit element" in inheritance.ml put the
         handlers in the right order.
         Thus, if there is ever a compilation failure about type errors
         due to handler order,
         inheritance.ml is not doing its job properly. *)
    handlers
    |> List.concat_map snd 
    |> List.map (fun case ->
         let handler =
            Naming.handler_name ~recursors:recursor_names ~case
         in
         handler |> Libnames.qualid_of_ident |> Constrexpr_ops.mkRefC)
  in  
  let computation =
    let motives =
      recursor_names
      |> List.map (fun recursor_name ->
             recursor_name |> Naming.motive_of |> Libnames.qualid_of_ident
             |> Constrexpr_ops.mkRefC)
    in    
    let open B in
    let inductives = inductive_paths |> List.map Naming.extract_path_base in
    let* _ =
      let* () = define_handlers in
      List.combine recursor_names inductives
      |> List.map (fun (name, inductive) ->
             let recursor =
               Naming.mutual_principle_name ~inductive ~inductives
                 ~kind:(RecKind.to_string suffix)
             in
             let recursor_path = Naming.qualid_point prefix recursor in
             let body =
               Constrexpr_ops.mkAppC
                 (Constrexpr_ops.mkRefC recursor_path, motives @ handlers)
             in
             define_term ~name body)
      |> flatmap
    in
    return ()
  in
  computation

(* Return the compiled module and the generated computational behaviour *)
let compile_recursive_definition_implementation
    ~(recursor_names : Names.Id.t list) ~handlers
    ~(inductive_paths : Libnames.qualid list) ~suffix ~handlers_table : unit B.t
    =
  let prefix =
    let inductive_path = List.hd inductive_paths in
    match inductive_path |> Naming.path_to_list |> List.rev with
    | [] | [ _ ] -> None
    | _ :: path -> Some (path |> List.rev |> Naming.list_to_path)
  in
  let computation =
    let motives =
      recursor_names
      |> List.map (fun recursor_name ->
             recursor_name |> Naming.motive_of |> Libnames.qualid_of_ident
             |> Constrexpr_ops.mkRefC)
    in
    let handlers =
      (* We expect that "inherit element" in inheritance.ml put the
         handlers in the right order.
         Thus, if there is ever a compilation failure about type errors
         due to handler order,
         inheritance.ml is not doing its job properly. *)
      handlers
      |> List.map (fun handler ->
             handlers_table |> List.assoc handler |> Libnames.qualid_of_ident
             |> Constrexpr_ops.mkRefC)
    in
    let open B in
    let inductives = inductive_paths |> List.map Naming.extract_path_base in
    let* _ =
      List.combine recursor_names inductives
      |> List.map (fun (name, inductive) ->
             let recursor =
               Naming.mutual_principle_name ~inductive ~inductives
                 ~kind:(RecKind.to_string suffix)
             in
             let recursor_path = Naming.qualid_point prefix recursor in
             let body =
               Constrexpr_ops.mkAppC
                 (Constrexpr_ops.mkRefC recursor_path, motives @ handlers)
             in
             define_term ~name body)
      |> flatmap
    in
    return ()
  in
  computation

let compile_computational_axiom_implementation ~axiom_name ~axiom_expr =
  let auto_tactic (* : Tacexpr.raw_tactic_expr*) =
    let open Ltac_plugin in
    CAst.make
      (Tacexpr.TacArg
         (Tacexpr.TacCall
            (CAst.make
               ( Libnames.qualid_of_ident (Names.Id.of_string "prove_comp_axiom"),
                 [] ))))
  in
  let ty = Naming.replace_self_qualification ~target:None axiom_expr in
  B.thunk
    (B.construct_term_using_proof ~is_starting_plain:true ~name:axiom_name
       ~proof:auto_tactic ~ty ~opaque:Vernacexpr.Opaque)

let compile_partial_recursor_implementation ~name ~type_name =
  let prove_prec_tactic =
    let proof =
      let open Ltac_plugin in
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 (Libnames.qualid_of_ident (Names.Id.of_string "prove_prec"), []))))
    in
    proof
  in
  let ty = Constrexpr_ops.mkIdentC type_name in
  B.thunk
    (B.construct_term_using_proof ~is_starting_plain:true ~name
       ~proof:prove_prec_tactic ~ty ~opaque:Vernacexpr.Transparent)

let compile_closing_fact_implementation ~name ~type_name
    ~(script : Ltac_plugin.Tacexpr.raw_tactic_expr) ~plain =
  let ty = Constrexpr_ops.mkIdentC type_name in
  B.thunk
    (B.construct_term_using_proof ~is_starting_plain:plain ~name ~proof:script
       ~ty ~opaque:Vernacexpr.Opaque)

(* The name of the equation to generate axioms for *)
let compile_computational_axiom_signature
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
    ~(constructor_name : Names.Id.t) ~(inductive : VernacInductive.t)
    ~(inductive_paths : Libnames.qualid list)
    ~(* Ind name -> Recursor Name *)
    (recursor_names : Names.Id.t Names.Id.Map.t)
    ~(prefix : Libnames.qualid option) :
    Names.Id.t * Constrexpr.constr_expr * CompiledModuleType.t =
  let inductive_names = inductive_paths |> List.map Naming.extract_path_base in
  let self__ =
    Naming.self_version (Env.Context.family_name (Env.Context.get ()))
  in
  let recursor_paths =
    recursor_names
    |> Names.Id.Map.map (fun recursor_name ->
           Naming.list_to_path [ self__; recursor_name ])
  in
  let constructor_path = Naming.qualid_point prefix constructor_name in
  let context = Some (Env.Context.get ()) in
  let module_name = Naming.fresh_name ~prefix:"ComputationalAxiom" in
  let axiom_name = ref None in
  let axiom_expr = ref None in
  let compiled_signature =
    B.run
    @@ B.define_moduletype ~module_name ~parameters:ctx ~body:(fun _ctx ->
           let open B in
           let* _ =
             thunk (fun () ->
                 let name, axiom =
                   Termutils.generate_one_computational_axiom ~inductive_names
                     ~inductive ~recursor_names ~recursor_paths
                     ~constructor_name ~constructor_path ~context
                 in
                 axiom_name := Some name;
                 axiom_expr := Some axiom;
                 postulate_axiom ~name ~ty:axiom)
           in
           return ())
  in
  (Option.get !axiom_name, Option.get !axiom_expr, compiled_signature)

let compile_prec_computational_axiom_signature
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
    ~(constructor_name : Names.Id.t) ~(constructor_path : Libnames.qualid)
    ~(handlers : Names.Id.t list) ~(inductive : VernacInductive.t)
    ~(prec_suffix : Names.Id.t) ~(recursor_path : Libnames.qualid) :
    Names.Id.t * Constrexpr.constr_expr * CompiledModuleType.t =
  let module_name = Naming.fresh_name ~prefix:"ComputationalAxiom" in
  let axiom_name = ref None in
  let axiom_expr = ref None in
  let compiled_signature =
    B.run
    @@ B.define_moduletype ~module_name ~parameters:ctx ~body:(fun _ctx ->
           let open B in
           let* _ =
             thunk (fun () ->
                 let name, axiom =
                   Termutils.generate_one_prec_computational_axiom ~inductive
                     ~recursor_path ~constructor_name ~constructor_path
                     ~prec_suffix ~handlers
                 in
                 axiom_name := Some name;
                 axiom_expr := Some axiom;
                 postulate_axiom ~name ~ty:axiom)
           in
           return ())
  in
  (Option.get !axiom_name, Option.get !axiom_expr, compiled_signature)

let normalize_parameters
    ~(default_ctx_params : (Names.Id.t * CompiledModule.t) list)
    ~(parameters : CompiledModule.t list) =
  let is_in_context (param : Libnames.qualid) =
    (* remove the location to avoid wrong equality comparison *)
    let parameters =
      parameters |> List.map (fun (p : Libnames.qualid) -> p.v)
    in
    let param = param.v in
    List.mem param parameters
  in
  (* Only use parameters that are in the context,
     other use the default param *)
  default_ctx_params
  |> List.map (fun (self_name, default) ->
         let self_name = Libnames.qualid_of_ident self_name in
         if is_in_context self_name then self_name else default)

let rec compile_linkage_context ~field_name (context : LinkageCtx.t) :
    CompiledModuleType.t * (Names.Id.t * Constrexpr.module_ast) list =
  let linkage =
    match context with
    | LinkageCtx.Toplevel linkage -> linkage
    | LinkageCtx.Nested (_, linkage) -> linkage
  in
  let Linkage.{ fields; _ } = linkage in
  let module_name_ctx () =
    Naming.fresh_name
      ~prefix:(Nameops.add_suffix field_name "Ctx" |> Names.Id.to_string)
  in
  (* Invariant: linkage.context contains self prefixed paths *)
  let parameters = Linkage.context_parameters linkage in
  match fields with
  | Bwd.Emp ->
      let signature_name =
        B.run
        @@ B.define_moduletype ~module_name:(module_name_ctx ())
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
  | Bwd.Snoc (fields, (_, TraitDefinition _)) ->
      let context =
        match context with
        | LinkageCtx.Toplevel linkage ->
            LinkageCtx.Toplevel { linkage with fields }
        | LinkageCtx.Nested (upper, linkage) ->
            LinkageCtx.Nested (upper, { linkage with fields })
      in
      compile_linkage_context ~field_name context
  | _ ->
      let fields = Linkage.fields_for_next_context linkage in
      let { LinkageElem.compiled_context; _ } = List.hd fields in
      let signature_name =
        B.(
          run
          @@ define_moduletype ~module_name:(module_name_ctx ())
               ~parameters:(Bwd.to_list linkage.context)
               ~body:(fun _arguments ->
                 let ctx =
                   Termutils.apply_module
                     ~functor_expr:
                       (Termutils.ident_to_module_expr compiled_context)
                     ~arguments:parameters
                 in
                 let* () = include_module ~module_expr:ctx in
                 fields
                 |> List.map
                      (fun
                        LinkageElem.
                          { default_ctx_params; compiled_signature; _ }
                      ->
                        let parameters =
                          normalize_parameters ~default_ctx_params ~parameters
                        in
                        let signature =
                          Termutils.apply_module
                            ~functor_expr:
                              (Termutils.ident_to_module_expr compiled_signature)
                            ~arguments:parameters
                        in
                        include_module ~module_expr:signature)
                 |> flatmap))
      in
      let signature =
        Termutils.apply_module
          ~functor_expr:(Termutils.ident_to_module_expr signature_name)
          ~arguments:parameters
      in
      ( signature_name,
        linkage.context @> [ (Naming.self_version linkage.name, signature) ] )

let compile_linkage_context ~field_name context =
  Env.Context.compute_or_pinned (fun () ->
      compile_linkage_context ~field_name context)

let synthesize_context ~(context : (Names.Id.t * Constrexpr.module_ast) Bwd.t)
    ~(module_name : Names.Id.t) ~(fields : (Names.Id.t * LinkageElem.t) Bwd.t) =
  let qualify name =
    [ module_name; name ] |> Naming.list_to_path |> Constrexpr_ops.mkRefC
  in
  let rec compile_fields (fields : (Names.Id.t * LinkageElem.t) Bwd.t) =
    match fields with
    | Bwd.Emp -> B.return ()
    | Snoc (fields, (_, LinkageElem.RecursorDefinition { names; _ })) ->
        let open B in
        let* _ = compile_fields fields in
        names
        |> List.map (fun name -> B.define_term ~name (qualify name))
        |> flatmap
    | Snoc (fields, (_, TheoremDefinition { names; _ })) ->
        let open B in
        let* _ = compile_fields fields in
        names
        |> List.map (fun name -> B.define_term ~name (qualify name))
        |> flatmap

    | Snoc (fields, (_, RecordDefinition { rd; _ } )) ->
       let open B in
       let* _ = compile_fields fields in
       let names =
         rd.name ::  List.map fst rd.fields
       in 
       names
       |> List.map (fun name -> B.define_term ~name (qualify name))
       |> flatmap
    | Snoc (fields, (_, (RecordComputationalAxiom { name; _} | ComputationalAxiom { name; _ }))) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    (* traits have no implmentation, so
       there's nothing to add in the context *)
    | Snoc (fields, (_, TraitDefinition _)) -> compile_fields fields
    | Snoc (fields, (name, FamilyDefinition _)) ->
        let open B in
        let* _ = compile_fields fields in
        let module_qualid = [ module_name; name ] |> Naming.list_to_path in
        let* _ =
          B.define_module_inline ~name
            ~value:(Termutils.ident_to_module_expr module_qualid)
        in
        return ()
    | Snoc (fields, (name, OpaqueFieldDefinition _)) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, FieldDefinition _)) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, ClosingFact _)) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, PartialRecursor _)) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (_, Marker _)) | Snoc (fields, (_, InductiveAxiom _))
    | Snoc (fields, (_, RecordConstrAxiom _))
    | Snoc (fields, (_, RecursiveAxiom _)) -> compile_fields fields
    | Snoc (fields, (_, InductiveDefinition { inductive; _ })) ->
        let open B in
        let* _ = compile_fields fields in
        let recs i =
          let suffixes =
            List.map RecKind.to_string RecKind.[ Ind; IndComplete; Rec; Rect ]
          in
          suffixes |> List.map (fun suffix -> Nameops.add_suffix i suffix)
        in
        let names =
          inductive |> VernacInductive.extract_all_names
          |> List.concat_map (fun (ind, ctrs) -> recs ind @ (ind :: ctrs))
        in
        names
        |> List.map (fun name -> B.define_term ~name (qualify name))
        |> flatmap
    | Snoc
        (fields, (_, MetaDataSection { compiled_impl; default_ctx_params; _ }))
      ->
        let open B in
        let* _ = compile_fields fields in
        let qualify name =
          [ name; Names.Id.of_string "Ctx" ] |> Naming.list_to_path
        in
        let parameters =
          let parameters =
            context |> Bwd.to_list
            |> List.map (fun (n, _) -> Libnames.qualid_of_ident n)
          in
          let parameters =
            normalize_parameters ~default_ctx_params ~parameters
          in
          match parameters with
          | [] -> []
          | l ->
              let l = List.tl l in
              let current =
                module_name |> Naming.self_version |> Libnames.qualid_of_ident
              in
              l @ [ current ]
        in
        let parameters =
          parameters
          |> List.map (fun parameter ->
                 parameter |> Naming.path_to_list |> List.hd
                 |> Naming.un_self_version |> qualify)
        in
        let module_expr = Termutils.ident_to_module_expr compiled_impl in
        let module_expr =
          Termutils.apply_module ~functor_expr:module_expr ~arguments:parameters
        in
        include_module ~module_expr
  in
  let ctx = Names.Id.of_string "Ctx" in
  B.run
  @@ B.define_module ~module_name:ctx ~parameters:[] ~body:(fun _ ->
         compile_fields fields)

type synth_ctx = {
  context : (Names.Id.t * Constrexpr.module_ast) Bwd.t;
  module_name : Names.Id.t;
  fields : (Names.Id.t * LinkageElem.t) Bwd.t;
}

let rec compile_linkage (synth_ctx : synth_ctx option) (linkage : Linkage.t) =
  let Linkage.{ name; fields; definition; _ } = linkage in
  let rec compile_fields fields (ctx : CompiledModule.t list) =
    match fields with
    | Bwd.Emp -> B.return ()
    | Snoc
        ( fields,
          ( _,
            LinkageElem.RecursorDefinition
              { inductive_paths; handlers; names; suffix; handlers_table; _ } )
        ) ->
        let open B in
        let* _ = compile_fields fields ctx in
        let handlers = handlers |> List.concat_map snd in
        compile_recursive_definition_implementation ~recursor_names:names
          ~handlers ~inductive_paths ~suffix ~handlers_table
    | Snoc
        ( fields,
          ( _,
            TheoremDefinition
              { inductive_paths; names; suffix; handlers; goals; _ } )
        ) ->
        let open B in
        let* _ = compile_fields fields ctx in        
        compile_finduction_implementation ~recursor_names:names ~inductive_paths ~suffix ~goals ~handlers
    | Snoc (fields, (_, (RecordComputationalAxiom { name; axiom; _ } | ComputationalAxiom { name; axiom; _ }))) ->
        let open B in
        let* _ = compile_fields fields ctx in
        compile_computational_axiom_implementation ~axiom_name:name
          ~axiom_expr:axiom       

    | Snoc (fields, (name, ClosingFact { type_name; script; plain; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in
        compile_closing_fact_implementation ~name ~type_name ~script ~plain
    | Snoc (fields, (_, PartialRecursor { name; type_name; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in
        compile_partial_recursor_implementation ~name ~type_name
    (* traits have no implementation *)
    | Snoc (fields, (_, TraitDefinition _)) -> compile_fields fields ctx
    (* Use the definition if we already have one *)
    | Snoc
        ( fields,
          ( _,
            FamilyDefinition
              { linkage = { name; definition = Some definition; _ }; _ } ) ) ->
        let open B in
        let* _ = compile_fields fields ctx in
        let value =
          definition |> Libnames.qualid_of_ident
          |> Termutils.ident_to_module_expr
        in
        define_module_inline ~name ~value
    | Snoc (fields, (_, FamilyDefinition { linkage = nested_linkage; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in
        thunk (fun () ->
            let synth_ctx =
              { context = linkage.context; module_name = linkage.name; fields }
            in
            let _ = compile_linkage (Some synth_ctx) nested_linkage in
            return ())

    (* Record definition *)
    | Snoc
       (fields, (_, RecordDefinition { rd; original; _ })) ->
       let open B in
       let* _ = compile_fields fields ctx in
       let __internal_original, _ = VernacInductive.definition_mapping original in
       let* _ = B.define_record __internal_original in
       let body = Constrexpr_ops.mkIdentC (Naming.internal_name rd.name) in 
       B.define_term ~name:rd.name body       

    (* Record constructors *)
    | Snoc (fields, (_, RecordConstrAxiom { name; record_name; defaults; fields = record_fields; _ })) ->
       (* The default values go after the arguments *)
       let open B in
       let* _ = compile_fields fields ctx in       
       let parameters =
         record_fields
         |> List.map Names.Id.to_string
         |> List.map (fun prefix -> Naming.fresh_name ~prefix)
       in
       let open Constrexpr_ops in
       let arguments = List.map mkIdentC parameters @ List.map mkRefC defaults in
       let body =         
         let main_record_constr =
           (* Record name is prefixed with `__internal_` because of "definition mapping" *)
           let record_name = Naming.internal_name record_name in
           Naming.rocq_record_constructor ~record_name          
         in 
         mkAppC (mkIdentC main_record_constr, arguments)
       in
       let body = Termutils.mk_lambda parameters body in
       (* Def X a b c = Y a b c <default-a> <default-b> <default-c> *)
       B.define_term ~name body  

    (* A marker has no implementation *)
    | Snoc (fields, (_, Marker _)) -> compile_fields fields ctx
    (* An implementation will be provided by the inductive *)
    | Snoc (fields, (_, InductiveAxiom _)) -> compile_fields fields ctx
    (* Implementation provided by RecursiveDefinition *)
    | Snoc (fields, (_, RecursiveAxiom _)) -> compile_fields fields ctx
    | Snoc
        (fields, (_, MetaDataSection { default_ctx_params; compiled_impl; _ }))
    | Snoc
        ( fields,
          (_, OpaqueFieldDefinition { default_ctx_params; compiled_impl; _ }) )
    | Snoc
        ( fields,
          (_, InductiveDefinition { default_ctx_params; compiled_impl; _ }) )
    | Snoc
        (fields, (_, FieldDefinition { default_ctx_params; compiled_impl; _ }))
      ->
        let open B in
        let qualify name =
          [ name; Names.Id.of_string "Ctx" ] |> Naming.list_to_path
        in
        (* Adjust parameters. Basically we're removing the "first" self
           because the context for a family will be nested as the
           first thing itself, so we need to access it with the name
           of the current family, not the upper family.
           In some sense, this is like shifting the parameters
           one "unit" to the right. *)
        let shift_parameters linkage parameters =
          let current =
            name |> Naming.self_version |> Libnames.qualid_of_ident
          in
          let rec next (lst : Libnames.qualid list) (name : Libnames.qualid) =
            match lst with
            | [] -> Some current
            | x :: rest ->
                if name.v = x.v then
                  match rest with [] -> Some current | n :: _ -> Some n
                else next rest name
          in
          match parameters with
          | [] -> []
          | _ ->
              let ctx_params = Linkage.context_parameters linkage in
              parameters |> List.filter_map (next ctx_params)
        in
        let reparam, parameters =
          let parameters =
            normalize_parameters ~default_ctx_params
              ~parameters:(Linkage.context_parameters linkage)
          in
          (* We shouldn't shift "Reparam" parameters *)
          (* REPARAM; REPARAM; self__Imp *)
          let reparam, parameters =
            parameters
            |> List.partition (fun id ->
                   let n =
                     id |> Naming.path_to_list |> List.hd |> Names.Id.to_string
                   in
                   String.starts_with n ~prefix:"Reparam")
          in
          let parameters = shift_parameters linkage parameters in
          (reparam, parameters)
        in
        let parameters =
          parameters
          |> List.map (fun parameter ->
                 parameter |> Naming.path_to_list |> List.hd
                 |> Naming.un_self_version |> qualify)
        in
        let parameters = reparam @ parameters in
        let* _ = compile_fields fields ctx in
        let module_expr = Termutils.ident_to_module_expr compiled_impl in
        let module_expr =
          Termutils.apply_module ~functor_expr:module_expr ~arguments:parameters
        in
        let* _ = include_module ~module_expr in
        return ()
  in
  match definition with
  | None ->
      B.run
      @@ B.define_module ~module_name:name ~parameters:[] ~body:(fun ctx ->
             let open B in
             let* _ =
               (* Provide the context for a nested family, before
                  compiling fields *)
               B.thunk (fun () ->
                   match synth_ctx with
                   | None -> B.return ()
                   | Some { context; module_name; fields } ->
                       let _ =
                         synthesize_context ~context ~module_name ~fields
                       in
                       B.return ())
             in
             compile_fields fields ctx)
  | Some definition ->
      let value =
        definition |> Libnames.qualid_of_ident |> Termutils.ident_to_module_expr
      in
      B.run
      @@
      let open B in
      let* _ = define_module_inline ~name ~value in
      return (Libnames.qualid_of_ident name)

(* Compile a toplevel linkage *)
let compile_linkage = compile_linkage None

let compile_linkage_signature linkage =
  let Linkage.{ name; context; _ } = linkage in
  let helper = Naming.fresh_name ~prefix:"HelperSig" in
  let helper_module =
    match Linkage.fields_for_next_context linkage with
    | [] ->
        B.(
          run
          @@ define_moduletype ~module_name:helper
               ~parameters:(Bwd.to_list context) ~body:(fun _ctx -> return ()))
    | fields ->
        let { LinkageElem.compiled_context; _ } = List.hd fields in
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
                 let* () = include_module ~module_expr:context_module_expr in
                 fields
                 |> List.map
                      (fun
                        LinkageElem.
                          { default_ctx_params; compiled_signature; _ }
                      ->
                        let ctx =
                          normalize_parameters ~default_ctx_params
                            ~parameters:ctx
                        in
                        let signature_module_expr =
                          Termutils.apply_module
                            ~functor_expr:
                              (Termutils.ident_to_module_expr compiled_signature)
                            ~arguments:ctx
                        in
                        include_module ~module_expr:signature_module_expr)
                 |> flatmap))
  in
  let sig_final = Naming.fresh_name ~prefix:"Sig" in
  let include_signature =
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
  in
  (include_signature, helper_module)

(* linkage is definitionally equal to base *)
let compile_final_linkage_signature ~linkage ~(base : Libnames.qualid) =
  let Linkage.{ name; context; _ } = linkage in
  let sig_final = Naming.fresh_name ~prefix:"Sig" in
  B.(
    run
    @@ define_moduletype ~module_name:sig_final
         ~parameters:(Bwd.to_list context) ~body:(fun _ctx ->
           let module_expr = Termutils.ident_to_module_expr base in
           (* Module Name := Base. *)
           let* _ = define_module_inline ~name ~value:module_expr in
           (*let* _ = define_module ~module_name:name
                        ~parameters:[] ~body:(fun _ -> include_module ~module_expr)
             in*)
           return ()))

(* optimization for empty families with a single base *)
let compile_same_linkage_signature ~linkage ~signature ~default_ctx_params =  
  let Linkage.{ name; context; _ } = linkage in
  let sig_final = Naming.fresh_name ~prefix:"Sig" in
  let include_signature =
    B.(
      run
      @@ define_moduletype ~module_name:sig_final
           ~parameters:(Bwd.to_list context) ~body:(fun ctx ->
             let ctx =
               normalize_parameters ~default_ctx_params ~parameters:ctx
             in
             let helper_module_expr =
               Termutils.apply_module
                 ~functor_expr:(Termutils.ident_to_module_expr signature)
                 ~arguments:ctx
             in
             (* Declare Name : Helper *)
             let* _ = declare_module ~module_name:name helper_module_expr in
             return ()))
  in
  include_signature

let compile_definition ~(name : Names.Id.t)
    ?(body_type : Constrexpr.constr_expr option)
    ~(body_expr : Constrexpr.constr_expr) parameters =
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  B.(
    run
    @@ define_module ~module_name ~parameters ~body:(fun _ ->
           let* () = define_term ~name ?ty:body_type body_expr in
           return ()))

let compile_lemma_signature ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr)
    ~parameters =
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  B.(
    run
    @@ define_moduletype ~module_name ~parameters ~body:(fun _ ->
           let* () = postulate_axiom ~name ~ty in
           return ()))

let make_module_path head path =
  let head = Libnames.qualid_of_ident head in
  List.fold_left
    (fun module_path x -> Naming.qualid_point (Some module_path) x)
    head path

let calculate_containing_family ~(inductive_path : Libnames.qualid)
    ~(context : LinkageCtx.t) =
  let resolved_path = Resolver.resolve_qualid ~context ~qualid:inductive_path in
  resolved_path |> Naming.path_to_list |> List.hd

let calculate_rec_principle_prefix ~inductive_path ~context =
  let rec remove_last lst =
    match lst with
    | [] -> failwith "Empty list"
    | [ _ ] -> []
    | x :: xs -> x :: remove_last xs
  in
  let containing_family =
    calculate_containing_family ~context ~inductive_path
  in
  let path = inductive_path |> Naming.path_to_list |> remove_last in
  make_module_path containing_family path

let compile_default_params
    ~(context : (Names.Id.t * Constrexpr.module_ast) list) :
    (Names.Id.t * CompiledModule.t) list =
  let compile ~(names : CompiledModule.t list) =
    let module_name = Naming.fresh_name ~prefix:"Reparam" in
    let f = List.hd names in
    let arguments = List.tl names in
    B.run
    @@ B.define_module ~module_name ~parameters:[] ~body:(fun _ctx ->
           let module_expr =
             Termutils.apply_module
               ~functor_expr:(Termutils.ident_to_module_expr f)
               ~arguments
           in
           B.include_module ~module_expr)
  in
  let rec extract_idents (expr : Constrexpr.module_ast) =
    match expr.v with
    | Constrexpr.CMident name -> [ name ]
    | Constrexpr.CMapply (rest, name) -> name :: extract_idents rest
    | Constrexpr.CMwith (_, _) ->
        Errors.fail ~info:"extract_idents: too complex to extract ident"
  in
  let find (map : (Names.Id.t * CompiledModule.t) Bwd.t)
      (name : Libnames.qualid) =
    let map =
      Bwd.map (fun (name, expr) -> (Libnames.qualid_of_ident name, expr)) map
    in
    match map |> Bwd.to_list |> List.assoc name with
    | name -> name
    | exception Not_found ->
        let info =
          Printf.sprintf "compile_default_params: %s was not found"
            (Pretty.pretty_qualid name)
        in
        Errors.fail ~info
  in
  let mapping : (Names.Id.t * CompiledModule.t) Bwd.t = Bwd.Emp in
  (* This is too messy! TODO: make it *beautiful* *)
  List.fold_left
    (fun map (name, expr) ->
      let names = expr |> extract_idents |> List.rev in
      let f, args = (List.hd names, List.tl names) in
      let names = f :: List.map (find map) args in
      let compiled = compile ~names in
      Bwd.Snoc (map, (name, compiled)))
    mapping context
  |> Bwd.to_list
