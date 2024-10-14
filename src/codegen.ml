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
  B.(
    run
    @@ define_moduletype ~module_name ~parameters:ctx ~body:(fun _ -> return ()))

let compile_inductive_constr ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) : CompiledModuleType.t =
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  B.run
  @@ B.define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
         B.postulate_axiom ~name ~ty)

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
             let handler_type_name =
               Naming.handler_type case_name ~suffix:(RecKind.to_string suffix)
             in
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
                   ~name:
                     (Naming.recursor_type ~inductive:recursor_name
                        (RecKind.to_string suffix))
                   recursor
               in
               return ()))
    in
    CompiledRecursor.
      { inductive_names; compiled_recursor; handlers; compiled_handlers }
  in
  recursors |> RecursorStore.mapi compile_one_recursor

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
                let open B in
                let motive_name = Naming.motive_of name in
                let* () = B.define_term ~name:motive_name motive in
                return ())
         |> B.flatmap)

(* Return the compiled handler type for each case *)
let compile_handler_types ~(names : Names.Id.t list)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
    ~(recursor : CompiledRecursor.t) ~(inductive_path : Libnames.qualid)
    ~(cases : Names.Id.t list) : CompiledModule.t =
  let function_name = names |> List.hd in
  let prefix =
    Printf.sprintf "HandlerTypesFor_%s" (Names.Id.to_string function_name)
  in
  let module_name = Naming.fresh_name ~prefix in
  let implementing_handlers =
    recursor.handlers
    |> List.filter (fun (case_name, _) ->
           cases |> List.exists (( = ) case_name))
  in
  B.run
  @@ B.define_module ~module_name ~parameters:ctx ~body:(fun _ ->
         let open B in
         let* () =
           implementing_handlers
           |> List.map (fun (case_name, handler) ->
                  let handler_name =
                    Naming.recursion_handler_type ~function_name ~case_name
                  in
                  let target =
                    match inductive_path |> Naming.path_to_list |> List.rev with
                    | [] | [ _ ] -> None
                    | _ :: path -> Some (path |> List.rev |> Naming.list_to_path)
                  in
                  let handler =
                    Naming.replace_self_qualification ~target handler
                  in
                  let handler =
                    Resolver.resolve_constrexpr ~context:(Env.Context.get ())
                      ~expression:handler
                  in
                  let* () = B.define_term ~name:handler_name handler in
                  return ())
           |> flatmap
         in
         return ())

let compile_handler_case ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
    ~(name : Names.Id.t) ~(body : Constrexpr.constr_expr)
    ~(ty : Constrexpr.constr_expr) : CompiledModule.t =
  let prefix = Printf.sprintf "%s" (Names.Id.to_string name) in
  let module_name = Naming.fresh_name ~prefix in
  B.run
  @@ B.define_module ~module_name ~parameters:ctx ~body:(fun _ ->
         let open B in
         let* () = define_term ~name ~ty body in
         return ())

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

(* Return the compiled module and the generated computational behaviour *)
let compile_recursive_definition_implementation ~inductive_name ~recursor_name
    ~handlers ~(inductive_path : Libnames.qualid) ~suffix : unit B.t =
  let prefix =
    match inductive_path |> Naming.path_to_list |> List.rev with
    | [] | [ _ ] -> None
    | _ :: path -> Some (path |> List.rev |> Naming.list_to_path)
  in
  let computation =
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
      let recursor_path = Naming.qualid_point prefix recursor in
      let motive =
        recursor_name |> Naming.motive_of |> Libnames.qualid_of_ident
        |> Constrexpr_ops.mkRefC
      in
      Constrexpr_ops.mkAppC
        (Constrexpr_ops.mkRefC recursor_path, motive :: handlers)
    in
    let open B in
    let* _ = define_term ~name:recursor_name recursor in
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
               (Libnames.qualid_of_ident (Names.Id.of_string "eauto"), []))))
  in
  let ty = Naming.replace_self_qualification ~target:None axiom_expr in  
  B.thunk (B.construct_term_using_proof ~name:axiom_name ~proof:auto_tactic ~ty ~opaque:Vernacexpr.Opaque)

let compile_partial_recursor_implementation ~name ~type_name = 
  let prove_prec_tactic =      
     let proof = 
        let open Ltac_plugin in
        CAst.make 
          (Tacexpr.TacArg 
             (Tacexpr.TacCall 
                (CAst.make 
                   (Libnames.qualid_of_ident (Names.Id.of_string "prove_prec") ,[]))) ) 
      in      
      proof
  in  
  let ty = Constrexpr_ops.mkIdentC type_name in
  B.thunk (B.construct_term_using_proof ~name ~proof:prove_prec_tactic ~ty ~opaque:Vernacexpr.Transparent)

let compile_closing_fact_implementation ~name ~type_name ~(script: Ltac_plugin.Tacexpr.raw_tactic_expr) =   
  let ty = Constrexpr_ops.mkIdentC type_name in  
  B.thunk (B.construct_term_using_proof ~name ~proof:script ~ty ~opaque:Vernacexpr.Opaque)

(* The name of the equation to generate axioms for *)
let compile_computational_axiom_signature
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
    ~(constructor_name : Names.Id.t) ~(inductive : VernacInductive.t)
    ~(recursor_name : Names.Id.t) ~(prefix : Libnames.qualid option) :
    Names.Id.t * Constrexpr.constr_expr * CompiledModuleType.t =
  (* Actually will actually be self qualified *)
  let self__ =
    Naming.self_version (Env.Context.family_name (Env.Context.get ()))
  in
  let recursor_path = Naming.list_to_path [ self__; recursor_name ] in
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
                   Termutils.generate_one_computational_axiom ~inductive
                     ~recursor_name ~recursor_path ~constructor_name
                     ~constructor_path ~context
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
    ~(constructor_name : Names.Id.t)
    ~(constructor_path : Libnames.qualid)
    ~(handlers: Names.Id.t list)
    ~(inductive : VernacInductive.t)
    ~(prec_suffix: Names.Id.t)
    ~(recursor_path : Libnames.qualid) :    
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
                   Termutils.generate_one_prec_computational_axiom 
                     ~inductive
                     ~recursor_path ~constructor_name
                     ~constructor_path ~prec_suffix ~handlers
                 in
                 axiom_name := Some name;
                 axiom_expr := Some axiom;
                 postulate_axiom ~name ~ty:axiom)
           in
           return ())
  in
  (Option.get !axiom_name, Option.get !axiom_expr, compiled_signature)

let compile_theorem_implementation ~(name : Names.Id.t)
    ~(inductive_name : Names.Id.t) ~(suffix : RecKind.t)
    ~(handler_names : Names.Id.t list) ~inductive_path =
  let prefix =
    match inductive_path |> Naming.path_to_list |> List.rev with
    | [] | [ _ ] -> None
    | _ :: path -> Some (path |> List.rev |> Naming.list_to_path)
  in
  let open Constrexpr_ops in
  let open B in
  let handler_names =
    handler_names
    |> List.map (fun handler ->
           Naming.handler_name ~recursor:name ~case:handler)
  in
  let handler_names =
    handler_names |> List.map Libnames.qualid_of_ident |> List.map mkRefC
  in
  let recursor =
    let recursor =
      Nameops.add_suffix inductive_name (RecKind.to_string suffix)
    in
    let recursor_path = Naming.qualid_point prefix recursor in
    let motive =
      name |> Naming.motive_of |> Libnames.qualid_of_ident
      |> Constrexpr_ops.mkRefC
    in
    Constrexpr_ops.mkAppC
      (Constrexpr_ops.mkRefC recursor_path, motive :: handler_names)
  in
  let* _ = define_term ~name recursor in
  return ()

let normalize_parameters 
    ~(default_ctx_params : (Names.Id.t * CompiledModule.t) list)
    ~(parameters : CompiledModule.t list) =
  let default_params_len = List.length default_ctx_params in
  let params_len = List.length parameters in
  let compare_result = compare params_len default_params_len in
  if compare_result = 0 then parameters
  else if compare_result < 0 then
    (* The base context has more params.
       We need to reparameterize via adding dummy args *)    
    default_ctx_params    
    |> List.map (fun (real, fake) -> 
        let real = Libnames.qualid_of_ident real in
        if List.mem real parameters then real else fake)
  else
    (* if compare_result > 0 *)
    (* The current context in which we about to include the module 
       with parameters `default_ctx_param` has more parameters, so 
       we are use our own arguments since this context subsumes *)
    (* TODO: actually check that the names in `default_ctx_params` are in 
        `parameters` *)
    default_ctx_params
    |> List.map (fun (self_name, _) -> Libnames.qualid_of_ident self_name)    

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
          MetaDataSection
            {
              default_ctx_params;
              compiled_context;
              compiled_impl = compiled_signature;
              _;
            } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          ComputationalAxiom
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          InductiveAxiom
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          TheoremDefinition
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          OpaqueFieldDefinition
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          FieldDefinition
            {
              default_ctx_params;
              compiled_context;
              compiled_impl = compiled_signature;
              _;
            } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          PartialRecursor
            {
              default_ctx_params;
              compiled_context;
              compiled_signature;
              _;
            } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          InductiveDefinition
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          ClosingFact
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          FamilyDefinition
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          RecursorDefinition
            { default_ctx_params; compiled_context; compiled_signature; _ } ) )
    ->
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
                 let parameters =
                   normalize_parameters ~default_ctx_params ~parameters
                 in
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
    | Snoc (fields, (_, ComputationalAxiom { name; _ })) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, FamilyDefinition _)) ->
        let open B in
        let* _ = compile_fields fields in
        let module_qualid =
           [ module_name; name ] |> Naming.list_to_path
        in
        let* _ = B.define_module_inline ~name ~value:(Termutils.ident_to_module_expr module_qualid) in
        (*let* _ =
          B.define_module ~module_name:name ~parameters:[] ~body:(fun _ ->
              let module_qualid =
                [ module_name; name ] |> Naming.list_to_path
              in
              B.include_module
                ~module_expr:(Termutils.ident_to_module_expr module_qualid))
        in*)
        return ()
    | Snoc (fields, (name, OpaqueFieldDefinition _)) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, FieldDefinition _)) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, ClosingFact _ )) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (name, PartialRecursor _ )) ->
        let open B in
        let* _ = compile_fields fields in
        B.define_term ~name (qualify name)
    | Snoc (fields, (_, InductiveAxiom _)) -> compile_fields fields
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
          let parameters = context |> Bwd.to_list |> List.map (fun (n, _) -> Libnames.qualid_of_ident n) in
          let parameters = normalize_parameters ~default_ctx_params ~parameters in
          match parameters with
          | [] -> []
          | l ->
              let l = List.tl l in
              let current = module_name |> Naming.self_version |> Libnames.qualid_of_ident in
              l @ [ current ]
        in
        let parameters =
          parameters
          |> List.map (fun parameter ->
                 parameter 
                 |> Naming.path_to_list 
                 |> List.hd 
                 |> Naming.un_self_version 
                 |> qualify)
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
  let Linkage.{ name; fields; _ } = linkage in
  let rec compile_fields fields (ctx : CompiledModule.t list) =
    match fields with
    | Bwd.Emp -> B.return ()
    | Snoc
        ( fields,
          ( _,
            LinkageElem.RecursorDefinition
              { inductive_path; handlers; names; suffix; _ } ) ) ->
        let open B in
        let* _ = compile_fields fields ctx in
        let recursor_name = List.hd names in
        let inductive_name =
          inductive_path |> Naming.path_to_list |> List.rev |> List.hd
        in
        compile_recursive_definition_implementation ~inductive_name
          ~recursor_name ~handlers ~inductive_path ~suffix
    | Snoc
        ( fields,
          (_, TheoremDefinition { inductive_path; handlers; names; suffix; _ })
        ) ->
        let open B in
        let* _ = compile_fields fields ctx in
        let name = List.hd names in
        let inductive_name =
          inductive_path |> Naming.path_to_list |> List.rev |> List.hd
        in
        compile_theorem_implementation ~name ~inductive_name ~inductive_path
          ~suffix ~handler_names:handlers
    | Snoc (fields, (_, ComputationalAxiom { name; axiom; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in
        compile_computational_axiom_implementation ~axiom_name:name
          ~axiom_expr:axiom
    | Snoc (fields, (name, ClosingFact { type_name; script; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in        
        compile_closing_fact_implementation ~name ~type_name ~script
    | Snoc
        (fields, (_, PartialRecursor { name; type_name; _ })) -> 
        let open B in
        let* _ = compile_fields fields ctx in        
        compile_partial_recursor_implementation ~name ~type_name
    | Snoc (fields, (_, FamilyDefinition { linkage = nested_linkage; _ })) ->
        let open B in
        let* _ = compile_fields fields ctx in
        thunk (fun () ->
            let synth_ctx =
              { context = linkage.context; module_name = linkage.name; fields }
            in
            let _ = compile_linkage (Some synth_ctx) nested_linkage in
            return ())
    (* An implementation will be provided by the inductive *)
    | Snoc (fields, (_, InductiveAxiom _)) -> compile_fields fields ctx
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
        let reparam, parameters =
          let parameters = 
            normalize_parameters 
              ~default_ctx_params 
              ~parameters:(Linkage.context_parameters linkage) 
          in          
          (* We shouldn't shift "Reparam" parameters *)
          (* REPARAM; REPARAM; self__Imp *)          
          let reparam, parameters = 
            parameters 
            |> List.partition (fun id -> 
                 let n = id |> Naming.path_to_list |> List.hd |> Names.Id.to_string in 
                 String.starts_with n ~prefix:"Reparam")            
          in
          match parameters with
          | [] -> [], []
          | _ :: l ->              
              let current =
                name |> Naming.self_version |> Libnames.qualid_of_ident
              in
              reparam, l @ [ current ]
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
                   let _ = synthesize_context ~context ~module_name ~fields in
                   B.return ())
         in
         compile_fields fields ctx)

(* Compile a toplevel linkage *)
let compile_linkage = compile_linkage None

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
    | Snoc
        ( _,
          ( _,
            LinkageElem.FamilyDefinition
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Snoc
        ( _,
          ( _,
            ComputationalAxiom
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Snoc
        ( _,
          ( _,
            InductiveAxiom
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Snoc
        ( _,
          ( _,
            MetaDataSection
              {
                default_ctx_params;
                compiled_context;
                compiled_impl = compiled_signature;
                _;
              } ) )
    | Snoc
        ( _,
          ( _,
            FieldDefinition
              {
                default_ctx_params;
                compiled_context;
                compiled_impl = compiled_signature;
                _;
              } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            TheoremDefinition
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Bwd.Snoc
        ( _,
          ( _,
            PartialRecursor
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Bwd.Snoc
        ( _,
          ( _,
            ClosingFact
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Bwd.Snoc
        ( _,
          ( _,
            OpaqueFieldDefinition
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Bwd.Snoc
        ( _,
          ( _,
            InductiveDefinition
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        )
    | Bwd.Snoc
        ( _,
          ( _,
            RecursorDefinition
              { default_ctx_params; compiled_context; compiled_signature; _ } )
        ) ->
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
                 let ctx =
                   normalize_parameters ~default_ctx_params ~parameters:ctx
                 in
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

let compile_handler_cases ~name ~(context : LinkageCtx.t) ~parameters ~motive
    ~(handler_cases : (Names.Id.t * Constrexpr.constr_expr) list)
    ~(handler_types : (Names.Id.t * Constrexpr.constr_expr) list) =
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
         let* _ = include_module ~module_expr:applied_motive in
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

(*
Reparameterization: 

let reparameterize_less
      ~(derived: Linkage.t)
      ~(base: Linkage.t) =
  (* Assumption: derived.context > base.context *)
  (* 1. Get the extra parameters in base, param_diff *)  
  (* 2. Append it to the context of base *)
  (* 3. Reparam contexts, impl, and signatures *)
  (*
    
    base.context = A_b, B_b
    derived.context = A_d, B_d, C

    --------------------------------------------
    Q: Do we need to ensure the following hold?
       1. A_b == A_d
       2. B_b = B_d
       
    A: Actually we need the following to hold: 
       1. A_d <: A_b 
       2. B_d <: B_b
    ---------------------------------------------
       
    module compiled_signature (A_b) (B_b) {
      ...
    }
       ===>

    module new_compiled_signature (A_d) (B_d) (C) {
      compiled_signature (A_d) (B_d)
    }
    
   *)
  Errors.fail ~info:"TODO: reparam less"

  Module Type ty_dummy回10
       (self__A: BCtx回1)
       (self__B: CCtx回2 self__A)
       (self__C: DCtx回3 self__A self__B)
       (self__D: ty_dummyCtx回9 self__A self__B self__C).

  
let reparameterize
      ~(derived: Linkage.t)
      ~(base: Linkage.t) =
  let derived_len = Bwd.length derived.context in
  let base_len = Bwd.length base.context in
  let compare_result = compare derived_len base_len in
  if compare_result = 0 then base
  else if compare_result < 0 then
     (* The base context has more params.
        We need to reparameterize via adding dummy args *)
    Errors.fail ~info:"TODO: reparam more"
  else (* if compare_result > 0 *)
    (* The base context has less params.
        We just add extra unused params from the
        derived to it *)
    Errors.fail ~info:"TODO: reparam less"    
*)

(* Note that this is the context parameter,
   not the parameters to a field *)
(* self_0 => defualt_0
   ...
   self_1 => defualt_1 *)
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
    let map = Bwd.map (fun (name, expr) -> Libnames.qualid_of_ident name, expr) map in
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
