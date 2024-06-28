open Types
open Bwd
open Bwd.Infix

(* These should actually be a module name *)
module ModuleTerm = struct
  type t = Libnames.qualid
end

module ModuleType = struct
  type t = Libnames.qualid
end

(* The interface for a code generation backend *)
module type S = sig
  val assume_parameter : name:Names.Id.t -> ty:Constrexpr.constr_expr -> unit

  val define_moduletype :
    name:Names.Id.t ->
    parameters:(Names.Id.t * Constrexpr.module_ast) list ->
    body:(ModuleTerm.t list -> unit) ->
    Names.ModPath.t
end

(** Code generation backend by mutating internal state with declarations *)
module DeclareBackend = struct
  (** Declare a toplevel binding *)
  let define name body sigma =
    let udecl = UState.default_univ_decl in
    let scope = Locality.Global Locality.ImportDefaultBehavior in
    let kind = Decls.(IsDefinition Definition) in
    let cinfo = Declare.CInfo.make ~name ~typ:None () in
    let info = Declare.Info.make ~scope ~kind ~udecl ~poly:false () in
    Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma |> ignore

  (** Push a local binding to an environment *)
  let push_local (n, t) env =
    EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env
end

(** Code generation backend by writing and interpreting Vernacular commands explicitly *)
module VernacBackend = struct
  type expr =
    | Original of Vernacexpr.vernac_expr
    | TrySilent of Vernacexpr.vernac_expr
    | Thunk of (unit -> expr list)

  type 'a t = expr list * 'a

  let emit_vernac_expr ~silence (orgexpr : Vernacexpr.vernac_expr) : unit =
    let () =
      Feedback.msg_notice
      @@
      let open Pp in
      Ppvernac.pr_vernac_expr orgexpr ++ str "."
    in
    let open Vernacexpr in
    let expr = { control = []; attrs = []; expr = orgexpr } in
    let expr = CAst.make expr in
    let backtrace =
      Printexc.raw_backtrace_to_string @@ Printexc.get_callstack 10
    in
    let dummyst = Vernacstate.freeze_full_state () in
    try
      let _ = Vernacinterp.interp ~st:dummyst expr in
      ()
    with reraise ->
      let info =
        "Exception Info: " ^ Printexc.to_string reraise ^ "\n"
        ^ (Pp.string_of_ppcmds @@ CErrors.print reraise)
        ^ "\n\n"
      in
      let ver_exc =
        "Error happened during translation\n   "
        ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac_expr orgexpr)
        ^ "\n"
      in
      if not silence then
        Errors.fail ~info:(info ^ ver_exc ^ "Stack Trace \n" ^ backtrace ^ "\n")

  let rec emit = function
    | Original e -> emit_vernac_expr ~silence:false e
    | TrySilent e -> emit_vernac_expr ~silence:true e
    | Thunk f -> f () |> emit_list

  and emit_list exprs = exprs |> List.iter emit

  let vernac_ expr : unit t = ([ Original expr ], ())
  let vernacs_ exprs : unit t = (List.map (fun x -> Original x) exprs, ())
  let try_ expr : unit t = (List.map (fun x -> TrySilent x) expr, ())

  let thunk (e : unit -> unit t) : unit t =
    ([ Thunk (fun () -> fst @@ e ()) ], ())   

  let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
    let x_data, x' = x in
    let y_data, y = f x' in
    (x_data @ y_data, y)

  let ( let* ) x f = bind x f
  let ( >> ) x y = bind x (fun _ -> y)
  let return (x : 'a) : 'a t = ([], x)

  let rec flatmap xs : unit t =
    match xs with [] -> return () | h :: t -> h >> flatmap t

  let run (computation : 'a t) : 'a =
    let expr, result = computation in
    emit_list expr;
    result

  let define_inductive (ind_def : VernacInductive.t) : unit t =
    let open Vernacexpr in
    vernac_ (VernacSynPure (VernacInductive (Inductive_kw, ind_def)))

  let define_inductive_scheme
      (specs : (Names.Id.t * Names.Id.t * Sorts.family) list) : unit t =
    let open Vernacexpr in
    let scheme =
      specs
      |> List.map (fun (name, ind_name, sort) ->
             ( Some (CAst.make name),
               {
                 sch_type = SchemeInduction;
                 sch_qualid =
                   CAst.make
                   @@ Constrexpr.AN (Libnames.qualid_of_ident ind_name);
                 sch_sort = sort;
               } ))
    in
    vernac_ (VernacSynPure (VernacScheme scheme))

  let define_term ?(ty : Constrexpr.constr_expr option) ~(name : Names.Id.t)
      (expr : Constrexpr.constr_expr) : unit t =
    let open Vernacexpr in
    let fname_ = (CAst.make @@ Names.Name.mk_name name, None) in
    vernac_
      (VernacSynPure
         (VernacDefinition
            ( (NoDischarge, Decls.Definition),
              fname_,
              DefineBody ([], None, expr, ty) )))

  let open_module ~(module_name : Names.Id.t)
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list) : ModuleTerm.t t
      =
    let modname_ = CAst.make module_name in
    let parameters_ =
      List.map
        (fun (n, m) -> (None, [ CAst.make n ], (m, Declaremods.DefaultInline)))
        parameters
    in
    let* _ =
      vernac_
        (VernacSynterp
           (VernacDefineModule
              (None, modname_, parameters_, Declaremods.Check [], [])))
    in
    return @@ Libnames.qualid_of_ident module_name

  let close_module ~(module_name : Names.Id.t) : ModuleTerm.t t =
    let modname_ = CAst.make module_name in
    let* _ = vernac_ (VernacSynterp (VernacEndSegment modname_)) in
    return @@ Libnames.qualid_of_ident module_name

  let define_module ~(module_name : Names.Id.t)
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
      ~(body : ModuleTerm.t list -> unit t) : ModuleTerm.t t =
    let open Vernacexpr in
    let modname_ = CAst.make module_name in
    let parameters_ =
      List.map
        (fun (n, m) -> (None, [ CAst.make n ], (m, Declaremods.DefaultInline)))
        parameters
    in

    let inner_parameter =
      List.map (fun (n, _) -> Libnames.qualid_of_ident n) parameters
    in
    let* _ =
      vernac_
        (VernacSynterp
           (VernacDefineModule
              (None, modname_, parameters_, Declaremods.Check [], [])))
    in
    let* _ = body inner_parameter in
    let* _ = vernac_ (VernacSynterp (VernacEndSegment modname_)) in
    return @@ Libnames.qualid_of_ident module_name

  let declare_module ~(module_name : Names.Id.t) (ty : Constrexpr.module_ast) :
      unit t =
    let name = CAst.make module_name in
    let* _ =
      vernac_
        (VernacSynterp
           (VernacDeclareModule (None, name, [], (ty, Declaremods.DefaultInline))))
    in
    return ()

  let define_moduletype ~(module_name : Names.Id.t)
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
      ~(body : ModuleTerm.t list -> unit t) : ModuleType.t t =
    let open Vernacexpr in
    let modname_ = CAst.make module_name in
    let parameters_ =
      List.map
        (fun (n, m) -> (None, [ CAst.make n ], (m, Declaremods.DefaultInline)))
        parameters
    in

    let inner_parameter =
      List.map (fun (n, _) -> Libnames.qualid_of_ident n) parameters
    in
    let* _ =
      vernac_
        (VernacSynterp (VernacDeclareModuleType (modname_, parameters_, [], [])))
    in
    let* _ = body inner_parameter in
    let* _ = vernac_ (VernacSynterp (VernacEndSegment modname_)) in
    return @@ Libnames.qualid_of_ident module_name

  let include_module ~(module_expr : Constrexpr.module_ast) : unit t =
    vernac_
      (VernacSynterp
         (VernacInclude [ (module_expr, Declaremods.DefaultInline) ]))

  let assume_parameter ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr) :
      unit t =
    let open Vernacexpr in
    let fname_ = (CAst.make @@ name, None) in
    vernac_
      (VernacSynPure
         (VernacAssumption
            ( (NoDischarge, Decls.Definitional),
              Declaremods.NoInline,
              [ (NoCoercion, ([ fname_ ], ty)) ] )))

  let postulate_axiom ~(name : Names.Id.t) ~(ty : Constrexpr.constr_expr) :
      unit t =
    let open Vernacexpr in
    let fname_ = (CAst.make @@ name, None) in
    vernac_
      (VernacSynPure
         (VernacAssumption
            ( (NoDischarge, Decls.Logical),
              Declaremods.NoInline,
              [ (NoCoercion, ([ fname_ ], ty)) ] )))

  let construct_term_using_proof 
      ~(name : Names.Id.t)
      ~(proof : Ltac_plugin.Tacexpr.raw_tactic_expr)
      ~(ty : Constrexpr.constr_expr) () : unit t =
    let open Ltac_plugin in
    let interppfs = Tacinterp.interp proof in
    (* Construct proof for it *)
    let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, type_checked_goal =
      Constrintern.interp_constr_evars env evd ty
    in
    let info = Declare.Info.make () in
    let cinfo = Declare.CInfo.make ~name ~typ:type_checked_goal () in
    let is_starting_plain = true in
    let proof = Declare.Proof.start ~info ~cinfo evd in
    let proof =
      (* apply unfold if not starting_plain  *)
      if is_starting_plain then proof
      else
        let unfold_all_definition =
          let open Tacexpr in
          let open Genredexpr in
          let open Locus in
          let tac =
            TacAtom
              (TacReduce
                 ( Cbv (Redops.make_red_flag [ FDeltaBut [] ]),
                   { onhyps = None; concl_occs = AllOccurrences } ))
          in
          let intp_tac = Tacinterp.interp (CAst.make tac) in
          intp_tac
        in
        let unfolded_proof, _ = Declare.Proof.by unfold_all_definition proof in
        unfolded_proof
    in
    let proof, _ = Declare.Proof.by interppfs proof in
    let opaque = Vernacexpr.Opaque in
    let _ = Declare.Proof.save_regular ~proof ~opaque ~idopt:None in
    return ()
end

let compile_inductive_signature ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModuleType.t =
  let module_name =
    let inductive_name = ind_def |> VernacInductive.extract_inductive_name in
    Naming.module_name_of ~family_name inductive_name
  in
  let module Backend = VernacBackend in
  let all_decls =
    let type_decls, constr_decls =
      ind_def |> VernacInductive.extract_all_names_with_type |> List.split
    in
    type_decls @ List.concat constr_decls
    |> List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty)
  in
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

let compile_inductive_implementation ~(ind_def : VernacInductive.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModule.t
    * (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t =
  (* Generate a definition mapping of the inductive type and
     return the new inductive definition and the export of the correct names *)
  let modified_indcstrs, alias_all_name_term_type_decl =
    VernacInductive.definition_mapping ~prefix:"__internal_" ind_def
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
  (* let defined_recursors :
         ((Names.Id.t list * RecKind.t) * Constrexpr.constr_expr) Bwd.t ref =
       ref Bwd.Emp
     in*)
  let defined_recursors :
      (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t ref =
    ref RecursorStore.empty
  in
  let remove_internal_prefix_map =
    let all_names = type_names @ List.concat constr_names in
    Naming.inv_name_map_with (Nameops.add_prefix "__internal_") all_names
  in
  let open VernacBackend in
  let collect_recursors_for ind_name () : unit t =
    let internal_name = Nameops.add_prefix "__internal_" ind_name in
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
               define_term
                 ~name:(Nameops.add_suffix ind_name (RecKind.to_string suffix))
                 recursor_name
               |> run
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
    return ()
  in
  let compiled_impl =
    define_module ~module_name ~parameters:ctx ~body:(fun _ ->
        let* () = define_inductive modified_indcstrs in

        (* The default _ind principle is declared as if with `Scheme Minimality`,
           so we define "complete" principles that use `Scheme Induction` and are
           thus in line with _rec and _rect. *)
        let all_ind_comp_schemes =
          List.map
            (fun ind_name ->
              let internal_name = Nameops.add_prefix "__internal_" ind_name in
              define_inductive_scheme
                [
                  ( Nameops.add_suffix internal_name "_ind_comp",
                    internal_name,
                    Sorts.InProp );
                ])
            type_names
        in
        let* () = flatmap all_ind_comp_schemes in

        (* Now, we read from the environment all defined recursors and get their types. *)
        let collect_thunks =
          type_names
          |> List.map (fun ind_name -> thunk (collect_recursors_for ind_name))
        in
        let* () = flatmap collect_thunks in

        let alias_all =
          List.map
            (fun (original_name, new_name, ty) ->
              define_term ~ty ~name:original_name new_name)
            alias_all_name_term_type_decl
        in
        let* () = flatmap alias_all in
        return ())
    |> run
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
    let rec_handlers =
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
    let open VernacBackend in
    let compiled_handlers =
      rec_handlers
      |> List.map (fun (case_name, raw_ty) ->
             let handler_type_name =
               Nameops.add_prefix "__handler_type_" case_name
             in
             let module_name =
               Nameops.add_prefix
                 (Names.Id.to_string type_name)
                 handler_type_name
               |> Naming.module_name_of ~family_name
             in
             let compiled_mod =
               define_module ~module_name ~parameters:ctx ~body:(fun _ ->
                   define_term ~name:handler_type_name raw_ty)
               |> run
             in
             (case_name, compiled_mod))
    in
    let compiled_recursor =
      define_module ~module_name ~parameters:ctx ~body:(fun _ ->
          let* () =
            define_term
              ~name:(Nameops.add_prefix "__recursor_type_" recursor_name)
              recursor
          in
          return ())
      |> run
    in
    CompiledRecursor.{ inductive_names; compiled_recursor; compiled_handlers }
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
    let open VernacBackend in
    define_moduletype ~module_name ~parameters:ctx ~body:(fun _ ->
        let* () = postulate_axiom ~name:recursor_name ~ty:recursor in
        return ())
    |> run
  in
  let principles = recursors |> RecursorStore.mapi compile_one_principle in
  let module_name =
    Naming.fresh_name ~prefix:(Names.Id.to_string family_name)
  in
  let open VernacBackend in
  define_moduletype ~module_name ~parameters:ctx ~body:(fun arguments ->
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
      return ())
  |> run

let compile_principle_implementation ctx =
  let open VernacBackend in
  let module_name = Naming.fresh_name ~prefix:"PrincipleImpl" in
  define_module ~module_name ~parameters:ctx ~body:(fun _ -> return ()) |> run

let compile_motives ~(names : Names.Id.t list)
    ~(motives : Constrexpr.constr_expr list)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list) ~family_name :
    CompiledModule.t =
  let module_name =
    Naming.module_name_of ~family_name
      (Nameops.add_prefix "motive_of" (Naming.concat_names names))
  in
  let open VernacBackend in
  define_module ~module_name ~parameters:ctx ~body:(fun _ ->
      List.combine names motives
      |> List.map (fun (name, motive) ->
             let name = Naming.motive_of name in
             define_term ~name motive)
      |> flatmap)
  |> run

let compile_recursor_signature 
    ~(names : Names.Id.t list)
    ~(motive_module : CompiledModule.t)
    ~(handler_cases : CompiledModule.t)
    ~(ctx : (Names.Id.t * Constrexpr.module_ast) list)
    ~(provenance : Linkage.t)
    ~(handlers : Names.Id.t list)
    ~family_name :
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
  let open VernacBackend in
  motive_module |> ignore;
  define_moduletype ~module_name ~parameters:ctx ~body:(fun ctx ->
      (* let applied_motive =
        Termutils.apply_module
          ~functor_expr:(Termutils.ident_to_module_expr motive_module)
          ~arguments:ctx
      in
      let* _ = include_module ~module_expr:applied_motive in*)

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
                 let func_body = mkAppC (motiveT, vars |> List.map mkIdentC) in
                 let prod_type = mkProdCN binders func_body in
                 assume_parameter ~name ~ty:prod_type))
      |> flatmap 
      in 
      (* Computational Axioms *)
      let* _ = 
      thunk
        (fun () -> 
          let recursor = names |> List.hd in          
          let result = 
            Termutils.generate_computational_axioms 
                ~provenance:provenance.name
                ~constructors:handlers
                ~recursor
          in           
          result 
          |> List.map (fun (name, ty) -> 
                 postulate_axiom ~name ~ty) 
          |> flatmap |> run;
          return ())
      in
      return ())
  |> run

let compile_recursor_implementation ~inductive ~(provenance : Linkage.t)
    ~recursor_name ~handlers ~suffix ~ctx ~(handler_cases : CompiledModule.t) =
  let open VernacBackend in
  let module_name = Naming.fresh_name ~prefix:"RecImpl" in
  let f ctx =
    let module_expr = Termutils.ident_to_module_expr handler_cases in
    let module_expr =
      Termutils.apply_module ~functor_expr:module_expr ~arguments:ctx
    in
    let inductive_name = inductive |> VernacInductive.extract_inductive_name in
    let handlers =
      handlers
      |> List.map (fun handler ->
             Nameops.add_prefix (Names.Id.to_string recursor_name) handler)
      |> List.map Libnames.qualid_of_ident
      |> List.map Constrexpr_ops.mkRefC
    in
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
        recursor_name |> Naming.motive_of |> Libnames.qualid_of_ident
        |> Constrexpr_ops.mkRefC
      in
      Constrexpr_ops.mkAppC
        (Constrexpr_ops.mkRefC recursor_path, motive :: handlers)
    in
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
    let* _ = 
      thunk
        (fun () -> 
          let result = 
            Termutils.generate_computational_axioms 
                ~provenance:provenance.name
                ~constructors
                ~recursor:recursor_name 
          in           
          result 
          |> List.map (fun (name, ty) -> construct_term_using_proof ~name ~proof:auto_tactic ~ty ()) 
          |> flatmap |> run;
          return ())
    in    
    return ()
  in
  run (define_module ~module_name ~parameters:ctx ~body:f)

let compile_linkage_context ~field_name (context : LinkageCtx.t) :
    CompiledModuleType.t * (Names.Id.t * Constrexpr.module_ast) list =
  let open VernacBackend in
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
        define_moduletype ~module_name:module_name_ctx
          ~parameters:(Bwd.to_list linkage.context) ~body:(fun _arguments ->
            return ())
        |> run
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
            { compiled_context; compiled_signature; _ } ) )
  | Bwd.Snoc
      ( _,
        ( _,
          LinkageElem.RecursorDefinition
            { compiled_context; compiled_signature; _ } ) ) ->
      let signature_name =
        define_moduletype ~module_name:module_name_ctx
          ~parameters:(Bwd.to_list linkage.context) ~body:(fun _arguments ->
            let ctx =
              Termutils.apply_module
                ~functor_expr:(Termutils.ident_to_module_expr compiled_context)
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
            return ())
        |> run
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
  let open VernacBackend in
  let rec compile_fields fields (ctx : ModuleTerm.t list) =
    match fields with
    | Bwd.Emp -> return ()
    | Bwd.Snoc (fields, (_, LinkageElem.RecursorDefinition { compiled_impl; _ }))
    | Bwd.Snoc (fields, (_, LinkageElem.FamilyDefinition { compiled_impl; _ }))
    | Bwd.Snoc
        (fields, (_, LinkageElem.PrincipleDefinition { compiled_impl; _ }))
    | Bwd.Snoc (fields, (_, LinkageElem.FieldDefinition { compiled_impl; _ }))
    | Bwd.Snoc
        (fields, (_, LinkageElem.InductiveDefinition { compiled_impl; _ })) ->
        let* _ = compile_fields fields ctx in
        let module_expr = Termutils.ident_to_module_expr compiled_impl in
        let module_expr =
          Termutils.apply_module ~functor_expr:module_expr
            ~arguments:(Linkage.context_parameters linkage)
        in
        let* _ = include_module ~module_expr in
        return ()
  in
  define_module ~module_name:name ~parameters:(Bwd.to_list context)
    ~body:(compile_fields fields)
  |> run

let compile_nested_linkage (linkage : Linkage.t) =
  let prefix = Names.Id.to_string (Nameops.add_suffix linkage.name "Impl") in
  let body =
    compile_linkage { linkage with name = Naming.fresh_name ~prefix }
  in
  let wrapper = Naming.fresh_name ~prefix in
  let open VernacBackend in
  define_module ~module_name:wrapper ~parameters:(Bwd.to_list linkage.context)
    ~body:(fun _ctx ->
      let* _ =
        define_module ~module_name:linkage.name ~parameters:[] ~body:(fun _ ->
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
      return ())
  |> run

let compile_linkage_signature linkage =
  let open VernacBackend in
  let Linkage.{ name; fields; context; _ } = linkage in
  let helper = Naming.fresh_name ~prefix:"HelperSig" in
  let helper_module =
    match fields with
    | Bwd.Emp ->
        define_moduletype ~module_name:helper ~parameters:(Bwd.to_list context)
          ~body:(fun _ctx -> return ())
        |> run
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
              { compiled_context; compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.PrincipleDefinition
              { compiled_context; compiled_signature; _ } ) )
    | Bwd.Snoc
        ( _,
          ( _,
            LinkageElem.RecursorDefinition
              { compiled_context; compiled_signature; _ } ) ) ->
        define_moduletype ~module_name:helper ~parameters:(Bwd.to_list context)
          ~body:(fun ctx ->
            let context_module_expr =
              Termutils.apply_module
                ~functor_expr:(Termutils.ident_to_module_expr compiled_context)
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
            return ())
        |> run
  in
  let sig_final = Naming.fresh_name ~prefix:"Sig" in
  define_moduletype ~module_name:sig_final ~parameters:(Bwd.to_list context)
    ~body:(fun ctx ->
      let helper_module_expr =
        Termutils.apply_module
          ~functor_expr:(Termutils.ident_to_module_expr helper_module)
          ~arguments:ctx
      in
      (* Declare Name : Helper *)
      let* _ = declare_module ~module_name:name helper_module_expr in
      return ())
  |> run

let compile_definition ~(name : Names.Id.t)
    ?(body_type : Constrexpr.constr_expr option)
    ~(body_expr : Constrexpr.constr_expr) parameters =
  let open VernacBackend in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  define_module ~module_name ~parameters ~body:(fun _ ->
      let* () = define_term ~name ?ty:body_type body_expr in
      return ())
  |> run

let include_handler_types (provenance : Linkage.t)
    (recursor : CompiledRecursor.t) =
  let open VernacBackend in
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
    ~(provenance : Linkage.t) ~(recursor : CompiledRecursor.t) =
  let family = context |> Env.Context.family_name |> Names.Id.to_string in
  let module_name =
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Cases" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let open VernacBackend in
  run
  @@ define_module ~module_name ~parameters ~body:(fun arguments ->
         let applied_motive =
           Termutils.apply_module
             ~functor_expr:(Termutils.ident_to_module_expr motive)
             ~arguments
         in
         let* _ = include_module ~module_expr:applied_motive in
         let* _ = include_handler_types provenance recursor in
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
    | LinkageElem.RecursorDefinition
        { handler_cases; handler_types; names; inductive; suffix; motives; _ }
      ->
        let name = List.hd names in
        let context = LinkageCtx.Toplevel linkage in
        let compiled_context, parameters =
          compile_linkage_context ~field_name:name context
        in
        let inductive_name = VernacInductive.extract_inductive_name inductive in
        let _inductive, compiled_recursors, provenance =
          Env.Context.lookup_inductive_for_recursion
            ~name:(Libnames.qualid_of_ident inductive_name)
            context
        in
        (* We can check for exhaustivity here *)
        let motive_module =
          compile_motives ~names:[ name ] ~motives ~ctx:parameters
            ~family_name:name
        in
        let recursor = RecursorStore.find suffix compiled_recursors.recursors in
        let handlers = recursor.compiled_handlers |> List.map fst in
        let recursor_module =
          compile_handler_cases ~name ~parameters ~handler_cases ~handler_types
            ~context ~motive:motive_module ~provenance ~recursor
        in
        let compiled_signature =
          compile_recursor_signature 
            ~provenance
            ~handlers
            ~handler_cases:recursor_module
            ~names:[ name ] ~motive_module
            ~ctx:parameters ~family_name:name
        in
        let compiled_impl =
          compile_recursor_implementation ~inductive ~provenance
            ~recursor_name:name ~handlers ~suffix ~ctx:parameters
            ~handler_cases:recursor_module
        in
        let elem =
          LinkageElem.RecursorDefinition
            {
              handler_cases;
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
            }
        in
        { linkage with fields = Bwd.Snoc (linkage.fields, (name, elem)) }
  in

  Bwd.fold_left f empty_linkage linkage.fields
