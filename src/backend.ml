open Types
(* Code generation backend *)

(** "Vernacular Backend": Code generation backend by writing and interpreting Vernacular commands explicitly *)
module Vernac = struct
  type expr =
    | Original of Vernacexpr.vernac_expr
    (* | TrySilent of Vernacexpr.vernac_expr *)
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
    (* | TrySilent e -> emit_vernac_expr ~silence:true e *)
    | Thunk f -> f () |> emit_list

  and emit_list exprs = exprs |> List.iter emit

  let vernac_ expr : unit t = ([ Original expr ], ())
  (* let vernacs_ exprs : unit t = (List.map (fun x -> Original x) exprs, ())
     let try_ expr : unit t = (List.map (fun x -> TrySilent x) expr, ()) *)

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

  let end_proof (goal : Names.Id.t) : unit t =
    let open Vernacexpr in
    vernac_
    @@ VernacSynPure
         (VernacEndProof (Proved (Transparent, Some (CAst.make goal))))

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

  let define_mutual_inductive_scheme ~(inductives: Names.Id.t list) ~(suffix: RecKind.t) : unit t =
    let sort = match suffix with 
      | RecKind.Ind | RecKind.IndComplete -> Sorts.InProp
      | RecKind.Rec -> Sorts.InSet
      | RecKind.Rect -> Sorts.InType
    in 
    let joined_indnames = Naming.concat_names inductives in
    let indp_name = Nameops.add_suffix joined_indnames (RecKind.to_string suffix) in
    let internal_indp_name = Naming.internal_name indp_name in
    let names = 
      inductives
      |> List.map (fun inductive ->
         let defined_typename = Naming.internal_name inductive in
         let decorated_typename = CAst.make @@ Constrexpr.AN (Libnames.qualid_of_ident defined_typename) in
         let defining_ind_name = CAst.make @@ Nameops.add_prefix ((Names.Id.to_string defined_typename) ^ "_") indp_name in
         (defining_ind_name, decorated_typename)) 
    in
    let open Vernacexpr in
    let scheme =       
      names 
      |> List.map (fun (defining_ind_name, decorated_typename) ->            
           Some defining_ind_name,
             {
               sch_type = SchemeInduction;
               sch_qualid = decorated_typename;
               sch_sort = sort;
             }    
        )
    in 
    let* _ = vernac_ (VernacSynPure (VernacScheme scheme)) in
    let* _ = vernac_ (VernacSynPure (VernacCombinedScheme (CAst.make internal_indp_name, List.map fst names))) in
    return ()

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
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list) :
      CompiledModule.t t =
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

  let close_module ~(module_name : Names.Id.t) : CompiledModule.t t =
    let modname_ = CAst.make module_name in
    let* _ = vernac_ (VernacSynterp (VernacEndSegment modname_)) in
    return @@ Libnames.qualid_of_ident module_name

  let define_module ~(module_name : Names.Id.t)
      ~(parameters : (Names.Id.t * Constrexpr.module_ast) list)
      ~(body : CompiledModule.t list -> unit t) : CompiledModule.t t =
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

  (** Module Z := A. *)
  let define_module_inline ~(name : Names.Id.t) ~(value: Constrexpr.module_ast) : unit t =
    let open Vernacexpr in
    let modname_ = CAst.make name in
    let parameters_ =
      []
    in    
    let* _ =
      vernac_
        (VernacSynterp
           (VernacDefineModule
              (None, modname_, parameters_, Declaremods.Check [], [(value, Declaremods.DefaultInline)])))
    in        
    return ()

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
      ~(body : CompiledModule.t list -> unit t) : CompiledModuleType.t t =
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

  let construct_term_using_proof ~(name : Names.Id.t)
      ~(proof : Ltac_plugin.Tacexpr.raw_tactic_expr)
      ~(ty : Constrexpr.constr_expr) ~(opaque: Vernacexpr.opacity_flag) () : unit t =
    let open Ltac_plugin in
    let interppfs = Tacinterp.interp proof in
    (* Construct proof for it *)
    let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, type_checked_goal = Constrintern.interp_constr_evars env evd ty in
    let info = Declare.Info.make () in
    let cinfo = Declare.CInfo.make ~name ~typ:type_checked_goal () in
    let is_starting_plain = false in
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
    (*let opaque = Vernacexpr.Opaque in*)
    let _ = Declare.Proof.save_regular ~proof ~opaque ~idopt:None in
    return ()
end

(** "Declare Backend": Code generation backend by mutating the internal state of Coq's "contexts" *)
module Declare = struct
  let start_module (name : Names.Id.t)
      (parameters : (Names.Id.t * Constrexpr.module_ast) list) =
    let export = Some (Lib.Export, Libobject.unfiltered) in
    let modified_parameters =
      parameters
      |> List.map (fun (name, ty) ->
             ([ CAst.make name ], (ty, Declaremods.NoInline)))
    in
    let module_path =
      Declaremods.start_module export name modified_parameters
        (Declaremods.Check [])
    in
    module_path |> Names.ModPath.to_string |> Libnames.qualid_of_string

  let end_module () =
    let module_path = Declaremods.end_module () in
    module_path |> Names.ModPath.to_string |> Libnames.qualid_of_string
end
