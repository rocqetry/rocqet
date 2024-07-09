(* FInduction implementation for extensible proofs *)
open Env
open Types
module B = Backend.Vernac

(* Private store *)
module Ctx = struct
  type t = {
    name : Names.Id.t;
    compiled_context : CompiledModuleType.t;
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    compiled_motive : CompiledModuleType.t;
    motive : Constrexpr.constr_expr;
    goal : Constrexpr.constr_expr;
    goal_name : Names.Id.t;
    inductive : VernacInductive.t;
    (* This is the module where the implementation will go into *)
    module_name : Names.Id.t;
    provenance : Linkage.t;
    recursor : CompiledRecursor.t;
    handlers : (Names.Id.t * Constrexpr.constr_expr) list;
  }

  let store = Summary.ref ~name:"TheoremCtx" (None : t option)
  let update data = store := Some data

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no theorem context open"
    | Some store -> store

  let clear () = store := None
end

let prepare_proving () =
  let Ctx.{ module_name; parameters; provenance; recursor; compiled_motive; _ }
      =
    Ctx.get ()
  in
  let _ = B.run @@ B.open_module ~module_name ~parameters in
  let _ = B.run @@ Codegen.include_handler_types provenance recursor in
  let applied_motive =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr compiled_motive)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  B.run (B.include_module ~module_expr:applied_motive)

let start_proving () =
  let Ctx.{ goal; goal_name; _ } = Ctx.get () in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, checked_goal = Termutils.internalize env goal sigma in
  let info = Declare.Info.make () in
  let cinfo = Declare.CInfo.make ~name:goal_name ~typ:checked_goal () in
  let ongoing_proof = Declare.Proof.start ~info ~cinfo sigma in
  (* These tactics are defined in Loader.v *)
  let open Ltac_plugin in
  let unfold_first_level =
    let __unfold_motive_helper =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident
                     (Names.Id.of_string "__unfold_ftheorem_motive"),
                   [] ))))
    in
    Tacinterp.interp __unfold_motive_helper
  in
  let unfold_nonsplit =
    let __unfold_motive_helper =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident
                     (Names.Id.of_string "__unfold_ftheorem_motive_nested"),
                   [] ))))
    in
    Tacinterp.interp __unfold_motive_helper
  in
  let repeat_split =
    Tacticals.tclREPEAT
      (Tactics.split_with_bindings false [ Tactypes.NoBindings ])
  in
  let repeat_split_then_unfold =
    Tacticals.tclTHEN repeat_split unfold_first_level
  in
  let split = false in
  let starting_operation =
    if split then repeat_split_then_unfold else unfold_nonsplit
  in
  let ongoing_proof, _ = Declare.Proof.by starting_operation ongoing_proof in
  ongoing_proof

let handler_types_table name (recursor : CompiledRecursor.t) =
  let motive = Naming.motive_of name in
  recursor.compiled_handlers
  |> List.map (fun (handler_name, _) ->
         let motive_term =
           Constrexpr_ops.mkRefC (Libnames.qualid_of_ident motive)
         in
         let handler_type = Naming.handler_type handler_name in
         let handler_type =
           Constrexpr_ops.mkRefC (Libnames.qualid_of_ident handler_type)
         in
         let handler_type =
           Constrexpr_ops.mkAppC (handler_type, [ motive_term ])
         in
         (handler_name, handler_type))

let open_theorem ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) =
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let family_name = Context.family_name context in
  let motive = Resolver.resolve_constrexpr ~context ~expression:motive in
  let compiled_motive =
    Codegen.compile_motives ~names:[ name ] ~ctx:parameters ~motives:[ motive ]
      ~family_name
  in
  let inductive, compiled_recursors, provenance =
    Context.lookup_inductive_for_recursion ~name:inductive context
  in
  let suffix = RecKind.IndComplete in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let handlers = handler_types_table name recursor in
  let goal =
    let open Constrexpr_ops in
    let the_motive =
      name |> Naming.motive_of |> Libnames.qualid_of_ident |> mkRefC
    in
    let __True = mkIdentC (Names.Id.of_string "True") in
    let __prod l r =
      let using_prod_or_conj =
        match suffix with RecKind.IndComplete -> "and" | _ -> "prod"
      in
      mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [ l; r ])
    in
    let all_recur_name =
      List.map (fun (name, _) -> Naming.handler_type name) handlers
    in
    let all_recur_ = List.map mkIdentC all_recur_name in
    let all_applied_recur =
      List.map (fun x -> mkAppC (x, [ the_motive ])) all_recur_
    in
    List.fold_right __prod all_applied_recur __True
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let ctx =
    Ctx.
      {
        name;
        module_name;
        handlers;
        goal;
        goal_name;
        inductive;
        compiled_context;
        compiled_motive;
        motive;
        parameters;
        provenance;
        recursor;
      }
  in
  Ctx.update ctx; 
  prepare_proving ()

let open_theorem_extension ~name =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let family_name = Context.family_name context in
  let linkage = Context.family_linkage context in
  let base_elem = Context.base_linkage_elem context ~field:name in
  let inductive, motives, inherited_handlers =
    match base_elem with
    | Some (base, LinkageElem.TheoremDefinition { inductive; motives; handlers; _ }) ->       
       let source = Naming.self_version base.name in
       let target = Naming.self_version linkage.name in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = motives |> List.map path_subtitution in
        let handlers =
          handlers
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
       inductive, motives, handlers
    | _ -> Errors.fail ~info:"Expected to inherit a Theorem"
  in 
  let motives = Resolver.resolve_constrexpr_list ~context ~expressions:motives in
  let compiled_motive =
    Codegen.compile_motives ~names:[ name ] ~ctx:parameters ~motives
      ~family_name
  in
  let inductive, compiled_recursors, provenance =
    let name =
      inductive
      |> VernacInductive.extract_inductive_name
      |> Libnames.qualid_of_ident
    in 
    Context.lookup_inductive_for_recursion ~name context
  in
  let suffix = RecKind.IndComplete in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let handlers = handler_types_table name recursor in
  let implementing_handlers = 
    let inside x l = List.exists (fun k -> Names.Id.equal k x) l in
    let inherited_handlers = List.map fst inherited_handlers in 
    List.filter (fun (x, _) -> not (inside x inherited_handlers)) handlers
  in 
  let goal =
    let open Constrexpr_ops in
    let the_motive =
      name |> Naming.motive_of |> Libnames.qualid_of_ident |> mkRefC
    in
    let __True = mkIdentC (Names.Id.of_string "True") in
    let __prod l r =
      let using_prod_or_conj =
        match suffix with RecKind.IndComplete -> "and" | _ -> "prod"
      in
      mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [ l; r ])
    in
    let all_recur_name =
      List.map (fun (name, _) -> Naming.handler_type name) implementing_handlers
    in
    let all_recur_ = List.map mkIdentC all_recur_name in
    let all_applied_recur =
      List.map (fun x -> mkAppC (x, [ the_motive ])) all_recur_
    in
    List.fold_right __prod all_applied_recur __True
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let motive = List.hd motives in
  let ctx =
    Ctx.
      {
        name;
        module_name;
        handlers;
        goal;
        goal_name;
        inductive;
        compiled_context;
        compiled_motive;
        motive;
        parameters;
        provenance;
        recursor;
      }
  in
  Ctx.update ctx; 
  prepare_proving ()  

let close_theorem () =
  let Ctx.
        {
          name;
          motive;
          compiled_motive;
          goal;
          goal_name;
          module_name;
          handlers;
          inductive;
          parameters;
          provenance;
          compiled_context;
          _;
        } =
    Ctx.get ()
  in
  let postfix = RecKind.IndComplete in
  let open Constrexpr_ops in
  let coq_fst x =
    let fst =
      let using_prod_or_conj =
        match postfix with RecKind.IndComplete -> "proj1" | _ -> "fst"
      in
      mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string using_prod_or_conj)
    in
    mkAppC (fst, [ x ])
  in
  let coq_snd x =
    let snd =
      let using_prod_or_conj =
        match postfix with RecKind.IndComplete -> "proj2" | _ -> "snd"
      in
      mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string using_prod_or_conj)
    in
    mkAppC (snd, [ x ])
  in
  let rec _proj_each_case_handlers (all_recur_names : Names.Id.t list)
      (acc_case_handlers : Constrexpr.constr_expr) =
    match all_recur_names with
    | [] -> []
    | h :: t ->
        (h, coq_fst acc_case_handlers)
        :: _proj_each_case_handlers t (coq_snd acc_case_handlers)
  in
  let handler_names = handlers |> List.map fst in
  let implemented_case_names_handlers =
    _proj_each_case_handlers handler_names (mkIdentC goal_name)
  in
  let define_implemented_case_names_handlers =
    List.map
      (fun (x, y) -> B.define_term ~name:x y)
      implemented_case_names_handlers
  in
  let _ = B.run @@ B.flatmap define_implemented_case_names_handlers in
  let compiled_handlers = B.run @@ B.close_module ~module_name in
  let the_motive = Naming.motive_of name in
  let impl_name = Naming.fresh_name ~prefix:(Names.Id.to_string module_name) in
  let compiled_impl =
    B.(
      run
      @@ define_module ~module_name:impl_name ~parameters ~body:(fun ctx ->
             let module_expr =
               Termutils.apply_module
                 ~functor_expr:
                   (Termutils.ident_to_module_expr compiled_handlers)
                 ~arguments:ctx
             in
             let* _ = B.include_module ~module_expr in
             let args = the_motive :: handler_names in
             let args =
               args |> List.map Libnames.qualid_of_ident |> List.map mkRefC
             in
             let inductive =
               inductive |> VernacInductive.extract_inductive_name
             in
             let kind = RecKind.to_string postfix in
             let inductive_principle =
               Naming.principle_name ~inductive ~kind
               |> Libnames.qualid_of_ident |> mkRefC
             in
             let inductive_proof = mkAppC (inductive_principle, args) in
             let* _ = define_term ~name ~ty:goal inductive_proof in
             return ()))
  in
  let family_name = Context.family_name (Context.get ()) in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature ~names:[ name ]
      ~motive_module:compiled_motive ~handler_cases:compiled_handlers
      ~ctx:parameters ~provenance ~handlers:handler_names ~family_name
  in
  let elem =
    LinkageElem.TheoremDefinition
      {
        names = [ name ];
        inductive;
        compiled_impl;
        compiled_signature;
        compiled_context;
        motives = [ motive ];
        compiled_handlers;
        handlers;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
