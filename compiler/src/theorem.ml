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
    suffix : RecKind.t;
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
  let handlers = Termutils.handler_types_table name recursor in
  let goal =
    Termutils.calculate_inductive_proof_goal ~theorem_name:name
      ~handlers:(List.map fst handlers) ~suffix
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
        suffix;
      }
  in
  Ctx.update ctx;
  prepare_proving ()

let remove_duplicates lst =
  let rec aux seen = function
    | [] -> []
    | hd :: tl ->
        if List.mem hd seen then aux seen tl else hd :: aux (hd :: seen) tl
  in
  aux [] lst

let open_theorem_extension ~name =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let family_name = Context.family_name context in
  let linkage = Context.family_linkage context in
  let further_elem = Context.further_bound_linkage_elem context ~field:name in
  let base_elem = Context.base_linkage_elem context ~field:name in
  let inductive, motives, inherited_handlers, suffix =
    match (further_elem, base_elem) with
    | (None,
       Some
        (base, LinkageElem.TheoremDefinition { inductive; motives; handlers; suffix; _ }))
      ->
        let source = Naming.self_version base.name in
        let target = Naming.self_version linkage.name in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = motives |> List.map path_subtitution in
        let handlers =
          handlers
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        (inductive, motives, handlers, suffix)
    | ( Some
          ( further,
            TheoremDefinition { inductive; suffix; motives; handlers; _ }
          ),
        None ) ->
        let source = Linkage.top_most_self_name further in
        let target = Linkage.top_most_self_name linkage in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = motives |> List.map path_subtitution in
        let handler_cases =
          handlers
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in        
        (inductive, motives, handler_cases, suffix)
    | Some (further, TheoremDefinition { motives; inductive; handlers = further_handlers; suffix; _}),
      Some (base, TheoremDefinition { handlers = base_handlers; _ })
      ->
        let source = Linkage.top_most_self_name further in
        let target = Linkage.top_most_self_name linkage in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = motives |> List.map path_subtitution in
        let handler_cases_further =
          further_handlers
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let handler_cases_base =
          let source = Naming.self_version base.name in
          let target = Naming.self_version linkage.name in
          let path_subtitution = Naming.replace_qualid_root ~source ~target in
          base_handlers
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let handler_cases =
          remove_duplicates (handler_cases_base @ handler_cases_further)
        in        
        (inductive, motives, handler_cases, suffix)
    | _ -> Errors.fail ~info:"Expected to inherit an FInduction"
  in
  let motives =
    Resolver.resolve_constrexpr_list ~context ~expressions:motives
  in
  let compiled_motive =
    Codegen.compile_motives ~names:[ name ] ~ctx:parameters ~motives
      ~family_name
  in
  let inductive, compiled_recursors, provenance =
    let name =
      inductive |> VernacInductive.extract_inductive_name
      |> Libnames.qualid_of_ident
    in
    Context.lookup_inductive_for_recursion ~name context
  in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let handlers = Termutils.handler_types_table name recursor in
  let implementing_handlers =
    let inside x l = List.exists (fun k -> Names.Id.equal k x) l in
    let inherited_handlers = List.map fst inherited_handlers in
    List.filter (fun (x, _) -> not (inside x inherited_handlers)) handlers
  in
  let goal =
    Termutils.calculate_inductive_proof_goal ~theorem_name:name
      ~handlers:(List.map fst implementing_handlers)
      ~suffix
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
        suffix;
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
          suffix;
          _;
        } =
    Ctx.get ()
  in
  let open Constrexpr_ops in
  let handler_names = handlers |> List.map fst in
  let implemented_case_names_handlers =
    Termutils.extract_handlers_from_inductive_proof handler_names
      (mkIdentC goal_name) suffix
  in
  let inherited_handlers =
    List.map (fun (x, y) -> B.define_term ~name:x y) handlers
  in
  let implemented_handlers =
    List.map
      (fun (x, y) -> B.define_term ~name:x y)
      implemented_case_names_handlers
  in
  let _ = B.run @@ B.flatmap inherited_handlers in
  let _ = B.run @@ B.flatmap implemented_handlers in
  let compiled_handlers = B.run @@ B.close_module ~module_name in
  let the_motive = Naming.motive_of name in
  let impl_name = Naming.fresh_name ~prefix:(Names.Id.to_string module_name) in
  let compiled_impl =
    Codegen.compile_theorem_implementation ~name:impl_name ~parameters
      ~compiled_handlers ~motive_name:the_motive
      ~inductive_name:(VernacInductive.extract_inductive_name inductive)
      ~suffix ~goal ~handler_names
  in
  let family_name = Context.family_name (Context.get ()) in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature ~names:[ name ]
      ~motive_module:compiled_motive ~handler_cases:compiled_handlers
      ~ctx:parameters ~provenance ~handlers:handler_names ~family_name
      ~computational_behaviour:`Hidden
  in
  let elem =
    LinkageElem.TheoremDefinition
      {
        names = [ name ];
        goal;
        inductive;
        compiled_impl;
        compiled_signature;
        compiled_context;
        motives = [ motive ];
        compiled_handlers;
        handlers = handlers @ implemented_case_names_handlers;
        suffix;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
