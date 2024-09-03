(* Core implementation for extensible proofs *)
open Env
open Types

(* TODO: This module should not know about the Backend *)
module VB = Backend.Vernac

(* We need this becuase for some reason, VB doesn't seem to work
   if modules are not closed immediately(?) *)
module DB = Backend.Declare

(* Private store *)
module Ctx = struct
  type t = {
    name : Names.Id.t;
    proof : Declare.Proof.t option;
    handler_names : Names.Id.t list;
    implementing_handler_names : Names.Id.t list;
    inherited_handlers : (Names.Id.t * Constrexpr.constr_expr) list;
    compiled_context : CompiledModuleType.t;
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    compiled_motive : CompiledModuleType.t;
    motive : Constrexpr.constr_expr;
    goal : Constrexpr.constr_expr;
    handler_type_prefix : Names.Id.t;
    goal_name : Names.Id.t;
    inductive : VernacInductive.t;
    module_name : Names.Id.t;
    provenance : Linkage.t;
    recursor : CompiledRecursor.t;
    suffix : RecKind.t;
  }

  let store = Summary.ref ~name:"TheoremCtx" (None : t option)
  let update data = store := Some data

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no theorem context open"
    | Some store -> store

  let update_proof proof =
    let s = get () in
    store := Some { s with proof = Some proof }

  let clear () = store := None
end

let aggregate_handler_types (recursor : CompiledRecursor.t) parameters =
  let open VB in
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
  VB.run @@ VB.define_module ~module_name ~parameters ~body:f

let prepare_proving () =
  let Ctx.
        {
          module_name;
          handler_type_prefix;
          parameters;
          provenance = _;
          recursor;
          compiled_motive;
          _;
        } =
    Ctx.get ()
  in
  let handler_types = aggregate_handler_types recursor parameters in
  let handler_wrapper =
    Codegen.wrap_module ~module_name:handler_type_prefix
      ~inner_module:handler_types ~ctx:parameters
  in
  let _ = DB.start_module module_name parameters in
  (* let _ = VB.run @@ Codegen.include_handler_types provenance recursor in *)
  let applied_motive =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr compiled_motive)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let applied_handler_types =
    Termutils.apply_module
      ~functor_expr:(handler_wrapper |> Termutils.ident_to_module_expr)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  VB.run (VB.include_module ~module_expr:applied_motive);
  VB.run (VB.include_module ~module_expr:applied_handler_types)

let start_proving () =
  let Ctx.{ goal; goal_name; _ } = Ctx.get () in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, checked_goal = Termutils.internalize env goal sigma in
  let info = Declare.Info.make ~poly:false () in
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
  Ctx.update_proof ongoing_proof;
  ongoing_proof

let end_proving () =
  let Ctx.{ proof; goal_name; _ } = Ctx.get () in
  let proof =
    match proof with
    | None -> Errors.fail ~info:"Not in proof mode"
    | Some proof -> proof
  in
  let pm = Declare.OblState.empty in
  Declare.Proof.save ~pm ~proof ~opaque:Vernacexpr.Transparent
    ~idopt:(Some (CAst.make goal_name))
  |> ignore

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
  let handler_names = recursor.compiled_handlers |> List.map fst
    (* Termutils.handler_types_table name recursor suffix |> List.map fst*)
  in
  let implementing_handler_names = handler_names in
  let handler_type_prefix = Naming.fresh_name ~prefix:"HandlerTypes" in
  let goal =
    Termutils.calculate_inductive_proof_goal ~handler_type_prefix
      ~theorem_name:name ~handler_names ~suffix
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let inherited_handlers = [] in
  let ctx =
    Ctx.
      {
        name;
        module_name;
        handler_names;
        handler_type_prefix;
        implementing_handler_names;
        inherited_handlers;
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
        proof = None;
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
  let elem = Inheritance.inherit_element ~field:name ~linkage ~context in
  let inductive, motives, inherited_handlers, suffix =
    match elem with
    | None -> Errors.fail ~info:"There is no such FInduction in a base family"
    | Some
        (LinkageElem.TheoremDefinition
          { inductive; motives; handlers; suffix; _ }) ->
        (inductive, motives, handlers, suffix)
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
  
  let handler_names = recursor.compiled_handlers |> List.map fst 
    (* Termutils.handler_types_table name recursor suffix |> List.map fst*)
  in
  let implementing_handler_names =
    let inside x l = List.exists (fun k -> Names.Id.equal k x) l in
    let inherited_handlers = List.map fst inherited_handlers in
    handler_names |> List.filter (fun x -> not (inside x inherited_handlers))
  in
  let handler_type_prefix = Naming.fresh_name ~prefix:"HandlerTypes" in
  let goal =
    Termutils.calculate_inductive_proof_goal ~theorem_name:name
      ~handler_type_prefix ~handler_names:implementing_handler_names ~suffix
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let motive = List.hd motives in
  let ctx =
    Ctx.
      {
        name;
        handler_names;
        implementing_handler_names;
        inherited_handlers;
        handler_type_prefix;
        module_name;
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
        proof = None;
      }
  in
  Ctx.update ctx;
  prepare_proving ()

let close_theorem () =
  let Ctx.
        {
          name;
          handler_names;
          implementing_handler_names;
          inherited_handlers;
          motive;
          compiled_motive;
          goal;
          goal_name;
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
  let implemented_handlers =
    Termutils.extract_handlers_from_inductive_proof implementing_handler_names
      (mkIdentC goal_name) suffix
  in
  let all_handlers = inherited_handlers @ implemented_handlers in
  let f x = x |> Termutils.cbn_type_check |> Termutils.reflect_checked_term in
  let all_handlers =
    List.map (fun (name, expr) -> (name, f expr)) all_handlers
  in
  let all_compiled_handlers =
    List.map
      (fun (x, y) ->
        VB.define_term ~name:(Naming.handler_name ~recursor:name ~case:x) y)
      all_handlers
  in
  let _ = VB.run @@ VB.flatmap all_compiled_handlers in
  let compiled_handlers = DB.end_module () in
  let the_motive = Naming.motive_of name in
  let compiled_impl =
    Codegen.compile_theorem_implementation ~name ~parameters ~compiled_handlers
      ~motive_name:the_motive
      ~inductive_name:(VernacInductive.extract_inductive_name inductive)
      ~suffix ~goal ~provenance ~handler_names
  in
  let family_name = Context.family_name (Context.get ()) in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature ~names:[ name ]
      ~motive_module:compiled_motive ~handler_cases:compiled_handlers
      ~ctx:parameters ~family_name ~computational_behaviour:`Hidden
      ~computational_axioms:[]
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
        handlers = all_handlers;
        suffix;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
