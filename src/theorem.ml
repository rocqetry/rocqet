(* Core implementation of extensible proofs *)
open Env
open Types

(* We use the Declare backend here because somehow the Vernac backend
   doesn't work when we don't close the module almost immediately(?) *)
module DB = Backend.Declare

module Ctx = struct
  type t = {
    names : Names.Id.t list;
    implementing_handler_names : Names.Id.t list;
    inherited_handlers : Names.Id.t list;
    compiled_context : CompiledModuleType.t;
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    goal : Constrexpr.constr_expr;
    goal_name : Names.Id.t;
    module_name : Names.Id.t;
    rec_principle_prefix : Libnames.qualid;
    inductive_paths : Libnames.qualid list;
    suffix : RecKind.t;
    inductive : VernacInductive.t;
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
  let Ctx.{ module_name; parameters; _ } = Ctx.get () in
  let _ = DB.start_module module_name parameters in
  ()

let start_proving () =
  let Ctx.{ goal; goal_name; names; _ } = Ctx.get () in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, checked_goal = Termutils.internalize env goal sigma in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name:goal_name ~typ:checked_goal () in
  let ongoing_proof = Declare.Proof.start ~info ~cinfo sigma in
  (* These tactics are defined in Loader.v *)
  let open Ltac_plugin in
  let idtac =
    let idtac =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident
                     (Names.Id.of_string "idtac"),
                   [] ))))
    in
    Tacinterp.interp idtac
  in
  let combine_tactics ~tactics = 
    List.fold_right (fun t rest -> Tacticals.tclTHEN t rest) tactics idtac
  in
  let unfold_motive_precisely name =
    let self__motive = 
      Resolver.resolve_qualid ~context:(Context.get ()) 
        ~qualid:(Libnames.qualid_of_ident (Naming.motive_of name))
    in 
    let self__motive_tactic =
      (Tacexpr.TacCall
         (CAst.make
            ( self__motive,
              [] )))      
    in
    let unfold_self_motive =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident
                     (Names.Id.of_string "__funfold"),
                   [self__motive_tactic] ))))
    in
    Tacinterp.interp unfold_self_motive
  in    
  let unfold_motives_precisely =
    let tactics = names |> List.map unfold_motive_precisely in
    combine_tactics ~tactics
  in 
  let split_cases_into_goals =
    let helper =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 (Libnames.qualid_of_ident (Names.Id.of_string "split_cases_into_goals"), []))))
    in
    Tacinterp.interp helper
  in  
  let starting_operation =
    combine_tactics ~tactics:[ unfold_motives_precisely; split_cases_into_goals ]      
  in
  let ongoing_proof, _ = Declare.Proof.by starting_operation ongoing_proof in
  ongoing_proof

let open_theorem ~(args : Frec_arg.t list) =    
  let rec split3 xs =
    match xs with
    | [] -> [], [], []
    | (a, b, c) :: xs ->
       let (as', bs, cs) = split3 xs in
       (a :: as', b :: bs, c :: cs)
  in 

  let names, inductive_paths, motives =
    args
    |> List.map (fun Frec_arg.{ name; inductive; motive } -> name, inductive, motive)
    |> split3
  in 
  
  let context = Context.get () in
  let motives =
    motives
    |> List.map (fun motive -> Resolver.resolve_constrexpr ~context ~expression:motive)
  in
  let inductive, recursors, _ =
    let inductive_path = List.hd inductive_paths in
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let suffix = RecKind.IndComplete in
  let recursor = RecursorStore.find suffix recursors in
  let motive_names = names |> List.map (fun name -> Naming.motive_of name) in
  let () =
    List.iter2 (fun motive_name motive -> Definition.add_definition ~name:motive_name motive)
      motive_names
      motives
  in
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:(Naming.concat_names names) context
  in
  let handler_types =
    Termutils.handler_type_for_recursion ~names ~inductive_paths ~recursor
  in
  (*let inductive_name = inductive_path |> Naming.extract_path_base in
  let handler_names =
    recursor.handlers
    |> Names.Id.Map.find inductive_name |> List.map fst
  in*)
  let handler_names =
    inductive_paths
    |> List.map Naming.extract_path_base
    |> List.concat_map (fun inductive_name ->
       inductive
       |> VernacInductive.create_inductive_constructor_map
       |> Names.Id.Map.find inductive_name)
  in 
  let implementing_handler_names = handler_names in
  let goal =
    Termutils.calculate_inductive_proof_goal
      ~handler_types:(List.map snd handler_types)
      ~suffix
  in
  let rec_principle_prefix =
    let inductive_path = List.hd inductive_paths in
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let module_name = goal_name in
  let inherited_handlers = [] in
  let ctx =
    Ctx.
      {
        names;
        module_name;
        implementing_handler_names;
        inherited_handlers;
        goal;
        goal_name;
        compiled_context;
        rec_principle_prefix;
        inductive_paths;
        parameters;
        suffix;
        inductive;
      }
  in
  Ctx.update ctx;
  prepare_proving ()

let open_theorem_extension ~(names : Names.Id.t list) =
  names |> List.iter (fun name -> Inheritance.inherit_dependencies ~prefix:name);
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:(Naming.concat_names names) context
  in
  let elem = Inheritance.lookup_field_in_base ~field:(List.hd names) ~context in
  let inductive_paths, inherited_handlers, suffix =
    match elem with
    | None -> Errors.fail ~info:"There is no such FInduction in a base family"
    | Some
        (LinkageElem.TheoremDefinition { inductive_paths; handlers; suffix; _ })
      ->
        (inductive_paths, handlers, suffix)
    | _ -> Errors.fail ~info:"Expected to inherit an FInduction"
  in
  let inductive, recursors, _ =
    let inductive_path = List.hd inductive_paths in 
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix recursors in  
  let handler_names =
    inductive_paths
    |> List.map Naming.extract_path_base
    |> List.concat_map (fun inductive_name ->
       inductive
       |> VernacInductive.create_inductive_constructor_map
       |> Names.Id.Map.find inductive_name)
  in 
  let inside x l = List.exists (fun k -> Names.Id.equal k x) l in
  let inherited_handlers = inherited_handlers |> List.concat_map snd in
  let implementing_handler_names =
    handler_names |> List.filter (fun x -> not (inside x inherited_handlers))
  in
  let handler_types =
    Termutils.handler_type_for_recursion ~names ~inductive_paths ~recursor
    |> List.filter_map (fun (name, handler_type) ->
           if inside name implementing_handler_names then Some handler_type
           else None)
  in
  let goal = Termutils.calculate_inductive_proof_goal ~handler_types ~suffix in
  let rec_principle_prefix =
    let inductive_path = List.hd inductive_paths in
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let module_name = goal_name in
  let ctx =
    Ctx.
      {
        names;
        implementing_handler_names;
        inherited_handlers;
        module_name;
        goal;
        goal_name;
        compiled_context;
        rec_principle_prefix;
        inductive_paths;
        parameters;
        suffix;
        inductive;
      }
  in
  Ctx.update ctx;
  prepare_proving ()

let close_theorem () =
  let Ctx.
        {
          names;
          inductive;
          implementing_handler_names;
          inherited_handlers;
          goal_name;
          compiled_context;
          suffix;
          rec_principle_prefix;
          inductive_paths;
          _;
        } =
    Ctx.get ()
  in
  rec_principle_prefix |> ignore;
  inherited_handlers |> ignore;
  let compiled_impl = DB.end_module () in
  let default_ctx_params =
    let context = Context.get () in
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let goal_elem =
    LinkageElem.FieldDefinition
      { compiled_context; compiled_impl; default_ctx_params }
  in
  (* Add the goal as a field *)
  Context.add_field ~name:goal_name ~elem:goal_elem;
  let open Constrexpr_ops in
  let implemented_handlers =
    Termutils.extract_handlers_from_inductive_proof implementing_handler_names
      (mkIdentC goal_name) suffix
  in
  (* let all_handlers = inherited_handlers @ List.map fst implemented_handlers in*)
  let inductive_names = inductive_paths |> List.map Naming.extract_path_base in
  (* We want the names to be in the right order *)
  (*let handlers =     
    inductive_names
    |> List.concat_map (fun inductive_name ->
       inductive
       |> VernacInductive.create_inductive_constructor_map
       |> Names.Id.Map.find inductive_name)
  in*)
  let handlers =     
    inductive_names
    |> List.map (fun inductive_name ->
       let handlers = 
         inductive
         |> VernacInductive.create_inductive_constructor_map
         |> Names.Id.Map.find inductive_name
       in
       (inductive_name, handlers))
  in
  let implemented_handlers =
    List.map (fun (name, expr) -> (name, expr)) implemented_handlers
  in
  (* Add the handlers as fields *)
  let _ =
    implemented_handlers
    |> List.iter (fun (constructor_name, handler) ->
           let name =
             Naming.handler_name ~recursors:names ~case:constructor_name
           in
           Definition.add_definition ~name handler)
  in
  let context = Context.get () in
  let family_name = Context.family_name context in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:(Naming.concat_names names) context
  in
  let compiled_signature =
    Codegen.compile_theorem_definition_signature ~names ~ctx:parameters
      ~family_name
  in
  let elem =
    LinkageElem.TheoremDefinition
      {
        names;
        compiled_signature;
        compiled_context;
        handlers;
        inductive_paths;
        suffix;
        default_ctx_params;
      }
  in
  let name = List.hd names in
  Context.add_field ~name ~elem;
  Ctx.clear ()
