(* Core implementation of extensible proofs *)
open Env
open Types

(* We use the Declare backend here because somehow the Vernac backend
   doesn't work when we don't close the module almost immediately(?) *)
module DB = Backend.Declare

module Ctx = struct
  type t = {
    name : Names.Id.t;    
    implementing_handler_names : Names.Id.t list;
    inherited_handlers : Names.Id.t list;
    compiled_context : CompiledModuleType.t;
    parameters : (Names.Id.t * Constrexpr.module_ast) list;    
    goal : Constrexpr.constr_expr;
    goal_name : Names.Id.t;    
    module_name : Names.Id.t;
    rec_principle_prefix : Libnames.qualid;
    inductive_path : Libnames.qualid;
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
  let Ctx.{ module_name; parameters; _ } = Ctx.get () in    
  let _ = DB.start_module module_name parameters in  
  ()

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
  let split_cases_into_goals =
    let helper =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 (Libnames.qualid_of_ident (Names.Id.of_string "finduction"), []))))
    in
    Tacinterp.interp helper
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
  let starting_operation =
    Tacticals.tclTHEN starting_operation split_cases_into_goals
  in
  let ongoing_proof, _ = Declare.Proof.by starting_operation ongoing_proof in  
  ongoing_proof

let open_theorem
    ~(name : Names.Id.t)
    ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) =
  let inductive_path = inductive in
  let context = Context.get () in  
  let motive = Resolver.resolve_constrexpr ~context ~expression:motive in  
  let _inductive, recursors, _ =
    Context.lookup_inductive_for_recursion ~name:inductive context
  in  
  let suffix = RecKind.IndComplete in
  let recursor = RecursorStore.find suffix recursors in
  let motive_name = Naming.motive_of name in
  let () = Definition.add_definition ~name:motive_name motive in
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in  
  let handler_types =
    Termutils.handler_type_for_recursion ~name ~inductive_path ~recursor      
  in  
  let handler_names = recursor.handlers |> List.map fst in
  let implementing_handler_names = handler_names in  
  let goal = Termutils.calculate_inductive_proof_goal ~handler_types:(List.map snd handler_types) ~suffix in
  let rec_principle_prefix =
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in  
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let module_name = goal_name in
  let inherited_handlers = [] in
  let ctx =
    Ctx.
      {
        name;
        module_name;
        implementing_handler_names;
        inherited_handlers;
        goal;
        goal_name;        
        compiled_context;                
        rec_principle_prefix;
        inductive_path;        
        parameters;
        suffix;        
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
  let elem = Inheritance.lookup_field_in_base ~field:name ~context in
  let inductive_path, inherited_handlers, suffix =
    match elem with
    | None -> Errors.fail ~info:"There is no such FInduction in a base family"
    | Some
        (LinkageElem.TheoremDefinition
          { inductive_path; handlers; suffix;  _ }) ->
        (inductive_path, handlers, suffix)
    | _ -> Errors.fail ~info:"Expected to inherit an FInduction"
  in  
  let _inductive, recursors, _ =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix recursors in  
  let handler_names =
    recursor.handlers |> List.map fst    
  in
  let inside x l = List.exists (fun k -> Names.Id.equal k x) l in
  let implementing_handler_names =    
    handler_names |> List.filter (fun x -> not (inside x inherited_handlers))
  in  
  let handler_types =    
    Termutils.handler_type_for_recursion ~name ~inductive_path ~recursor
    |> List.filter_map (fun (name, handler_type) ->
           if inside name implementing_handler_names then Some handler_type
           else None)
  in
  let goal = Termutils.calculate_inductive_proof_goal ~handler_types ~suffix in
  let rec_principle_prefix =
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in  
  let goal_name = Naming.fresh_name ~prefix:"Goal" in
  let module_name = goal_name in  
  let ctx =
    Ctx.
      {
        name;
        implementing_handler_names;
        inherited_handlers;
        module_name;
        goal;
        goal_name;        
        compiled_context;        
        rec_principle_prefix;
        inductive_path;        
        parameters;
        suffix;        
      }
  in
  Ctx.update ctx;
  prepare_proving ()

let close_theorem () =
  let Ctx.
        {
          name;
          implementing_handler_names;
          inherited_handlers;                    
          goal_name;                    
          compiled_context;
          suffix;
          rec_principle_prefix;
          inductive_path;
          _;
        } =
    Ctx.get ()
  in
  rec_principle_prefix |> ignore;
  let compiled_impl = DB.end_module () in
  let goal_elem =
    LinkageElem.FieldDefinition
      {
        compiled_context;
        compiled_impl
      }
  in
  (* Add the goal as a field *)
  Context.add_field ~name:goal_name ~elem:goal_elem;    
  let open Constrexpr_ops in
  let implemented_handlers =
    Termutils.extract_handlers_from_inductive_proof implementing_handler_names
      (mkIdentC goal_name) suffix
  in
  let all_handlers = inherited_handlers @ List.map fst implemented_handlers in  
  let implemented_handlers =
    List.map (fun (name, expr) -> (name, expr)) implemented_handlers
  in
  (* Add the handlers as fields *)
  let _ =
    implemented_handlers
    |> List.iter (fun (constructor_name, handler) ->
           let name = Naming.handler_name ~recursor:name ~case:constructor_name in
           Definition.add_definition ~name handler)
  in 
  let context = Context.get () in  
  let family_name = Context.family_name context in  
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let compiled_signature =
    Codegen.compile_theorem_definition_signature
      ~names:[ name ]       
      ~ctx:parameters ~family_name      
  in
  let elem =
    LinkageElem.TheoremDefinition
      {
        names = [ name ];        
        compiled_signature;
        compiled_context;        
        handlers = all_handlers;
        inductive_path;
        suffix;        
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
