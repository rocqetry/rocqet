open Types
open Env

(* For some reason, the VernacBackend doesn't seem to work
   if modules are not closed immediately?
*)
module M = struct
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

(* Private store *)
module Ctx = struct
  type t = {
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    handler_types : (Names.Id.t * Constrexpr.constr_expr) list;
    handler_cases : (Names.Id.t * Constrexpr.constr_expr) list;
    module_name : Names.Id.t;
    compiled_context : CompiledModuleType.t;
    name : Names.Id.t;
    inductive : VernacInductive.t;
    provenance : Linkage.t;
    motive : CompiledModule.t;
    motive_expr : Constrexpr.constr_expr list;
    suffix : RecKind.t;
  }

  let store = Summary.ref ~name:"RecursionCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no recursion context open"
    | Some store -> store

  let clear () = store := None
  let update recursion_data = store := Some recursion_data

  let add_handler_case name expr =
    let ctx = get () in
    let ctx = { ctx with handler_cases = (name, expr) :: ctx.handler_cases } in
    update ctx
end

let calculate_computational_axiom_for_constructor 
      ~recursor_name
      ~recursor_path 
      ~constructor_name 
      ~constructor_path = 
  let open Constrexpr_ops in 
  let constructor_params, fully_applied_constr = 
    Termutils.extract_variables_and_apply (mkRefC constructor_path) 
  in 
  let recursor_params, _ = 
    recursor_path
    |> mkRefC
    |> Termutils.checked_type_of
    |> Termutils.reflect_checked_term
    |> Termutils.collect_argument_and_ret_of_type
  in
  let recursor_parameter_wo_first = List.tl recursor_params in 
  let recursor_remained_arguments = List.map snd recursor_parameter_wo_first in
  let params = 
    constructor_params @ recursor_parameter_wo_first 
  in 
  let recursor_applied = mkAppC ((mkRefC recursor_path),fully_applied_constr::recursor_remained_arguments) in
  let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in 
  let id_on_fully_applied_r =  mkAppC (eq_cstr, [recursor_applied;recursor_applied]) in
   let closed_recursor_applied = 
    List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) (List.map fst params) id_on_fully_applied_r  
  in 
  (* The final axiom is an equation *)
  let equation = 
    let reflected = 
      closed_recursor_applied 
      |> Termutils.cbn_type_check 
      |> Termutils.reflect_checked_term 
    in     
    let _, body = Termutils.collect_argument_and_ret_of_type reflected in   
    let destEq {CAst.v = t; _} = 
      match t with 
      | Constrexpr.CNotation (_ ,(_, "_ = _"), ([lhs; rhs], _, _, _)) -> (lhs, rhs) 
      | _ -> Errors.fail ~info:"Expected CNotation"
    in
    let normalized, _ = destEq body in 
    let id_on_applied_and_normalized = mkAppC (eq_cstr, [recursor_applied;normalized]) in 
    List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) (List.map fst params) id_on_applied_and_normalized 
  in 
  let equation_name = 
    Names.Id.to_string recursor_name ^ "_" ^ 
    Names.Id.to_string constructor_name ^ "_eq" 
    |> Names.Id.of_string
  in 
  equation_name, equation

let generate_computational_axioms provenance constructors recursor =
  let prefix =
    Libnames.qualid_of_ident (Naming.self_version provenance)
  in
  let recursor_name = recursor in
  let recursor_path = Libnames.qualid_of_ident recursor in
  let constructors = 
     constructors
     |> List.map (fun (name, _) -> name, Naming.qualid_point (Some prefix) name)
  in
  constructors 
  |> List.map (fun (constructor_name, constructor_path) -> 
         calculate_computational_axiom_for_constructor
           ~recursor_name
           ~recursor_path
           ~constructor_name 
           ~constructor_path)  


let _compile_computational_recursor_behaviour elem provenance parameters =
  match elem with
  | LinkageElem.RecursorDefinition { names; inductive; _ } ->
      let module_name =
        let inductive_name =
          inductive |> VernacInductive.extract_inductive_name
          |> Names.Id.to_string
        in
        let name = names |> List.hd |> Names.Id.to_string in
        name ^ inductive_name
      in
      let auto_tactic (* : Tacexpr.raw_tactic_expr*) =
        let open Ltac_plugin in
        CAst.make
          (Tacexpr.TacArg
             (Tacexpr.TacCall
                (CAst.make
                   (Libnames.qualid_of_ident (Names.Id.of_string "eauto"), []))))
      in
      let constructors =
        let _, constructors =
          inductive |> List.hd |> fst |> VernacInductive.extract_type_and_cstrs
        in
        constructors
      in
      let recursor =  names |> List.hd in 
      let name_axiom_pairs : (Names.Id.t * Constrexpr.constr_expr) list =
        generate_computational_axioms provenance constructors recursor
      in
      let open Codegen.VernacBackend in
      let compiled_signature =
        run
        @@ define_moduletype
             ~module_name:(Naming.fresh_name ~prefix:module_name) ~parameters
             ~body:(fun _ctx ->
               let for_each_pair (name, ty) = assume_parameter ~name ~ty in
               flatmap (List.map for_each_pair name_axiom_pairs))
      in
      let compiled_implementation =
         run @@
         define_module ~module_name:(Naming.fresh_name ~prefix:module_name) ~parameters         
         ~body:(fun _ctx -> 
           let for_each_pair (name, ty) =
             thunk (construct_term_using_proof ~name ~proof:auto_tactic ~ty) in 
           flatmap (List.map for_each_pair name_axiom_pairs))
      in 
      compiled_signature, compiled_implementation
  | _ -> Errors.fail ~info:"Expected a recursor definition"

let close_recursion () =
  let Ctx.
        {
          handler_types;
          name;
          inductive;
          suffix;
          compiled_context;
          motive;
          provenance;
          parameters;
          module_name;
          handler_cases;
          motive_expr;
          _;
        } =
    Ctx.get ()
  in
  module_name |> ignore;
  let module_name = M.end_module () in
  let compiled_signature =
    Codegen.compile_recursor_signature 
      ~names:[ name ] 
      ~motive_module:motive
      ~handler_cases:module_name
      ~ctx:parameters 
      ~family_name:name
  in
  let compiled_impl =
    Codegen.compile_recursor_implementation ~inductive ~provenance
      ~recursor_name:name
      ~handlers:(handler_types |> List.map fst)
      ~suffix ~ctx:parameters ~handler_cases:module_name
  in
  let elem =
    LinkageElem.RecursorDefinition
      {
        handler_cases;
        names = [ name ];
        inductive;
        recursor_module = module_name;
        motive_module = motive;
        motives = motive_expr;
        compiled_signature;
        compiled_impl;
        compiled_context;
        suffix;
        handler_types;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()

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

let open_recursion ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) ~(suffix : RecKind.t) =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let family = context |> Context.family_name |> Names.Id.to_string in
  let module_name =
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Cases" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in
  let motive_expr = Resolver.resolve_constrexpr ~context ~expression:motive in
  let motive =
    Codegen.compile_motives ~names:[ name ] ~motives:[ motive_expr ]
      ~ctx:parameters ~family_name:name
  in
  let inductive, compiled_recursors, provenance =
    Context.lookup_inductive_for_recursion ~name:inductive context
  in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let _module_name = M.start_module module_name parameters in
  let open Codegen.VernacBackend in
  run @@ Codegen.include_handler_types provenance recursor;
  let applied_motive =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr motive)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let _ = include_module ~module_expr:applied_motive |> run in
  let handler_types = handler_types_table name recursor in
  let recursion_ctx =
    Ctx.
      {
        parameters;
        handler_cases = [];
        suffix;
        handler_types;
        module_name;
        name;
        compiled_context;
        motive;
        motive_expr = [ motive_expr ];
        inductive;
        provenance;
      }
  in
  Ctx.update recursion_ctx

let remove_duplicates lst =
  let rec aux seen = function
    | [] -> []
    | hd :: tl ->
        if List.mem hd seen then aux seen tl else hd :: aux (hd :: seen) tl
  in
  aux [] lst

let open_recursion_extension ~name =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let linkage = Context.family_linkage context in
  let further_elem = Context.further_bound_linkage_elem context ~field:name in
  let base_elem = Context.base_linkage_elem context ~field:name in
  let inductive, motives, handler_cases, suffix =
    match (further_elem, base_elem) with
    | ( None,
        Some
          ( base,
            RecursorDefinition { inductive; suffix; motives; handler_cases; _ }
          ) ) ->
        let source = Naming.self_version base.name in
        let target = Naming.self_version linkage.name in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = motives |> List.map path_subtitution in
        let handler_cases =
          handler_cases
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let inductive = inductive |> VernacInductive.extract_inductive_name in
        (inductive, motives, handler_cases, suffix)
    | ( Some
          ( further,
            RecursorDefinition { inductive; suffix; motives; handler_cases; _ }
          ),
        None ) ->
        let source = Linkage.top_most_self_name further in
        let target = Linkage.top_most_self_name linkage in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = motives |> List.map path_subtitution in
        let handler_cases =
          handler_cases
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let inductive = inductive |> VernacInductive.extract_inductive_name in
        (inductive, motives, handler_cases, suffix)
    | Some (further, RecursorDefinition frec), Some (base, RecursorDefinition _)
      ->
        let source = Linkage.top_most_self_name further in
        let target = Linkage.top_most_self_name linkage in
        let path_subtitution = Naming.replace_qualid_root ~source ~target in
        let motives = frec.motives |> List.map path_subtitution in
        let handler_cases_further =
          frec.handler_cases
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let handler_cases_base =
          let source = Naming.self_version base.name in
          let target = Naming.self_version linkage.name in
          let path_subtitution = Naming.replace_qualid_root ~source ~target in
          frec.handler_cases
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let handler_cases =
          remove_duplicates (handler_cases_base @ handler_cases_further)
        in
        let inductive =
          frec.inductive |> VernacInductive.extract_inductive_name
        in
        (inductive, motives, handler_cases, frec.suffix)
    | _ -> Errors.fail ~info:"Not yet implemented"
  in
  let module_name =
    let family = Names.Id.to_string linkage.name in
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Cases" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in
  let motive =
    Codegen.compile_motives ~names:[ name ] ~motives ~ctx:parameters
      ~family_name:name
  in
  let inductive, compiled_recursors, provenance =
    let inductive = Libnames.qualid_of_ident inductive in
    Context.lookup_inductive_for_recursion ~name:inductive context
  in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let open Codegen.VernacBackend in
  let handler_types = handler_types_table name recursor in
  let recursor_module =
    Codegen.compile_handler_cases ~name ~context ~motive ~handler_cases
      ~handler_types ~parameters ~provenance ~recursor
  in
  let _module_name = M.start_module module_name parameters in
  let previous_cases =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr recursor_module)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let _ = include_module ~module_expr:previous_cases |> run in
  let recursion_ctx =
    Ctx.
      {
        parameters;
        handler_cases;
        suffix;
        handler_types;
        module_name;
        name;
        compiled_context;
        motive;
        motive_expr = motives;
        inductive;
        provenance;
      }
  in
  Ctx.update recursion_ctx

let add_handler ~name ~handler =
  let recursion_ctx = Ctx.get () in
  match List.assoc_opt name recursion_ctx.handler_types with
  | None -> Errors.fail ~info:"Unbound Constructor"
  | Some ty ->
      let open Codegen.VernacBackend in
      let case_name =
        Naming.handler_name ~recursor:recursion_ctx.name ~case:name
      in
      Ctx.add_handler_case name handler;
      define_term ~name:case_name ~ty handler |> run
