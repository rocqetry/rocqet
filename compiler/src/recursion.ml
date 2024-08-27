open Types
open Env

(* TODO: This module should not know about the Vernac backend *)
module VB = Backend.Vernac
(* We need this becuase for some reason, VB doesn't seem to work 
   if modules are not closed immediately(?) *)
module DB = Backend.Declare

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
  Typechecking.check_exhaustive ~name ~inductive ~handlers:handler_cases;
  module_name |> ignore;
  let module_name = DB.end_module () in
  let handlers = handler_types |> List.map fst in
  let compiled_impl, computational_axioms =
    Codegen.compile_recursive_definition_implementation ~inductive ~provenance
      ~recursor_name:name ~handlers ~suffix ~ctx:parameters
      ~handler_cases:module_name
  in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature ~provenance ~handlers
      ~names:[ name ] ~motive_module:motive ~handler_cases:module_name
      ~ctx:parameters ~family_name:name ~computational_behaviour:`Exposed
      ~computational_axioms
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
  let _module_name = DB.start_module module_name parameters in
  VB.run @@ Codegen.include_handler_types provenance recursor;
  let applied_motive =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr motive)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let _ = VB.(run (include_module ~module_expr:applied_motive)) in
  let handler_types = Termutils.handler_types_table name recursor in
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
    | Some (further, RecursorDefinition frec), Some (base, RecursorDefinition brec)
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
          brec.handler_cases
          |> List.map (fun (name, expr) -> (name, path_subtitution expr))
        in
        let handler_cases =
          remove_duplicates (handler_cases_base @ handler_cases_further)
        in
        let inductive =
          frec.inductive |> VernacInductive.extract_inductive_name
        in
        (inductive, motives, handler_cases, frec.suffix)
    | _ -> Errors.fail ~info:"Expected to inherit an FRecrusion"
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
  let handler_types = Termutils.handler_types_table name recursor in
  let compiled_handler_types = Codegen.aggregate_handler_types recursor parameters in 
  let recursor_module =
    Codegen.compile_handler_cases
      ~name 
      ~context ~motive 
      ~handler_cases
      ~handler_types 
      ~compiled_handler_types
      ~parameters 
      ~provenance
      ~recursor
  in
  let _module_name = DB.start_module module_name parameters in
  let previous_cases =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr recursor_module)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let _ = VB.(run @@ include_module ~module_expr:previous_cases) in
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

let add_handler ~name ~arguments ~handler =    
  let recursion_ctx = Ctx.get () in
  match List.assoc_opt name recursion_ctx.handler_types with
  | None -> Errors.fail ~info:"Unbound Constructor"
  | Some ty ->
      let case_name =
        Naming.handler_name ~recursor:recursion_ctx.name ~case:name
      in
      let arguments = 
        match arguments with 
        | None -> []
        | Some arguments -> arguments
      in 
      let handler = Termutils.mk_lambda arguments handler in 
      Ctx.add_handler_case name handler;
      VB.run (VB.define_term ~name:case_name ~ty handler)
