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
    module_name : Names.Id.t;
    compiled_context : CompiledModuleType.t;
    name : Names.Id.t;
    inductive : VernacInductive.t;
    provenance : Linkage.t;
    motive : CompiledModule.t;
    suffix : RecKind.t;
  }

  let store = Summary.ref ~name:"RecursionCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no recursion context open"
    | Some store -> store

  let clear () = store := None
  let update recursion_data = store := Some recursion_data
end

(* let add_recursor ~ind_decls ~rec_mod ~suffix =
  let rec split3 = function
    | [] -> ([], [], [])
    | (x, y, z) :: l ->
        let xs, ys, zs = split3 l in
        (x :: xs, y :: ys, z :: zs)
  in
  let rec lookup_inductive name context =
    let f (linkage : Linkage.t) (found_name, elem) =
      match elem with
      | LinkageElem.InductiveDefinition { inductive; _ }
        when Names.Id.equal found_name name ->
          Some (inductive, linkage)
      | _ -> None
    in
    match context with
    | LinkageCtx.Toplevel linkage -> linkage.fields |> Bwd.find_map (f linkage)
    | LinkageCtx.Nested (context, linkage) -> (
        match linkage.fields |> Bwd.find_map (f linkage) with
        | None -> lookup_inductive name context
        | Some result -> Some result)
  in
  let names, ind_names, motives = split3 ind_decls in
  let recursor_name = List.hd names in
  Inheritance.inherit_dependencies ~prefix:recursor_name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:recursor_name context
  in
  let family_name = Context.family_name context in
  let motive_module =
    Codegen.compile_motives ~names ~motives ~ctx:parameters ~family_name
  in
  let compiled_signature =
    Codegen.compile_recursor_signature ~names ~motive_module ~ctx:parameters
      ~family_name
  in
  let inductive, linkage =
    (* No mutual inductive yet *)
    let name = ind_names |> List.hd |> Libnames.qualid_basename in
    match lookup_inductive name context with
    | None -> Errors.fail ~info:"Unbound inductive"
    | Some result -> result
  in
  let compiled_impl =
    Codegen.compile_recursor_implementation ~inductive ~linkage ~names ~rec_mod
      ~motive_module ~suffix ~ctx:parameters ~family_name
  in
  let elem =
    LinkageElem.RecursorDefinition
      {
        names;
        inductive;
        handlers = [];
        recursor_module = rec_mod;
        motive_module;
        suffix;
        compiled_context;
        compiled_signature;
        compiled_impl;
      }
  in
  Context.add_field ~name:recursor_name ~elem*)

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
          _;
        } =
    Ctx.get ()
  in      
  module_name |> ignore;
  let module_name = M.end_module () in
  let handlers = handler_types |> List.map fst in 
  let compiled_signature = 
    Codegen.compile_recursor_signature 
        ~names:[name]
        ~motive_module:motive
        ~ctx:parameters
        ~family_name:name
  in
  let compiled_impl = 
    Codegen.compile_recursor_implementation 
      ~inductive      
      ~provenance 
      ~recursor_name:name
      ~handlers
      ~suffix
      ~ctx:parameters
      ~handler_cases:module_name
  in 
  let elem =
    LinkageElem.RecursorDefinition
      {
        names = [ name ];
        inductive;
        recursor_module = module_name;
        motive_module = motive;
        compiled_signature;
        compiled_impl;
        compiled_context;
        suffix;
        handlers;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()

let include_handler_types (provenance : Linkage.t) (recursor: CompiledRecursor.t) = 
    let open Codegen.VernacBackend in 
    recursor.compiled_handlers
    |> List.map (fun (_case_name, handler_module) ->
           let arguments =
             let family =
               provenance.name |> Naming.self_version
               |> Libnames.qualid_of_ident
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
    |> flatmap |> run

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
  let motive = Resolver.resolve_constrexpr ~context ~expression:motive in
  let motive = 
    Codegen.compile_motives 
      ~names:[name] 
      ~motives:[motive] 
      ~ctx:parameters 
      ~family_name:name
  in
  let inductive, compiled_recursors, provenance = 
    Context.lookup_inductive_for_recursion ~name:inductive context 
  in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in    
  let _module_name = M.start_module module_name parameters in
  include_handler_types provenance recursor;  
  let open Codegen.VernacBackend in 
  let applied_motive =
        Termutils.apply_module
          ~functor_expr:(Termutils.ident_to_module_expr motive)
          ~arguments:(parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
      in
  let _ = include_module ~module_expr:applied_motive |> run in
  let handler_types =  handler_types_table name recursor in
  let recursion_ctx =
    Ctx.
      {
        parameters;
        suffix;
        handler_types;        
        module_name;
        name;        
        compiled_context;
        motive;
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
      let name =
        Nameops.add_prefix (Names.Id.to_string recursion_ctx.name) name
      in
      define_term ~name ~ty handler |> run

