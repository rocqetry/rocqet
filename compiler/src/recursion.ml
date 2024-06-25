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
      ~handlers:(handler_types |> List.map fst)
      ~suffix
      ~ctx:parameters
      ~handler_cases:module_name
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
    Codegen.compile_motives 
      ~names:[name] 
      ~motives:[motive_expr] 
      ~ctx:parameters 
      ~family_name:name
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
          ~arguments:(parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
      in
  let _ = include_module ~module_expr:applied_motive |> run in
  let handler_types =  handler_types_table name recursor in
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
        motive_expr = [motive_expr];
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
        Nameops.add_prefix (Names.Id.to_string recursion_ctx.name) name
      in
      Ctx.add_handler_case name handler;
      define_term ~name:case_name ~ty handler |> run

