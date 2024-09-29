open Types
open Env

let add_definition ~name ?body_type body_expr =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let body_expr = Resolver.resolve_constrexpr ~context ~expression:body_expr in
  let body_type =
    body_type
    |> Option.map (fun expression ->
           Resolver.resolve_constrexpr ~context ~expression)
  in
  let compiled_impl =
    Codegen.compile_definition ~name ?body_type ~body_expr parameters
  in
  let elem =
    LinkageElem.FieldDefinition
      { compiled_context; compiled_impl; default_ctx_params }
  in
  Context.add_field ~name ~elem

let add_opaque_definition ~name ~body_type ~body_expr = 
  Inheritance.inherit_dependencies ~prefix:name;
  let type_name = Naming.fresh_name ~prefix:"OpaqueTy" in
  let _ = add_definition ~name:type_name body_type in 
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in  
  let body_expr = Resolver.resolve_constrexpr ~context ~expression:body_expr in
  let body_type =
    let expression = Constrexpr_ops.mkIdentC type_name in
    Resolver.resolve_constrexpr ~context ~expression
  in
  let compiled_impl =
    Codegen.compile_definition ~name ~body_type ~body_expr parameters
  in
  let compiled_signature = 
    Codegen.compile_lemma_signature ~name ~ty:body_type ~parameters
  in 
  let elem =
    LinkageElem.OpaqueFieldDefinition
      {
        type_name;
        compiled_context;
        compiled_signature;
        compiled_impl;
        default_ctx_params
      }
  in
  Context.add_field ~name ~elem

let override ~name ~expr =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let base_elem = Inheritance.lookup_field_in_base ~field:name ~context in 
  match base_elem with
  | None -> Errors.fail ~info:"Can't override. No such element in base"
  | Some (LinkageElem.OpaqueFieldDefinition { type_name; _ }) ->
     let context = Context.get () in
     let default_ctx_params =
       context |> Context.family_linkage |> function
       | { default_ctx_params; _ } -> default_ctx_params
     in
     let compiled_context, parameters =
       Codegen.compile_linkage_context ~field_name:name context
     in  
     let body_expr = Resolver.resolve_constrexpr ~context ~expression:expr in
     let body_type =
       let expression = Constrexpr_ops.mkIdentC type_name in
       Resolver.resolve_constrexpr ~context ~expression
     in
     let compiled_impl =
       Codegen.compile_definition ~name ~body_type ~body_expr parameters
     in     
     let elem =
       LinkageElem.FieldDefinition
         {           
           compiled_context;           
           compiled_impl;
           default_ctx_params
         }
     in
     Context.add_field ~name ~elem     
  | Some _ -> Errors.fail ~info:"Can't override. Only Opaque fields can be overriden"
    
      
  
