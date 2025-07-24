open Types
open Env 

let add_record rd =
  let context = Context.get () in
  let rd = Resolver.resolve_record ~context ~rd in
  let RecordDecl.{ name; ty; _ } = rd in  
  Inheritance.inherit_dependencies ~prefix:name;    
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty = Resolver.resolve_constrexpr ~context ~expression:ty in
  let compiled_signature =
    Codegen.compile_inductive_axiom ~name ~ty ~ctx:parameters
  in  
  let elem = LinkageElem.RecordDefinition { rd; compiled_context; compiled_signature; default_ctx_params } in  
  Context.add_field ~name ~elem
  

