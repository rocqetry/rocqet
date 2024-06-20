open Types 
open Env 

let add_definition ~name ~body_type ~body_expr =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let compiled_impl =
    Codegen.compile_definition ~name ~body_type ~body_expr ~parameters
  in
  let elem =
    LinkageElem.FieldDefinition
      { body_expr; body_type; compiled_context; compiled_impl }
  in
  Context.add_field ~name ~elem
