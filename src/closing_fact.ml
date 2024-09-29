open Types
open Env

let add ~name ~ty ~(script: Ltac_plugin.Tacexpr.raw_tactic_expr) = 
  Inheritance.inherit_dependencies ~prefix:name;  
  let type_name = Naming.fresh_name ~prefix:"ClosingFactTy" in
  let _ = Definition.add_definition ~name:type_name ty in 
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in        
  let ty =
    let expression = Constrexpr_ops.mkIdentC type_name in
    Resolver.resolve_constrexpr ~context ~expression
  in
  let compiled_signature = 
    Codegen.compile_lemma_signature ~name ~ty ~parameters
  in 
  let elem = 
    LinkageElem.ClosingFact 
      {
        type_name;
        compiled_context;
        compiled_signature;
        default_ctx_params;
        script;
      }
  in
  Context.add_field ~name ~elem
