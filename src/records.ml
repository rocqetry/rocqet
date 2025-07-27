open Types
open Env 

let add_record rd =
  let context = Context.get () in
  let rd = Resolver.resolve_record ~context ~rd in
  let RecordDecl.{ name; ty; fields } = rd in  
  Inheritance.inherit_dependencies ~prefix:name;    
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in

  (* The record type *)
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty = Resolver.resolve_constrexpr ~context ~expression:ty in
  let compiled_signature =
    Codegen.compile_inductive_axiom ~name ~ty ~ctx:parameters
  in
  let elem = LinkageElem.RecordDefinition { rd; compiled_context; compiled_signature; default_ctx_params } in  
  Context.add_field ~name ~elem;

  
  (* The record constructor *)
  let family_name = Context.family_name context in
  let constructor_name = Naming.record_constructor ~record_name:name ~family_name in
  let args_type = fields |> List.map snd in
  let ret_type =
    let expression = Constrexpr_ops.mkIdentC name in
    Resolver.resolve_constrexpr ~context ~expression
  in 
  let constructor_type = Termutils.mk_arrow_ty ~args_type ~ret_type in 
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let compiled_signature =
    Codegen.compile_inductive_axiom ~name:constructor_name ~ty:constructor_type ~ctx:parameters
  in
  let elem =
    LinkageElem.RecordConstrAxiom {
        name = constructor_name;
        record_name = name;
        fields = fields |> List.map fst;
        compiled_context;
        compiled_signature;
        default_ctx_params
    }
  in
  
  Context.add_field ~name:constructor_name ~elem
  

