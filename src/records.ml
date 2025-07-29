open Types
open Env

let add_record rd original_inductive =
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
  let elem =
    LinkageElem.RecordDefinition
      {
        rd;
        compiled_context;
        compiled_signature;
        default_ctx_params;
        original = original_inductive;
      }
  in  
  Context.add_field ~name ~elem;

  
  (* The *introduction* form *)
  let context = Context.get () in
  let family_name = Context.family_name context in
  let constructor_name = Naming.rocqet_record_constructor ~record_name:name ~family_name in
  let args_type = fields |> List.map snd in
  let record_type =
    let expression = Constrexpr_ops.mkIdentC name in
    Resolver.resolve_constrexpr ~context ~expression
  in 
  let constructor_type =
    Termutils.mk_arrow_ty ~args_type ~ret_type:record_type
  in
  (* Resolve it *)
  let constructor_type = Resolver.resolve_constrexpr ~context ~expression:constructor_type in   
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
  
  Context.add_field ~name:constructor_name ~elem;

  (* The *elimination* forms *)     
  fields
  |> List.map (fun (field_name, field_type) ->
         field_name, Termutils.mk_arrow_ty ~args_type:[record_type] ~ret_type:field_type)
  |> List.iter (fun (n, t) ->
         let context = Context.get () in
         let compiled_context, parameters =
           Codegen.compile_linkage_context ~field_name:n context
         in
         let compiled_signature =
           Codegen.compile_inductive_axiom ~name:n ~ty:t ~ctx:parameters
         in
         let elem = LinkageElem.InductiveAxiom { compiled_context; compiled_signature; default_ctx_params } in
         Context.add_field ~name:n ~elem
       )
    
let extend_record
      ~(rd: RecordDecl.t)
      ~(original_inductive: VernacInductive.t)
      ~(defaults: (Names.Id.t * Constrexpr.constr_expr) list) =
  rd |> ignore ; 
  original_inductive |> ignore ;
  defaults |> ignore
