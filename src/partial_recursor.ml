open Env
open Types

let add 
      ~(inductive_path : Libnames.qualid)        
      ~(inherited_handlers: Names.Id.t list) 
      ~(handlers: Names.Id.t list) = 
  let context = Context.get () in    
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive, _, _ =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let prec_suffix = Naming.fresh_name ~prefix:"PrecSuffix" in
  let inductive_name = inductive_path |> Naming.extract_path_base in
  let name = Naming.partial_recursor_name ~inductive_name ~prec_suffix in
  
  let type_name = Naming.fresh_name ~prefix:"PrecTy" in
  let ty = Termutils.compute_partial_recursor_signature ~inductive_path ~context in  
  let _ = Definition.add_definition ~name:type_name ty in
  let context = Context.get () in
  
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
  let defining_handlers = 
    (* We don't create equations for inherited handlers *)
    handlers 
    |> List.filter (fun constructor_name -> 
         not (List.mem constructor_name inherited_handlers))
  in 
  let behaviour = 
    defining_handlers
    |> List.map (fun constructor_name -> 
           constructor_name,
           Naming.prec_computational_axiom_name 
             ~constructor_name
             ~prec_suffix)
  in   
  let elem = 
    LinkageElem.PartialRecursor 
     { 
       inductive_path;
       compiled_signature;
       compiled_context;
       type_name; 
       name;
       prec_suffix;
       default_ctx_params;
       handlers;
       defining_handlers;
       behaviour;
     }
  in 
  Context.add_field ~name ~elem; 
  
  (* Computational Axioms *)
  let prefix = Codegen.calculate_rec_principle_prefix ~inductive_path ~context in
  let construct_path name = Naming.qualid_point (Some prefix) name in  
  let _ =  
    defining_handlers
    |> List.iter (fun constructor_name -> 
         let context = Context.get () in
         let module_name = Naming.fresh_name ~prefix:"PrecCtx" in
           let compiled_context, parameters =
             Codegen.compile_linkage_context ~field_name:module_name context
           in           
           let constructor_path = construct_path constructor_name in 
           let recursor_path = construct_path name in
           let axiom_name, axiom, compiled_signature =
             Codegen.compile_prec_computational_axiom_signature ~ctx:parameters
               ~constructor_name ~constructor_path
               ~inductive ~recursor_path ~handlers ~prec_suffix                  
           in
           let elem =
             LinkageElem.ComputationalAxiom
               {
                 name = axiom_name;
                 axiom;
                 compiled_context;
                 compiled_signature;
                 default_ctx_params;
               }
           in
           Context.add_field ~name:axiom_name ~elem)
  in

  ()
  
let extend 
      ~(inductive_path : Libnames.qualid)   
      ~(inherited_handlers: Names.Id.t list)
      ~(handlers: Names.Id.t list) =  
  
  (* i.e Make inherited partial recursors exhaustive *)
  let _ = Inheritance.inherit_partial_recursor ~inductive_path in
  
  let handlers = inherited_handlers @ handlers in
  add ~inductive_path ~inherited_handlers ~handlers
