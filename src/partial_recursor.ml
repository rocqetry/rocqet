open Env
open Types

let add ~(inductive_path : Libnames.qualid) ~(handlers: Names.Id.t list) = 
  let context = Context.get () in    
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive, _, _ =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in  
  let prec_suffix = Naming.fresh_name ~prefix:"PrecSuffix" in
  let inductive_name = inductive_path |> Naming.path_to_list |> List.rev |> List.hd in     
  let name = Naming.partial_recursor_name ~inductive_name ~prec_suffix in
  
  let type_name = Naming.fresh_name ~prefix:"PrecTy" in
  let ty = Termutils.compute_partial_recursor_signature ~inductive_path ~context in  
  (*let sigma, env = Termutils.global_env () in
  let s = Ppconstr.pr_constr_expr env sigma ty in 
  Feedback.msg_warning s;*)
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
  let behaviour = 
    handlers 
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
       behaviour;
     }
  in 
  Context.add_field ~name ~elem; 
  
  (* Computational Axioms *)
  let prefix = Codegen.calculate_rec_principle_prefix ~inductive_path ~context in
  let construct_path name = Naming.qualid_point (Some prefix) name in  
  let _ =     
    handlers 
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
               ~constructor_name ~constructor_path ~inductive ~recursor_path ~handlers ~prec_suffix                  
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
  
  let _ = Inheritance.inherit_partial_recursor ~inductive_path ~new_handlers:handlers in
  
  (* Define the new partial recursor and it's computational axioms *)
  let _ = 
    inherited_handlers 
    |> List.iter (fun n -> Printf.printf "%s\n" (Names.Id.to_string n))
  in 
  
  let handlers = inherited_handlers @ handlers in
  add ~inductive_path ~handlers
