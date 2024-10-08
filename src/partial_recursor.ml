open Env
open Types

let add ~(inductive_path : Libnames.qualid) = 
  let context = Context.get () in    
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive, _, _ =
    Env.Context.lookup_inductive_for_recursion ~name:inductive_path context
  in  
  let handlers = 
    inductive 
    |> List.hd 
    |> fst 
    |> VernacInductive.extract_type_and_cstrs 
    |> snd 
    |> List.map fst 
  in
  let inductive_name = inductive_path |> Naming.path_to_list |> List.rev |> List.hd in   
  let family_name = Context.family_name context in
  let name = Naming.partial_recursor_name ~inductive_name ~family_name in
  
  let type_name = Naming.fresh_name ~prefix:"PrecTy" in
  let ty = Termutils.compute_partial_recursor_signature ~inductive_path ~context in  
  let sigma, env = Termutils.global_env () in
  let s = Ppconstr.pr_constr_expr env sigma ty in 
  Feedback.msg_warning s;
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
  let elem = 
    LinkageElem.PartialRecursor 
     { 
       inductive_path;
       compiled_signature;
       compiled_context;
       type_name; 
       name;
       default_ctx_params;
       handlers;
     }
  in 
  Context.add_field ~name ~elem; 
  
  let prefix = Codegen.calculate_rec_principle_prefix ~inductive_path ~context in
  
  
  
  let module_name = Naming.fresh_name ~prefix:"Freshforprec" in
  let results = ref [] in
  let _ = 
    let open Backend.Vernac in
    Backend.Vernac.run @@
      Backend.Vernac.define_moduletype ~module_name ~parameters ~body:(fun _ctx -> 
          let* _ = 
            thunk (fun () -> 
                let axioms = 
                  Termutils.generate_prec_computational_axioms
                    ~inductive
                    ~recursor_name:name 
                    ~context 
                    ~prefix
                in
                results := axioms;
                return ()) in 
          return ()
        )
  in
  let _ =
    !results 
    |> List.iter (fun (name, equation) -> 
         Feedback.msg_warning (Pp.str (Names.Id.to_string name));          
         let s = Ppconstr.pr_constr_expr env sigma equation in 
         Feedback.msg_warning s)
  in 

  ()
  
