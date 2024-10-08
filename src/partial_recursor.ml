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
  let _ = Definition.add_definition ~name:type_name ty in
  let context = Context.get () in
  
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty = Constrexpr_ops.mkIdentC type_name in  
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
  Context.add_field ~name ~elem
  
