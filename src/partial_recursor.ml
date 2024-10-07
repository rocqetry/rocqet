open Env
open Types

let add ~(inductive_path : Libnames.qualid) = 
  let context = Context.get () in  
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let inductive_name = inductive_path |> Naming.path_to_list |> List.rev |> List.hd in 
  (* TODO *)
  let handlers = [] in
  let family_name = Context.family_name context in
  let name = Naming.partial_recursor_name ~inductive_name ~family_name in
  (* TODO *)
  let type_name = Naming.fresh_name ~prefix:"PrecTy" in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty = Termutils.compute_partial_recursor_signature ~inductive_path ~context in  
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
  
