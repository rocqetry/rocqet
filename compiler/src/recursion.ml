open Types
open Env
open Bwd

let add_recursor ~ind_decls ~rec_mod ~suffix =
  let rec split3 = function
    | [] -> ([], [], [])
    | (x, y, z) :: l ->
        let xs, ys, zs = split3 l in
        (x :: xs, y :: ys, z :: zs)
  in
  let rec lookup_inductive name context = 
    let f (linkage: Linkage.t) (found_name, elem) = 
      match elem with 
       | LinkageElem.InductiveDefinition { inductive;  _ } 
           when Names.Id.equal found_name name -> 
           Some (inductive, linkage)
       | _ -> None
    in 
    match context with            
    | LinkageCtx.Toplevel linkage -> linkage.fields |> Bwd.find_map (f linkage)       
    | LinkageCtx.Nested (context, linkage) -> 
       match linkage.fields |> Bwd.find_map (f linkage) with 
       | None -> lookup_inductive name context
       | Some result -> Some result 
  in 
  let names, ind_names, motives = split3 ind_decls in
  let recursor_name = List.hd names in
  Inheritance.inherit_dependencies ~prefix:recursor_name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:recursor_name context
  in
  let family_name = Context.family_name context in
  let motive_module =
    Codegen.compile_motives ~names ~motives ~ctx:parameters ~family_name
  in
  let compiled_signature =
    Codegen.compile_recursor_signature ~names ~motive_module ~ctx:parameters
      ~family_name
  in
  let inductive, linkage =
    (* No mutual inductive yet *)
    let name = ind_names |> List.hd |> Libnames.qualid_basename in 
    match lookup_inductive name context with 
    | None -> Errors.fail ~info:"Unbound inductive"  
    | Some result -> result 
  in 
  let compiled_impl =
    Codegen.compile_recursor_implementation 
      ~inductive
      ~linkage
      ~names
      (* ~ind_names *)
      ~rec_mod
      ~motive_module 
      ~suffix 
      ~ctx:parameters 
      ~family_name
  in
  let elem =
    LinkageElem.RecursorDefinition
      {
        names;
        ind_names;
        recursor_module = rec_mod;
        motive_module;
        suffix;
        compiled_context;
        compiled_signature;
        compiled_impl;
      }
  in
  Context.add_field ~name:recursor_name ~elem
