open Types
open Env

let add_recursor ~ind_decls ~rec_mod ~suffix =
  let rec split3 = function
    | [] -> ([], [], [])
    | (x, y, z) :: l ->
        let xs, ys, zs = split3 l in
        (x :: xs, y :: ys, z :: zs)
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
  let compiled_impl =
    Codegen.compile_recursor_implementation ~names ~ind_names ~rec_mod
      ~motive_module ~suffix ~ctx:parameters ~family_name
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
