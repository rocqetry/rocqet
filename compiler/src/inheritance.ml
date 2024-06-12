open Env
open Types

(* This updates the context so you must call Context.get again after using this *)
let inherit_dependencies ~prefix =
  let context = Context.get () in
  let further = Context.further_bound_linkage context in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in
  let linkage =
    match (base, further) with
    | None, None -> linkage
    | Some base, None ->
       let base =         
         match Linkage.context_match base linkage with
         | `Less | `More -> 
            Codegen.recompute_linkage { base with context = linkage.context }
         | `Equal -> base
       in
       let base =
          Linkage.path_subtitution base
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
       in       
        Linkage.concatenate_prefix ~prefix ~derived:linkage ~base
    | None, Some further ->
        let further =
          Linkage.path_subtitution further
            ~source:(Linkage.top_most_self_name further)
            ~target:(Linkage.top_most_self_name linkage)
        in
        Linkage.concatenate_prefix ~prefix ~derived:linkage ~base:further
    | Some base, Some further ->
        let base =         
         match Linkage.context_match base linkage with
         | `Less | `More -> 
            Codegen.recompute_linkage { base with context = linkage.context } 
         | `Equal -> base
       in
        let further =             
              Linkage.path_subtitution further
                ~source:(Linkage.top_most_self_name further)
                ~target:(Linkage.top_most_self_name linkage)
            in            
        let base =          
           Linkage.path_subtitution base
           ~source:(Naming.self_version base.name)
           ~target:(Naming.self_version linkage.name)
         in
         let base = Linkage.concatenate_recursive_prefix ~prefix ~base:further ~derived:base in
         let base = { base with name = further.name } in
         let base = Codegen.recompute_linkage base in         
         let linkage = Linkage.concatenate_recursive ~derived:linkage ~base in
         Codegen.recompute_linkage linkage
  in
  Context.replace ~linkage
