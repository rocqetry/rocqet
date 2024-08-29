open Env
open Types
(* Generic inheritance operators *)

(* Inherit Element from both the base and *all* further bound families *)
let inherit_element ~field ~linkage ~context =
  let further_elem = Context.further_bound_linkage_elem context ~field in
  let further_subst elem l =
    Linkage.path_substitution_elem elem
      ~source:(Linkage.top_most_self_name l)
      ~target:(Linkage.top_most_self_name linkage)
  in
  let base_subst elem l =
    Linkage.path_substitution_elem elem
      ~source:(Naming.self_version l.Linkage.name)
      ~target:(Naming.self_version linkage.name)
  in
  let further_elem =
    match further_elem with
    | [] ->        
       None
    | (first_l, first_e) :: rest ->
       failwith "further" |> ignore;
        Some
          (List.fold_right
             (fun (l, e) furthers ->
               Linkage.concatenate_elem (further_subst e l) furthers)
             rest
             (further_subst first_e first_l))
  in
  let base_elem =
    Context.base_linkage_elem context ~field
    |> Option.map (fun (base, elem) -> base_subst elem base)
  in
  match (further_elem, base_elem) with
  | None, None -> None
  | Some further, None -> Some further
  | None, Some base -> Some base
  | Some further, Some base -> Some (Linkage.concatenate_elem further base)

(* This updates the context so you must call Context.get again after using this *)
let inherit_dependencies ~prefix =
  let context = Context.get () in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in
  let further_subst further =
    Linkage.path_subtitution further
      ~source:(Linkage.top_most_self_name further)
      ~target:(Linkage.top_most_self_name linkage)
  in
  let further = Context.further_bound_linkage context in
  let further =
    match further with
    | [] -> None
    | x :: xs ->         
         (* let s = Printf.sprintf "%s\n" (Names.Id.to_string x.name) in 
         _xs |> List.iter (fun (x : Linkage.t) -> Printf.printf "%s\n" (Names.Id.to_string x.name));
         failwith s |> ignore;*)
        let f further furthers =
          Linkage.concatenate ~derived:(further_subst further) ~base:furthers
        in
        (* Some (further_subst x)*)
        Some
          ((* Codegen.compute_linkage None*)
             (List.fold_right f xs (further_subst x)))
  in
  let linkage =
    match (base, further) with
    | None, None -> linkage
    | Some base, None ->
        let base =
          match Linkage.context_match base linkage with
          | `Less | `More ->
              Codegen.compute_linkage None
                { base with context = linkage.context }
          | `Equal -> base
        in
        let base =
          Linkage.path_subtitution base
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
        in
        Linkage.concatenate_prefix ~prefix ~derived:linkage ~base
    | None, Some further ->
        Linkage.concatenate_prefix ~prefix ~derived:linkage ~base:further
    | Some base, Some further ->
        let base =
          match Linkage.context_match base linkage with
          | `Less | `More ->
              Codegen.compute_linkage None
                { base with context = linkage.context }
          | `Equal -> base
        in
        let base =
          Linkage.path_subtitution base
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
        in
        let base = Linkage.concatenate_recursive ~base:further ~derived:base in
        let _ = 
          base.fields
          |> Bwd.Bwd.iter (fun (name, elem) ->                  
                 Printf.printf "Elem: %s\n" (Names.Id.to_string name);
                 match elem with 
                 | LinkageElem.FamilyDefinition { linkage; _ } -> 
                       linkage.fields 
                       |> Bwd.Bwd.iter (fun (name, _) -> Printf.printf "Inner Elem: %s\n" (Names.Id.to_string name))
                 | _ -> ())
        in
        (* failwith "" |> ignore;*)
        let base = { base with name = further.name } in
        let base = Codegen.compute_linkage None base in
        let linkage =
          Linkage.concatenate_recursive_prefix ~prefix ~derived:linkage ~base
        in
        Codegen.compute_linkage None linkage
  in
  Context.replace ~linkage
