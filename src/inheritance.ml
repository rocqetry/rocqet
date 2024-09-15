open Env
open Types
open Bwd

(* Generic inheritance operators *)

(* Inherit Element from both the base and *all* further bound families *)
let inherit_element ~field ~linkage ~context =
  let further_elem = Context.further_bound_linkage_elem context ~field in
  (* This should not be the top most linkage, but the
     linkage which is this further binding was found *)
  let subst (target, source) elem =
    Linkage.path_substitution_elem elem
      ~source:(Naming.self_version source)
      ~target:(Naming.self_version target)
  in
  let _further_subst elem l =
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
    | [] -> None
    | (m, _first_l, first_e) :: rest ->
        (* failwith "further" |> ignore;*)
        Some
          (List.fold_right
             (fun (m, _l, e) furthers ->
               Linkage.concatenate_elem (subst m e) furthers)
             rest (subst m first_e))
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


(* We want to inherit element from a base family into 
   a derived family in interactive mode *)
let inherit_one
      ~(name: Names.Id.t)
      ~(element: LinkageElem.t)
      ~(linkage: Linkage.t) =
  let rec find_field = function
    | Bwd.Emp -> false
    | Bwd.Snoc (_, (field, _)) when Names.Id.equal name field -> true
    | Bwd.Snoc (fields, _) -> find_field fields
  in  
  match find_field linkage.fields with
  | true -> linkage (* Field has already been inherited *)
  | false ->
     (* Various checks to ensure correctness *)
     (* We need to update the context of the inherited fields *)
     (* Just a hack as compile_linkage_context accepts a ctx, but unwraps 
       it and looks at the parameters anyway. *)
     let context = LinkageCtx.Toplevel linkage in
     let compiled_context, _ = Codegen.compile_linkage_context ~field_name:name context in
     let element = 
          match element with
          | LinkageElem.InductiveDefinition inductive -> 
              LinkageElem.InductiveDefinition { inductive with compiled_context }
          (* TODO: Update wrt late bound base family *)
          | LinkageElem.FamilyDefinition  family ->               
             LinkageElem.FamilyDefinition { family with compiled_context }
          | LinkageElem.ComputationalAxiom comp ->
            LinkageElem.ComputationalAxiom { comp with compiled_context } 
          | LinkageElem.FieldDefinition field -> 
              LinkageElem.FieldDefinition { field with compiled_context}
          | LinkageElem.MetaDataSection metadata -> 
              LinkageElem.MetaDataSection { metadata with compiled_context}
          | LinkageElem.OpaqueFieldDefinition field -> 
              LinkageElem.OpaqueFieldDefinition { field with compiled_context}
          (* Exhaustiveness checks *)
          | LinkageElem.RecursorDefinition recursive -> 
              LinkageElem.RecursorDefinition { recursive with compiled_context }
          | LinkageElem.TheoremDefinition theorem -> 
              LinkageElem.TheoremDefinition { theorem with compiled_context }
      in 
      let fields = Bwd.Snoc (linkage.fields, (name, element)) in
      { linkage with fields }

let inherit_elements
      ~(elements: (Names.Id.t * LinkageElem.t) list)
      ~(linkage : Linkage.t) =
  List.fold_left 
    (fun linkage (name, element) -> inherit_one ~name ~element ~linkage) 
    linkage 
    elements

let inherit_deps
      ~(field : Names.Id.t)
      ~(base : Linkage.t)
      ~(derived : Linkage.t) =
  let rec find_dependencies fields =
      match fields with
      | Bwd.Emp -> []
      | Bwd.Snoc (fields, (found_name, _)) when Names.Id.equal found_name field ->
           Bwd.to_list fields
      | Bwd.Snoc (fields, _) -> find_dependencies fields
  in
  let deps = find_dependencies base.fields in
  inherit_elements ~elements:deps ~linkage:derived

(* This updates the context so you must call Context.get again after using this *)
let inherit_dependencies ~prefix =
  let context = Context.get () in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in
  let subst (target, source) l =
    Linkage.path_subtitution l
      ~source:(Naming.self_version source)
      ~target:(Naming.self_version target)
  in
  let _further_subst further =
    Linkage.path_subtitution further
      ~source:(Linkage.top_most_self_name further)
      ~target:(Linkage.top_most_self_name linkage)
  in
  let further = Context.further_bound_linkage context in
  let further =
    match further with
    | [] -> None
    | (m, x) :: xs ->
        let f (m, further) furthers =
          Linkage.concatenate ~derived:(subst m further) ~base:furthers
        in
        Some (List.fold_right f xs (subst m x))
  in
  let linkage =
    match (base, further) with
    | None, None -> linkage
    | Some base, None ->
        (*let base =
          match Linkage.context_match base linkage with
          | `Less | `More ->
              Codegen.compute_linkage None
                { base with context = linkage.context }
          | `Equal -> base
        in*)
        let base =
          Linkage.path_subtitution base
            ~source:(Naming.self_version base.name)
            ~target:(Naming.self_version linkage.name)
        in
        (* Linkage.concatenate_prefix ~prefix ~derived:linkage ~base*)
        inherit_deps ~field:prefix ~base ~derived:linkage
    | None, Some further ->
        (* Linkage.concatenate_prefix ~prefix ~derived:linkage ~base:further *)
        inherit_deps ~field:prefix ~base:further ~derived:linkage
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
        let base = Linkage.concatenate ~base:further ~derived:base in
        let base = { base with name = further.name } in
        let base = Codegen.compute_linkage None base in
        let linkage =
          Linkage.concatenate_prefix ~prefix ~derived:linkage ~base
        in
        Codegen.compute_linkage None linkage
  in
  Context.replace ~linkage
  
(* 
let inherit_one_element ~element ~linkage =
  failwith ""

let inherit_elements ~elements ~linkage =
   failwith ""

let path_substitution ~source ~target = 

(* derived has the preference over base *)
let linkage_concatenate ~base ~derived =
  failwith ""
 *)
