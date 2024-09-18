open Env
open Types
open Bwd

(* Generic inheritance operators *)

let lookup_field_in_base ~field ~context =    
  Context.base_linkage_elem context ~field
  |> Option.map snd

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
          | FamilyDefinition family -> FamilyDefinition { family with compiled_context }

          | ComputationalAxiom comp ->
            ComputationalAxiom { comp with compiled_context }
          | InductiveConstr constr ->
             InductiveConstr { constr with compiled_context }
          | FieldDefinition field -> 
              FieldDefinition { field with compiled_context }
          | MetaDataSection metadata -> 
              MetaDataSection { metadata with compiled_context }
          | OpaqueFieldDefinition field -> 
             OpaqueFieldDefinition { field with compiled_context }

          (* Exhaustiveness checks *)
          | RecursorDefinition recursive -> 
              RecursorDefinition { recursive with compiled_context }
          | TheoremDefinition theorem -> 
              TheoremDefinition { theorem with compiled_context }
      in 
      let fields = Snoc (linkage.fields, (name, element)) in
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
      | Snoc (fields, (found_name, _)) when Names.Id.equal found_name field ->
           Bwd.to_list fields
      | Snoc (fields, _) -> find_dependencies fields
  in
  let deps = find_dependencies base.fields in
  inherit_elements ~elements:deps ~linkage:derived

let inherit_name
     ~(name: Names.Id.t) =     
  let context = Context.get () in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in  
  let inherit_name
        ~(name: Names.Id.t)
        ~(base: Linkage.t)
        ~(linkage: Linkage.t) =
    let rec find_element = function
      | Bwd.Emp -> None
      | Bwd.Snoc (_, (field, element)) when Names.Id.equal name field -> Some element
      | Bwd.Snoc (fields, _) -> find_element fields
    in
    let element = find_element base.fields in
    match element with
    | None ->
       let info =
         Printf.sprintf
           "Couldn't inherit %s because it \
            was not found the the base or/and \
            further bound family"
           (Names.Id.to_string name)
       in
       Errors.fail ~info
    | Some element -> inherit_one ~name ~element ~linkage
  in  
  match base with  
  | Some base ->
     let linkage = inherit_deps ~field:name ~base ~derived:linkage in
     let linkage = inherit_name ~name ~base ~linkage in     
     Context.replace ~linkage
  | _ -> Errors.fail ~info:"There is not base to inherit from"
  

(** This updates the context so you must call Context.get again after using this *)
let inherit_dependencies ~prefix =
  let context = Context.get () in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in  
  let linkage =
    match base with
    | None -> linkage
    | Some base -> inherit_deps ~field:prefix ~base ~derived:linkage
  in   
  Context.replace ~linkage

let rec find_and_remove name fields =
  match fields with
  | Bwd.Emp -> None, fields
  | Bwd.Snoc (fields, (field, elem))  ->
     if Names.Id.equal field name then
       Some (elem, fields), Bwd.Emp
     else
       let result, rest = find_and_remove name fields in
       result, Bwd.Snoc (rest, (field, elem))

(** Performs reparameterization of base wrt derived *)
let ensure_matching_parameters
      ~(derived: Linkage.t)
      ~(base: Linkage.t) =
  let derived_len = Bwd.length derived.context in
  let base_len = Bwd.length base.context in
  let compare_result = compare derived_len base_len in
  if compare_result = 0 then base
  else if compare_result < 0 then
     (* The base context has more params.
        We need to reparameterize via adding dummy args *)
    Errors.fail ~info:"TODO: reparam more"
  else (* if compare_result > 0 *)
    (* The base context has less params.
        We just add extra unused params from the
        derived to it *)
    Errors.fail ~info:"TODO: reparam less"    

let rec linkage_concatenate ~(derived: Linkage.t) ~(base: Linkage.t) =  
  let base = ensure_matching_parameters ~derived ~base in
  let rec loop linkage derived_fields base_fields =
    match derived_fields with
    | [] -> inherit_elements ~elements:(Bwd.to_list base_fields) ~linkage
    | (name, element) :: derived_fields ->
       match find_and_remove name base_fields with
       | None, base_fields ->
          let linkage = inherit_one ~name ~element ~linkage in
          loop linkage derived_fields base_fields
       | Some (base_element, dependencies), base_fields ->
          let linkage = inherit_elements ~elements:(Bwd.to_list dependencies) ~linkage in
          let element = linkage_elem_concatenate ~derived:element ~base:base_element ~linkage in
          let linkage = inherit_one ~name ~element ~linkage in
          loop linkage derived_fields base_fields
  in    
  let linkage = { derived with fields = Bwd.Emp } in
  let derived_fields = Bwd.to_list derived.fields in
  let base_fields = base.fields in
  loop linkage derived_fields base_fields

(* General inheritance rule:
   hanlders from the base
   family come before the derived family's handlers
*)
and linkage_elem_concatenate
  ~(derived: LinkageElem.t)
  ~(base: LinkageElem.t)
  ~(linkage: Linkage.t) =
  let remove_duplicates lst =
      let rec aux seen = function
        | [] -> []
        | hd :: tl ->
            if List.mem hd seen then aux seen tl else hd :: aux (hd :: seen) tl
      in
      aux [] lst
  in
  match derived, base with
  | LinkageElem.ComputationalAxiom derived, LinkageElem.ComputationalAxiom _ ->
     LinkageElem.ComputationalAxiom derived
  | InductiveDefinition derived, InductiveDefinition base ->
     let inductive =
       VernacInductive.concatenate
         ~derived:derived.inductive
         ~base:base.inductive
     in
     let context = LinkageCtx.Toplevel linkage in
     let field_name = inductive |> VernacInductive.extract_inductive_name in
     let compiled_context, params = Codegen.compile_linkage_context ~field_name context in
     let compiled_impl, principles =
       Codegen.compile_inductive_implementation
         ~ind_def:inductive
         ~ctx:params
         ~family_name:linkage.name
     in
     let recursors = Termutils.extract_handler_types_from_principle ~inductive ~principles in  
     InductiveDefinition { derived with compiled_context; compiled_impl; recursors; }
  | InductiveConstr derived, InductiveConstr _ ->
    InductiveConstr derived 
  | FamilyDefinition derived, FamilyDefinition base ->
     let linkage = linkage_concatenate ~derived:derived.linkage ~base:base.linkage in
     let compiled_signature = Codegen.compile_linkage_signature linkage in
     let compiled_impl = Codegen.compile_nested_linkage linkage in
     FamilyDefinition { derived with linkage; compiled_impl; compiled_signature }
  | FieldDefinition derived, FieldDefinition _ ->
    FieldDefinition derived 
  | OpaqueFieldDefinition derived, OpaqueFieldDefinition _ ->
    OpaqueFieldDefinition derived
  | RecursorDefinition derived, RecursorDefinition base ->
     let names = remove_duplicates (base.names @ derived.names) in
     let handlers = remove_duplicates (base.handlers @ derived.handlers) in
     RecursorDefinition { derived with names; handlers; }
  | TheoremDefinition derived, TheoremDefinition base ->
     let names = remove_duplicates (base.names @ derived.names) in
     let handlers = remove_duplicates (base.handlers @ derived.handlers) in
     TheoremDefinition { derived with names; handlers; }
  | MetaDataSection derived, MetaDataSection _ ->
     MetaDataSection derived     
  | _, _ -> Errors.fail ~info:"Can't concatenate different kinds of linkage element"


