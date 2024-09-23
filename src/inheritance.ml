open Env
open Types
open Bwd

(* Inheritance operators *)

let lookup_field_in_base ~field ~context =    
  Context.base_linkage_elem context ~field
  |> Option.map snd

let rec linkage_concatenate ~(derived: Linkage.t) ~(base: Linkage.t) =
  let rec find_and_remove name fields =
      match fields with
      | Bwd.Emp -> None, fields
      | Bwd.Snoc (fields, (field, elem))  ->
         if Names.Id.equal field name then
           Some (elem, fields), Bwd.Emp
         else
           let result, rest = find_and_remove name fields in
           result, Bwd.Snoc (rest, (field, elem))
  in 
  let inherit_one
        ~(name: Names.Id.t)
        ~(element: LinkageElem.t)
        ~(linkage: Linkage.t) =     
    let rec find_field = function
      | Bwd.Emp -> false
      | Snoc (_, (field, _)) when Names.Id.equal name field -> true
      | Snoc (fields, _) -> find_field fields
    in  
    match find_field linkage.fields with
    | true -> linkage (* Field has already been inherited *)
    | false ->
       (* Note that we're not doing anything with late binding *)
       let fields = Snoc (linkage.fields, (name, element)) in
       { linkage with fields }
  in 
  let inherit_elements
        ~(elements: (Names.Id.t * LinkageElem.t) list)      
        ~(linkage : Linkage.t) =       
    List.fold_left 
      (fun linkage (name, element) -> inherit_one ~name ~element ~linkage) 
      linkage 
      elements
  in
  
  (* Helpers above *)
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
          let element =
            linkage_elem_concatenate              
              ~derived:element ~base:base_element              
          in          
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
  ~(base: LinkageElem.t) : LinkageElem.t =   
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
     InductiveDefinition { derived with inductive; }
  | InductiveConstr derived, InductiveConstr _ ->
    InductiveConstr derived 
  | FamilyDefinition derived, FamilyDefinition base ->          
     let linkage = linkage_concatenate ~derived:derived.linkage ~base:base.linkage in     
     FamilyDefinition { derived with linkage; }
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

(* We want to inherit element from a base family into 
   a derived family in interactive mode *)
(** [context] is the current linkage context we're building
    [linkage] in.
    E.g: 
    Nested ([context], [linkage])
    Toplevel ([linkage])
 *)
let rec inherit_one
      ~(name: Names.Id.t)
      ~(element: LinkageElem.t)
      ~(linkage: Linkage.t)
      ~(context: LinkageCtx.t) =
  let rec find_field = function
    | Bwd.Emp -> false
    | Snoc (_, (field, _)) when Names.Id.equal name field -> true
    | Snoc (fields, _) -> find_field fields
  in  
  match find_field linkage.fields with
  | true -> linkage (* Field has already been inherited *)
  | false ->
     (* Various checks to ensure correctness *)
     (* We need to update the context of the inherited fields *)

     (* Update the context with the updated linkage *)
     let context =
       match context with
       | LinkageCtx.Toplevel _ -> LinkageCtx.Toplevel linkage
       | Nested (context, _) -> Nested (context, linkage)
     in
     let compiled_context, parameters = Codegen.compile_linkage_context ~field_name:name context in     
     (*let _ =       
       List.iter (fun (name, e) ->
           let name = Names.Id.to_string name in
           let e = e |> Termutils.extract_functor_name |> Pretty.pretty_qualid in
           Feedback.msg_warning Pp.(str "Params " ++ str name ++ str " : " ++ str e))
         parameters
     in *)
     (*Feedback.msg_warning Pp.(str "Context: " ++ str (Pretty.pretty_qualid compiled_context));*)
     let element = 
          match element with
          | LinkageElem.InductiveDefinition inductive ->             
             let compiled_impl, principles =
               Codegen.compile_inductive_implementation
                 ~ind_def:inductive.inductive
                 ~ctx:parameters
                 ~family_name:name
             in
             let compiled_signature =
               Codegen.compile_inductive_signature
                 ~ind_def:inductive.inductive
                 ~ctx:parameters
                 ~family_name:name
             in 
             let recursors =
               Termutils.extract_handler_types_from_principle
                 ~inductive:inductive.inductive
                 ~principles
             in
             let default_ctx_params =
               context
               |> Context.family_linkage
               |> function { default_ctx_params; _ } -> default_ctx_params
             in
             (* TODO: Use the right default_ctx_params *)
             LinkageElem.InductiveDefinition
               { inductive with
                 compiled_context;
                 compiled_impl;
                 compiled_signature;
                 recursors;
                 default_ctx_params;                 
               }

          (* TODO: Update wrt late bound base family *)
          | FamilyDefinition family ->
             (* We need to compile the context again *)
             begin
               match family.linkage.base with
               | None -> FamilyDefinition { family with compiled_context }
               | Some base ->
                  (* We want to perform a local lookup
                     so we don't update a family with a non-late bound
                     family name. *)
                  let path = Libnames.qualid_of_ident base.name in
                  match Context.local_lookup context path with
                  | None -> FamilyDefinition { family with compiled_context }
                  | Some new_base ->                                          
                     let new_base =
                         Linkage.path_subtitution new_base
                           ~source:(Naming.self_version new_base.name)
                           ~target:(Naming.self_version family.linkage.name)
                     in
                     let family_linkage = (* family.linkage *)
                       { family.linkage with context = Bwd.of_list parameters }
                     in
                     let _context =
                       LinkageCtx.Nested (context, family_linkage)
                     in
                     let linkage = linkage_concatenate ~derived:family_linkage ~base:new_base in
                     let linkage =
                       let empty_linkage = { linkage with fields = Bwd.Emp } in
                       inherit_elements
                         ~elements:(Bwd.to_list linkage.fields)
                         ~linkage:empty_linkage
                         ~context:(LinkageCtx.Nested (context, empty_linkage))
                     in
                     let default_ctx_params =
                        Codegen.compile_default_params
                          ~context:parameters
                     in
                     let linkage = Linkage.{ linkage with base = Some new_base; default_ctx_params } in
                     let compiled_signature = Codegen.compile_linkage_signature linkage in
                     let compiled_impl = Codegen.compile_nested_linkage linkage in
                     FamilyDefinition { family with linkage; compiled_context; compiled_signature; compiled_impl }                     
             end

          | ComputationalAxiom comp -> ComputationalAxiom { comp with compiled_context }
          | InductiveConstr constr -> InductiveConstr { constr with compiled_context }
          | FieldDefinition field -> FieldDefinition { field with compiled_context }
          | MetaDataSection metadata -> MetaDataSection { metadata with compiled_context }
          | OpaqueFieldDefinition field -> OpaqueFieldDefinition { field with compiled_context }

          (* Exhaustiveness checks *)
          (* We don't want to do exhaustiveness
             checks when this function is called
             from linkage concatenation *)
          | RecursorDefinition recursive -> RecursorDefinition { recursive with compiled_context }
          | TheoremDefinition theorem -> TheoremDefinition { theorem with compiled_context }
      in 
      let fields = Snoc (linkage.fields, (name, element)) in
      { linkage with fields }

and inherit_elements
      ~(elements: (Names.Id.t * LinkageElem.t) list)      
      ~(linkage : Linkage.t)
      ~(context: LinkageCtx.t) =
  List.fold_left 
    (fun linkage (name, element) -> inherit_one ~name ~element ~linkage ~context) 
    linkage 
    elements

let inherit_deps
      ~(field : Names.Id.t)
      ~(base : Linkage.t)
      ~(derived : Linkage.t)
      ~(context : LinkageCtx.t) =
  let rec find_dependencies fields =
      match fields with
      | Bwd.Emp -> []
      | Snoc (fields, (found_name, _)) when Names.Id.equal found_name field ->
           Bwd.to_list fields
      | Snoc (fields, _) -> find_dependencies fields
  in
  let deps = find_dependencies base.fields in
  inherit_elements ~elements:deps ~linkage:derived ~context

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
      | Snoc (_, (field, element)) when Names.Id.equal name field -> Some element
      | Snoc (fields, _) -> find_element fields
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
    | Some element -> inherit_one ~name ~element ~linkage ~context
  in  
  match base with  
  | Some base ->
     let linkage = inherit_deps ~field:name ~base ~derived:linkage ~context in
     let linkage = inherit_name ~name ~base ~linkage in     
     Context.replace ~linkage
  | _ -> Errors.fail ~info:"There is no base to inherit from"
  

(** This updates the context so you must call Context.get again after using this *)
let inherit_dependencies ~prefix =
  let context = Context.get () in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in  
  let linkage =
    match base with
    | None -> linkage
    | Some base -> inherit_deps ~field:prefix ~base ~derived:linkage ~context
  in   
  Context.replace ~linkage
