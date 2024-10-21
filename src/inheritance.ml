open Env
open Types
open Bwd

(* Inheritance operators *)

let lookup_field_in_base ~field ~context =
  Context.base_linkage_elem context ~field |> Option.map snd

let rec linkage_concatenate ~(derived : Linkage.t) ~(base : Linkage.t) =
  let rec find_and_remove name fields =
    match fields with
    | Bwd.Emp -> (None, fields)
    | Bwd.Snoc (fields, (field, elem)) ->
        if Names.Id.equal field name then (Some (elem, fields), Bwd.Emp)
        else
          let result, rest = find_and_remove name fields in
          (result, Bwd.Snoc (rest, (field, elem)))
  in
  let inherit_one ~(name : Names.Id.t) ~(element : LinkageElem.t)
      ~(linkage : Linkage.t) =
    let rec find_field = function
      | Bwd.Emp -> false
      | Snoc (_, (field, _)) when Names.Id.equal name field -> true
      | Snoc (fields, _) -> find_field fields
    in
    match find_field linkage.fields with
    | true -> linkage
    | false ->
        (* Note that we're not doing anything with late binding *)
        let fields = Snoc (linkage.fields, (name, element)) in
        { linkage with fields }
  in
  let inherit_elements ~(elements : (Names.Id.t * LinkageElem.t) list)
      ~(linkage : Linkage.t) =
    List.fold_left
      (fun linkage (name, element) -> inherit_one ~name ~element ~linkage)
      linkage elements
  in

  (* Helpers above *)
  let rec loop linkage derived_fields base_fields =
    match derived_fields with
    | [] -> inherit_elements ~elements:(Bwd.to_list base_fields) ~linkage
    | (name, element) :: derived_fields -> (
        match find_and_remove name base_fields with
        | None, base_fields ->            
            let linkage = inherit_one ~name ~element ~linkage in
            loop linkage derived_fields base_fields
        | Some (base_element, dependencies), base_fields ->
            let linkage =
              inherit_elements ~elements:(Bwd.to_list dependencies) ~linkage
            in
            let element =
              linkage_elem_concatenate ~name ~derived:element ~base:base_element
            in            
            let linkage = inherit_one ~name ~element ~linkage in
            loop linkage derived_fields base_fields)
  in
  let linkage = { derived with fields = Bwd.Emp } in
  let derived_fields = Bwd.to_list derived.fields in
  let base_fields = base.fields in
  loop linkage derived_fields base_fields

(* General inheritance rule:
   hanlders from the base
   family come before the derived family's handlers
*)
and linkage_elem_concatenate ~name ~(derived : LinkageElem.t) ~(base : LinkageElem.t)
    : LinkageElem.t =
  let remove_duplicates lst =
    let rec aux seen = function
      | [] -> []
      | hd :: tl ->
          if List.mem hd seen then aux seen tl else hd :: aux (hd :: seen) tl
    in
    aux [] lst
  in
  (* TODO: Since we will never compile a field twice, 
     we can actualy check for equality of compiled functor 
     for cases where we don't overriding or not? *)
  match (derived, base) with
  | LinkageElem.ComputationalAxiom derived, LinkageElem.ComputationalAxiom _ ->
      LinkageElem.ComputationalAxiom derived
  | InductiveDefinition derived, InductiveDefinition base ->
      let inductive =
        VernacInductive.concatenate ~derived:derived.inductive
          ~base:base.inductive
      in
      InductiveDefinition { derived with inductive }
  | InductiveAxiom derived, InductiveAxiom _ -> InductiveAxiom derived
  | FamilyDefinition derived, FamilyDefinition base ->
      let linkage =
        linkage_concatenate ~derived:derived.linkage ~base:base.linkage
      in
      FamilyDefinition { derived with linkage }
  | FieldDefinition derived, FieldDefinition _ -> FieldDefinition derived
  | OpaqueFieldDefinition derived, OpaqueFieldDefinition _ ->
      OpaqueFieldDefinition derived
  
  (* Overriding *)
  | FieldDefinition derived, OpaqueFieldDefinition _ -> FieldDefinition derived
  | OpaqueFieldDefinition _, FieldDefinition base -> FieldDefinition base

  | RecursorDefinition derived, RecursorDefinition base ->
      let names = remove_duplicates (base.names @ derived.names) in
      let handlers = remove_duplicates (base.handlers @ derived.handlers) in
      RecursorDefinition { derived with names; handlers }
  | TheoremDefinition derived, TheoremDefinition base ->
      let names = remove_duplicates (base.names @ derived.names) in
      let handlers = remove_duplicates (base.handlers @ derived.handlers) in
      TheoremDefinition { derived with names; handlers }
  | MetaDataSection derived, MetaDataSection _ -> MetaDataSection derived
  | ClosingFact fact, ClosingFact _ -> ClosingFact fact
  | PartialRecursor derived, PartialRecursor _ -> PartialRecursor derived
  | _, _ ->
      let info = 
        Printf.sprintf 
          "Can't concatenate different kinds of linkage element: %s" 
          (Names.Id.to_string name)
      in
      Errors.fail ~info

let linkages_concatenate linkages =
  match linkages with
  | [] -> Errors.fail ~info:"concatenate_linkages: empty list"
  | linkage :: linkages ->
      List.fold_left
        (fun result_linkage linkage ->
          linkage_concatenate ~derived:result_linkage ~base:linkage)
        linkage linkages

(* Helper function for updating context during `inherit_one` *)
let update_context context name elem = 
   match context with 
   | LinkageCtx.Toplevel linkage -> 
      let linkage = { linkage with fields = Bwd.Snoc(linkage.fields, (name, elem)) } in 
      LinkageCtx.Toplevel linkage
   | LinkageCtx.Nested (c, linkage) -> 
      let linkage = { linkage with fields = Bwd.Snoc(linkage.fields, (name, elem)) } in 
      LinkageCtx.Nested (c, linkage)       

(* Generating fresh elements (new computational axioms) after
   inheriting a partial recursor *)
let generate_prec_handlers
      ~inductive_path 
      ~handlers ~inductive
      ~new_handlers ~context
      ~prect_name ~prec_suffix =   
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in  
  let prefix = Codegen.calculate_rec_principle_prefix ~inductive_path ~context in
  let construct_path name = Naming.qualid_point (Some prefix) name in    
  List.fold_left (fun (context, acc) constructor_name ->          
         let module_name = Naming.fresh_name ~prefix:"PrecCtx" in
         let compiled_context, parameters =
           Codegen.compile_linkage_context ~field_name:module_name context
         in  
         let constructor_path = construct_path constructor_name in 
         let recursor_path = construct_path prect_name in           
         let axiom_name, axiom, compiled_signature =
           Codegen.compile_prec_computational_axiom_signature 
             ~ctx:parameters
             ~constructor_name 
             ~constructor_path 
             ~inductive 
             ~recursor_path 
             ~handlers
             ~prec_suffix:prec_suffix               
         in
         let elem = 
           LinkageElem.ComputationalAxiom
           {
             name = axiom_name;
             axiom;
             compiled_context;
             compiled_signature;
             default_ctx_params;
           }
         in
         let context = update_context context axiom_name elem in
         context, ((axiom_name, elem) :: acc)) (context, []) new_handlers          
      |> function (_, l) -> List.rev l

(* Updating a single partial recursor element that
    is about to be inherited *)
let inherit_one_partial_recursor ~elem ~new_handlers ~context ~inductive = 
   match elem with 
   | LinkageElem.PartialRecursor 
     ({ name; handlers; inductive_path; prec_suffix; behaviour = old_behaviour; _ } as prec) ->       
       let new_behaviour = 
          new_handlers
          |> List.map (fun constructor_name -> 
                 constructor_name,
                 Naming.prec_computational_axiom_name 
                   ~constructor_name
                   ~prec_suffix)
       in             
       let behaviour = old_behaviour @ new_behaviour in 
       let compiled_context, _parameters =
        Codegen.compile_linkage_context ~field_name:name context
       in
       let elem = LinkageElem.PartialRecursor { prec with compiled_context; behaviour } in       
       (* Add the new computational axioms *)
       let context = update_context context name elem in
       let elements = 
         generate_prec_handlers
           ~inductive_path 
           ~handlers ~new_handlers 
           ~prect_name:name ~prec_suffix
           ~context ~inductive
       in 
       elem, elements
   | _ -> 
      Errors.fail 
        ~info:"inherit_one_partial_recursor: expected \ 
               a partial recursor linkage elem"

(* We want to inherit element from a base family into
   a derived family in interactive mode *)

(** [context] is the current linkage context we're building
    [linkage] in.
    E.g: 
    Nested ([context], [linkage])
    Toplevel ([linkage])
 *)
let rec inherit_one ~(name : Names.Id.t) ~(element : LinkageElem.t)
    ~(linkage : Linkage.t) ~(context : LinkageCtx.t) =
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
      let compiled_context, parameters =
        Codegen.compile_linkage_context ~field_name:name context
      in
      (* Inheriting a LinkageElem.t updates that linkage
         element wrt to the current context. It might also create
         new elements in addition to that update. This captures
         exact this idea. *)
      let element, fresh_elements =
        match element with
        | LinkageElem.InductiveDefinition inductive ->
            let compiled_impl, principles =
              Codegen.compile_inductive_implementation
                ~ind_def:inductive.inductive ~ctx:parameters ~family_name:name
            in
            let compiled_signature =
              Codegen.compile_inductive_signature ~ind_def:inductive.inductive
                ~ctx:parameters ~family_name:name
            in
            let recursors =
              Termutils.extract_handler_types_from_principle
                ~inductive:inductive.inductive ~principles
            in
            let default_ctx_params =
              context |> Context.family_linkage |> function
              | { default_ctx_params; _ } -> default_ctx_params
            in
            LinkageElem.InductiveDefinition
              {
                inductive with
                compiled_context;
                compiled_impl;
                compiled_signature;
                recursors;
                default_ctx_params;
              }, []

        (* Exhausitivity check, that never fails 
           becuase we make it exhaustive if it 
           is not already. *)
        | PartialRecursor prec ->

           (* List helper functions *)
           let get_portion_after sublist full_list =
             let rec take n lst =
               if n <= 0 then []
               else match lst with
                 | [] -> []
                 | h::t -> h :: take (n-1) t
             in
             let rec drop n lst =
               if n <= 0 then lst
               else match lst with
                 | [] -> []
                 | _::t -> drop (n-1) t
             in 
             let rec find_sublist acc = function
               | [] -> []
               | h :: t as l ->
                   if List.length l < List.length sublist then []
                   else if take (List.length sublist) l = sublist then
                     drop (List.length sublist) l
                   else find_sublist (h :: acc) t
             in
             find_sublist [] full_list
           in

           let inductive, _, _ =
              Context.lookup_inductive_for_recursion
                ~name:prec.inductive_path context
           in
           let inductive_handlers = 
             inductive 
             |> List.hd 
             |> fst 
             |> VernacInductive.extract_type_and_cstrs 
             |> snd 
             |> List.map fst 
           in
           let defined_handlers = 
             prec.behaviour |> List.map fst
           in 
           let remaining_handlers = get_portion_after defined_handlers inductive_handlers in
           
           begin match remaining_handlers with 
           | [] -> PartialRecursor { prec with compiled_context }, []
           | new_handlers -> 
              let elem, more = 
                inherit_one_partial_recursor
                  ~elem:element 
                  ~new_handlers 
                  ~context
                  ~inductive 
              in
              elem, more
           end

        | FamilyDefinition family -> (
            match family.linkage.base with
            | None ->
                let linkage =
                  let default_ctx_params =
                    Codegen.compile_default_params ~context:parameters
                  in
                  let empty_linkage =
                    {
                      family.linkage with
                      fields = Bwd.Emp;
                      default_ctx_params;
                      context = Bwd.of_list parameters;
                    }
                  in
                  inherit_elements
                    ~elements:(Bwd.to_list family.linkage.fields)
                    ~linkage:empty_linkage
                    ~context:(LinkageCtx.Nested (context, empty_linkage))
                in
                let compiled_signature =
                  Codegen.compile_linkage_signature linkage
                in
                let default_ctx_params =
                  context |> Context.family_linkage |> function
                  | { default_ctx_params; _ } -> default_ctx_params
                in
                FamilyDefinition
                  {
                    default_ctx_params;
                    compiled_context;
                    compiled_signature;
                    linkage;
                  }, []
            | Some base -> (
                (* TODO: store an actual path in the base *)
                let path = Libnames.qualid_of_ident base.name in
                match Context.local_lookup context path with
                | None ->
                    let linkage =
                      let default_ctx_params =
                        Codegen.compile_default_params ~context:parameters
                      in
                      let empty_linkage =
                        {
                          family.linkage with
                          fields = Bwd.Emp;
                          default_ctx_params;
                          context = Bwd.of_list parameters;
                        }
                      in
                      inherit_elements
                        ~elements:(Bwd.to_list family.linkage.fields)
                        ~linkage:empty_linkage
                        ~context:(LinkageCtx.Nested (context, empty_linkage))
                    in
                    let compiled_signature =
                      Codegen.compile_linkage_signature linkage
                    in
                    let default_ctx_params =
                      context |> Context.family_linkage |> function
                      | { default_ctx_params; _ } -> default_ctx_params
                    in
                    FamilyDefinition
                      {
                        default_ctx_params;
                        compiled_signature;
                        compiled_context;
                        linkage;
                      }, []
                | Some new_base ->
                    let new_base =
                      Linkage.path_subtitution new_base
                        ~source:(Naming.self_version new_base.name)
                        ~target:(Naming.self_version family.linkage.name)
                    in
                    let family_linkage =
                      (* family.linkage *)
                      { family.linkage with context = Bwd.of_list parameters }
                    in
                    (* Update the context too? *)
                    let _context =
                      LinkageCtx.Nested (context, family_linkage)
                    in
                    let linkage =
                      linkage_concatenate ~derived:family_linkage ~base:new_base
                    in
                    let linkage =
                      let default_ctx_params =
                        Codegen.compile_default_params ~context:parameters
                      in
                      let empty_linkage =
                        {
                          linkage with
                          fields = Bwd.Emp;
                          context = Bwd.of_list parameters;
                          default_ctx_params;
                        }
                      in
                      inherit_elements
                        ~elements:(Bwd.to_list linkage.fields)
                        ~linkage:empty_linkage
                        ~context:(LinkageCtx.Nested (context, empty_linkage))
                    in
                    (* Should the linkage context parameters not be updated? *)
                    let linkage =
                      Linkage.{ linkage with base = Some new_base }
                    in
                    let compiled_signature =
                      Codegen.compile_linkage_signature linkage
                    in
                    let default_ctx_params =
                      context |> Context.family_linkage |> function
                      | { default_ctx_params; _ } -> default_ctx_params
                    in
                    FamilyDefinition
                      {
                        default_ctx_params;
                        linkage;
                        compiled_context;
                        compiled_signature;
                      }, []))        
        
        (* late bound base? *)
        | TraitDefinition trait ->
            TraitDefinition { trait with compiled_context }, []

        | ComputationalAxiom comp ->
            ComputationalAxiom { comp with compiled_context }, []
        | InductiveAxiom axiom ->
            InductiveAxiom { axiom with compiled_context }, []
        | FieldDefinition field ->
            FieldDefinition { field with compiled_context }, []
        | MetaDataSection metadata ->
            MetaDataSection { metadata with compiled_context }, []
        | OpaqueFieldDefinition field ->
            OpaqueFieldDefinition { field with compiled_context }, []
        | ClosingFact fact -> ClosingFact { fact with compiled_context }, []
        (* Exhaustiveness checks *)
        | RecursorDefinition recursive ->
            let inductive, _, _ =
              Context.lookup_inductive_for_recursion
                ~name:recursive.inductive_path context
            in
            let name = List.hd recursive.names in
            Checks.check_exhaustive ~name ~inductive
              ~handlers:recursive.handlers;
            RecursorDefinition { recursive with compiled_context }, []
        | TheoremDefinition theorem ->
            let inductive, _, _ =
              Context.lookup_inductive_for_recursion
                ~name:theorem.inductive_path context
            in
            let name = List.hd theorem.names in
            Checks.check_exhaustive ~name ~inductive ~handlers:theorem.handlers;
            TheoremDefinition { theorem with compiled_context }, []
      in      
      let open Bwd.Infix in
      let fields = Snoc (linkage.fields, (name, element)) <@ fresh_elements in
      { linkage with fields }

and inherit_elements ~(elements : (Names.Id.t * LinkageElem.t) list)
    ~(linkage : Linkage.t) ~(context : LinkageCtx.t) =
  List.fold_left
    (fun linkage (name, element) ->
      inherit_one ~name ~element ~linkage ~context)
    linkage elements

let inherit_deps ~(field : Names.Id.t) ~(base : Linkage.t)
    ~(derived : Linkage.t) ~(context : LinkageCtx.t) =
  let rec find_dependencies fields =
    match fields with
    | Bwd.Emp -> []
    | Snoc (fields, (found_name, _)) when Names.Id.equal found_name field ->
        Bwd.to_list fields
    | Snoc (fields, _) -> find_dependencies fields
  in
  let deps = find_dependencies base.fields in
  inherit_elements ~elements:deps ~linkage:derived ~context

let inherit_name ~(name : Names.Id.t) =
  let context = Context.get () in
  let base = Context.base_linkage context in
  let linkage = Context.family_linkage context in
  let inherit_name ~(name : Names.Id.t) ~(base : Linkage.t)
      ~(linkage : Linkage.t) =
    let rec find_element name = function
      | Bwd.Emp -> None
      | Snoc (_, (field, element)) when Names.Id.equal name field ->
          Some element
      | Snoc (fields, _) -> find_element name fields
    in
    let element = find_element name base.fields in
    match element with
    | None ->
        let info =
          Printf.sprintf
            "Couldn't inherit %s because it was not found the the base or/and \
             further bound family"
            (Names.Id.to_string name)
        in
        Errors.fail ~info
    | Some (InductiveDefinition { inductive; _ } as element) ->           
       let names =          
         inductive 
         |> VernacInductive.extract_all_names 
         |> List.concat_map (fun (ind, ctrs) -> ind :: ctrs)          
         |> List.map (fun axiom -> 
                let axiom = Naming.inductive_axiom_name axiom in
                match find_element axiom base.fields with
                | Some element -> (axiom, element)
                | None -> Errors.fail ~info:"Couldn't find inductive axiom")              
       in
       let names = (name, element) :: names in
       List.fold_left 
       (fun linkage (name, element) -> 
         print_endline @@ Names.Id.to_string @@ name;
         inherit_one ~name ~element ~linkage ~context)
       linkage 
       names      
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

let inherit_partial_recursor ~(inductive_path: Libnames.qualid) =   
  let context = Context.get () in
  let base = Context.base_linkage context in
  match base with 
  | None -> Errors.fail ~info:"No base linkage"
  | Some base -> 
     base.fields
     |> Bwd.to_list
     |> List.iter (fun (_, elem) -> 
          match elem with 
          | LinkageElem.PartialRecursor 
            { name; inductive_path = i; behaviour; _ } when i = inductive_path -> 
            inherit_name ~name; 
            behaviour |> List.iter (fun (_, axiom) -> inherit_name ~name:axiom);
          | _ -> ())
