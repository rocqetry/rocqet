open Types
open Env

(* Private store *)
module Ctx = struct
  type t = {    
    handler_types : (Names.Id.t * Constrexpr.constr_expr) list;    
    (* The name of the handlers that were supposed to be implemented *)
    implementing_handlers : Names.Id.t list;
    (* The handlers actually implemented or inherited *)
    defined_handlers: Names.Id.t list;
    name : Names.Id.t;
    inductive : VernacInductive.t;    
    suffix : RecKind.t;
    (* the name of the arguments to this FRecursion *)
    arguments : Names.Id.t list;
    inductive_path : Libnames.qualid;
    rec_principle_prefix : Libnames.qualid;    
  }

  let store = Summary.ref ~name:"RecursionCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no recursion context open"
    | Some store -> store

  let clear () = store := None
  let update recursion_data = store := Some recursion_data

  let add_handler name  =
    let ctx = get () in
    let ctx = { ctx with defined_handlers = name :: ctx.defined_handlers } in
    update ctx  
end

let close_recursion () =
  let Ctx.
        {          
          name;
          inductive;
          suffix;          
          defined_handlers;          
          arguments;
          inductive_path;
          rec_principle_prefix;
          implementing_handlers;
          _;
        } =
    Ctx.get ()
  in
  Checks.check_exhaustive ~name ~inductive ~handlers:defined_handlers;
  (* We use this becuase the handlers have to be in the right order *)
  let handlers =
    let _, constructors =
      inductive |> List.hd |> fst |> VernacInductive.extract_type_and_cstrs
    in
    constructors |> List.map fst
  in
  let context = Context.get () in
  let family = context |> Context.family_name |> Names.Id.to_string in
  let module_name =
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Ctx" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature
      ~names:[ name ]
      ~ctx:parameters
      ~family_name:name      
  in
  let elem =
    LinkageElem.RecursorDefinition
      {
        handlers;
        names = [ name ];        
        inductive_path;                
        compiled_signature;
        compiled_context;
        suffix;        
        arguments;
        prefix = rec_principle_prefix;        
      }
  in  
  Context.add_field ~name ~elem;
  let context = Context.get () in 
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in  
  let _ =    
    implementing_handlers
    |> List.iter (fun constructor_name ->
           let axiom_name, axiom, compiled_signature =
             Codegen.compile_computational_axiom_signature
               ~ctx:parameters ~constructor_name ~inductive
               ~recursor_name:name ~prefix:(Some rec_principle_prefix)
           in
           let elem = 
              LinkageElem.ComputationalAxiom
                { name = axiom_name; axiom; compiled_context; compiled_signature }
           in
           Context.add_field ~name:axiom_name ~elem)
  in  
  (* inherited_handlers = handlers - implementing_handlers *)
  let inherited_handlers =
    let list_difference list1 list2 =
      List.filter (fun x -> not (List.mem x list2)) list1
    in
    list_difference handlers implementing_handlers
  in
  (* Force the inheritance of computational axioms *)
  let _ =
    let recursor_name = name in
    inherited_handlers    
    |> List.iter (fun constructor_name ->
           let name = Naming.computational_axiom_name ~constructor_name ~recursor_name in
           Inheritance.inherit_name ~name)
  in 
  
  Ctx.clear ()

let open_recursion
    ~(name : Names.Id.t)
    ~(inductive_path : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) ~(suffix : RecKind.t)
    ~(arguments : Names.Id.t list) =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in    
  let motive_expr = Resolver.resolve_constrexpr ~context ~expression:motive in  
  let inductive, recursors, _provenance =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix recursors in
  (* Make the motive a field in the family:  *)
  let motive_name = Naming.motive_of name in
  let () = Definition.add_definition ~name:motive_name motive_expr in
  let context = Context.get () in  
  let handler_types =
    Termutils.handler_type_for_recursion ~name ~inductive_path ~recursor     
  in  
  let rec_principle_prefix =
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in
  let implementing_handlers = List.map fst handler_types in
  let recursion_ctx =
    Ctx.
      {        
        defined_handlers = [];
        implementing_handlers;
        suffix;
        inductive_path;
        handler_types;        
        name;        
        inductive;
        arguments;
        rec_principle_prefix;        
      }
  in
  Ctx.update recursion_ctx

let open_recursion_extension ~name =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let linkage = Context.family_linkage context in
  let elem = Inheritance.inherit_element ~field:name ~linkage ~context in
  let inductive_path, inherited_handlers, suffix, arguments =
    match elem with
    | None -> Errors.fail ~info:"There is no such FRecursion in a base family"
    | Some
        (RecursorDefinition
          { inductive_path; suffix; handlers; arguments; _ }) ->
        (inductive_path, handlers, suffix, arguments)
    | _ -> Errors.fail ~info:"Expected to inherit an FRecrusion"
  in    
  let inductive, recursors, _provenance =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix recursors in  
  let handler_types =
    Termutils.handler_type_for_recursion ~name ~inductive_path ~recursor     
  in
  let implementing_handlers =
    let inside x l = List.exists (fun k -> Names.Id.equal k x) l in    
    handler_types |> List.filter_map (fun (x, _) -> if not (inside x inherited_handlers) then Some x else None)
  in
  let rec_principle_prefix =
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in
  let recursion_ctx =
    Ctx.
    {
        defined_handlers = inherited_handlers;
        implementing_handlers;
        suffix;
        handler_types;        
        name;        
        inductive;
        inductive_path;
        arguments;        
        rec_principle_prefix;
      }
  in
  Ctx.update recursion_ctx

let extend_argumets_with_inductive_case
    ~(recursor : Names.Id.t)
    ~(constructor : Names.Id.t) ~(arguments : Names.Id.t list)
    ~(inductive : VernacInductive.t) =
  let types =
    Termutils.flatten_inductive_constructor_type ~inductive ~constructor
  in
  (* Give a good error message for this, e.g as user to fallback
      to the regular syntax if we cannot infer handlers *)
  let result =
    match List.combine arguments types with
    | result -> result
    | exception Invalid_argument _ ->
        let name = Names.Id.to_string constructor in
        let types_len = List.length types in
        let arg_len = List.length arguments in
        let info =
          Printf.sprintf
            "%s exptects %d arguments,  \n\
            \                         but you provided %d" name types_len
            arg_len
        in
        Errors.fail ~info
  in
  result
  |> List.concat_map (fun (arg, ty) ->
         let r = Names.Id.to_string recursor ^ "_" ^ Names.Id.to_string arg in
         let r = Names.Id.of_string r in
         match ty with None -> [ arg ] | Some _ -> [ arg; r ])

(* Given a recursor name `r` and an argument `n`
   replace the expression r n (i.e r applied to n) with the
   variable r_n *)
let replace_recursor ~(recursor : Names.Id.t) (c : Constrexpr.constr_expr) =
  let recursor_qualid = Libnames.qualid_of_ident recursor in
  let rec aux _ (c : Constrexpr.constr_expr) =
    match c.v with
    | CApp (f, args) -> (
        match f.v with
        | CRef (ref_name, _) when ref_name.v = recursor_qualid.v -> (
            match args with
            | ({ v = CRef (n, _); _ }, _) :: args ->
                let name = n |> Naming.path_to_list |> List.hd in
                let r =
                  Names.Id.to_string recursor ^ "_" ^ Names.Id.to_string name
                in
                let r = Libnames.qualid_of_string r in
                let r = Constrexpr_ops.mkRefC r in
                Constrexpr_ops.mkAppC (r, List.map fst args)
            | _ ->
                Constrexpr_ops.map_constr_expr_with_binders
                  (fun _ _ -> ())
                  aux () c)
        | _ ->
            Constrexpr_ops.map_constr_expr_with_binders (fun _ _ -> ()) aux () c
        )
    | _ -> Constrexpr_ops.map_constr_expr_with_binders (fun _ _ -> ()) aux () c
  in
  aux () c

let add_handler ~name ~arguments ~handler =
  let recursion_ctx = Ctx.get () in
  let context = Context.get () in
  let handler = Resolver.resolve_constrexpr ~context ~expression:handler in
  match List.assoc_opt name recursion_ctx.handler_types with
  | None ->
      let names =
        recursion_ctx.handler_types |> List.map fst
        |> List.map Names.Id.to_string
        |> String.concat ", "
      in
      let info =
        Printf.sprintf "Unbound constructor %s. Avaiable constructors are %s"
          (Names.Id.to_string name) names
      in
      Errors.fail ~info
  | Some ty ->
      let case_name =
        Naming.handler_name ~recursor:recursion_ctx.name ~case:name
      in
      let handler =
        match arguments with
        | None ->
            let handler =
              replace_recursor ~recursor:recursion_ctx.name handler
            in
            let handler = Termutils.mk_lambda recursion_ctx.arguments handler in
            handler
        | Some arguments ->
            let arguments =
              extend_argumets_with_inductive_case ~recursor:recursion_ctx.name
                ~constructor:name ~arguments ~inductive:recursion_ctx.inductive
            in
            let handler =
              replace_recursor ~recursor:recursion_ctx.name handler
            in
            let handler = Termutils.mk_lambda recursion_ctx.arguments handler in
            Termutils.mk_lambda arguments handler
      in
      let () = Definition.add_definition ~name:case_name ~body_type:ty handler in      
      Ctx.add_handler name 

let extract = function
  | [] -> None (* Empty list case *)
  | [ _ ] -> None (* Single element list case *)
  | x :: xs ->
      let rec last_and_rest = function
        | [] ->
            failwith
              "This case should never happen due to previous pattern matching"
        | [ last ] -> (last, [])
        | y :: ys ->
            let last, rest = last_and_rest ys in
            (last, y :: rest)
      in
      let last, middle = last_and_rest xs in
      Some (x, last, middle)

let get_identifier (e : Constrexpr.constr_expr) =
  match e.v with
  | Constrexpr.CRef (name, _) -> name
  | _ -> Errors.fail ~info:"Expected an identifier"

let infer_inductive_suffix (i : VernacInductive.t) : RecKind.t =
  let open Constrexpr in
  let open Glob_term in
  let inductive_expr, _ = i |> List.hd in
  let (_, sort), _ = inductive_expr |> VernacInductive.extract_type_and_cstrs in
  let sort = Option.map (fun (e : Constrexpr.constr_expr) -> e.v) sort in
  match sort with
  | Some (CSort (UNamed (_, l))) -> (
      let sort_name, _ = l |> List.hd in
      (* Naive inference *)
      match sort_name with
      | CProp | CSProp -> RecKind.Ind
      | CSet -> RecKind.Rec
      | CType _ -> RecKind.Rect
      | CRawType _ -> RecKind.Ind)
  | _ -> RecKind.Rec

let elegant name (args : (Names.Id.t * Constrexpr.constr_expr) list) =
  let first, (_, last), middle =
    match extract args with
    | Some x -> x
    | None -> Errors.fail ~info:"Expected a list with at least two items"
  in
  let inductive_name = first |> snd |> get_identifier in
  let body =
    Termutils.lambda_to_prod (Termutils.mk_lambda_with_type middle last)
  in
  let motive = Termutils.mk_lambda_with_type [ first ] body in
  let context = Context.get () in
  let inductive, _, _ =
    Context.lookup_inductive_for_recursion ~name:inductive_name context
  in
  let suffix = infer_inductive_suffix inductive in
  open_recursion ~name ~inductive_path:inductive_name ~motive ~suffix
    ~arguments:(List.map fst middle)
