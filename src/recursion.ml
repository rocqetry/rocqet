open Types
open Env

(* Private store *)
module Ctx = struct
  type t = {
    handler_types : (Names.Id.t * Constrexpr.constr_expr) list;
    (* The name of the handlers that were supposed to be implemented *)
    implementing_handlers : Names.Id.t list;
    (* The handlers actually implemented or inherited *)
    defined_handlers : Names.Id.t list;
    names : Names.Id.t list;
    inductive : VernacInductive.t;
    suffix : RecKind.t;
    (* the name of the arguments to this FRecursion *)
    arguments : Names.Id.t list;
    inductive_paths : Libnames.qualid list;
    rec_principle_prefix : Libnames.qualid;
  }

  let store = Summary.ref ~name:"RecursionCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no recursion context open"
    | Some store -> store

  let clear () = store := None
  let update recursion_data = store := Some recursion_data

  let add_handler name =
    let ctx = get () in
    let ctx = { ctx with defined_handlers = name :: ctx.defined_handlers } in
    update ctx
end

let close_recursion () =
  let Ctx.
        {
          names;
          inductive;
          suffix;
          defined_handlers;
          arguments;
          inductive_paths;
          rec_principle_prefix;
          implementing_handlers;
          _;
        } =
    Ctx.get ()
  in
  (* let inductive_name = inductive_path |> Naming.extract_path_base in*)
  let _ = Checks.check_exhaustive ~names ~inductive ~inductive_paths ~handlers:defined_handlers in
  (* We use this becuase the handlers have to be in the right order *)
  let inductive_names =
    inductive_paths
    |> List.map Naming.extract_path_base
  in
  let handlers =     
    inductive_names
    |> List.map (fun inductive_name ->
       let handlers = 
         inductive
         |> VernacInductive.create_inductive_constructor_map
         |> Names.Id.Map.find inductive_name
       in
       (inductive_name, handlers))
  in
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let family = context |> Context.family_name |> Names.Id.to_string in
  let module_name =
    let name = Nameops.add_suffix (Nameops.add_prefix family (Naming.concat_names names)) "Ctx" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature ~names
      ~ctx:parameters ~family_name:(Naming.concat_names names)
  in
  let elem =
    LinkageElem.RecursorDefinition
      {
        handlers;
        names;
        inductive_paths;
        compiled_signature;
        compiled_context;
        suffix;
        arguments;
        prefix = rec_principle_prefix;
        default_ctx_params;
      }
  in  
  Context.add_field ~name:(List.hd names) ~elem;    
  let recursor_names =
    List.combine inductive_names names
    |> Names.Id.Map.of_list
  in 
  let _ =
    implementing_handlers
    |> List.iter (fun constructor_name ->
           let context = Context.get () in
           let compiled_context, parameters =
             Codegen.compile_linkage_context ~field_name:module_name context
           in
           let axiom_name, axiom, compiled_signature =
             Codegen.compile_computational_axiom_signature ~ctx:parameters
               ~constructor_name ~inductive ~inductive_paths ~recursor_names
               ~prefix:(Some rec_principle_prefix)
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
           Context.add_field ~name:axiom_name ~elem)
  in
  (* inherited_handlers = handlers - implementing_handlers *)
  let handlers = handlers |> List.concat_map snd in 
  let inherited_handlers =
    let list_difference list1 list2 =
      List.filter (fun x -> not (List.mem x list2)) list1
    in
    list_difference handlers implementing_handlers
  in  
  (* Force the inheritance of computational axioms *)
  let _ =    
    inherited_handlers
    |> List.iter (fun constructor_name ->
           let name =
             Naming.computational_axiom_name ~constructor_name ~recursor_names:names
           in
           Inheritance.inherit_name ~name)
  in

  Ctx.clear ()

let open_recursion 
    ~(args : Frec_arg.t list)
    ~(suffix : RecKind.t)
    ~(arguments : Names.Id.t list) =
  let rec split3 xs =
    match xs with
    | [] -> [], [], []
    | (a, b, c) :: xs ->
       let (as', bs, cs) = split3 xs in
       (a :: as', b :: bs, c :: cs)
  in 

  let names, inductive_paths, motives =
    args
    |> List.map (fun Frec_arg.{ name; inductive; motive } -> name, inductive, motive)
    |> split3
  in 
  
  names |> List.iter (fun name -> Inheritance.inherit_dependencies ~prefix:name);
  let context = Context.get () in
  
  let motive_exprs = motives |> List.map (fun motive -> Resolver.resolve_constrexpr ~context ~expression:motive) in
  let inductive_path = List.hd inductive_paths in
  let inductive, recursors, _provenance =    
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix recursors in
  (* Make the motive a field in the family:  *)
  let motive_names = names |> List.map (fun name -> Naming.motive_of name) in  
  let () =
    List.iter2 (fun motive_name motive_expr -> Definition.add_definition ~name:motive_name motive_expr)
      motive_names motive_exprs 
  in
  let context = Context.get () in
  let handler_types =
    Termutils.handler_type_for_recursion ~names ~inductive_paths ~recursor
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
        inductive_paths;
        handler_types;
        names;
        inductive;
        arguments;
        rec_principle_prefix;
      }
  in
  Ctx.update recursion_ctx

let open_recursion_extension ~names =
  names |> List.iter (fun name -> Inheritance.inherit_dependencies ~prefix:name);
  let context = Context.get () in
  let elem =
    let name = List.hd names in
    Inheritance.lookup_field_in_base ~field:name ~context
  in
  let inductive_paths, inherited_handlers, suffix, arguments =
    match elem with
    | None -> Errors.fail ~info:"There is no such FRecursion in a base family"
    | Some
        (RecursorDefinition { inductive_paths; suffix; handlers; arguments; _ })
      ->
        (inductive_paths, handlers, suffix, arguments)
    | _ -> Errors.fail ~info:"Expected to inherit an FRecrusion"
  in
  let inductive, recursors, _provenance =
    let inductive_path = List.hd inductive_paths in
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix recursors in
  let handler_types =
    Termutils.handler_type_for_recursion ~names ~inductive_paths ~recursor
  in
  let inherited_handlers = inherited_handlers |> List.concat_map snd in
  let implementing_handlers =
    let inside x l = List.exists (fun k -> Names.Id.equal k x) l in
    handler_types
    |> List.filter_map (fun (x, _) ->
           if not (inside x inherited_handlers) then Some x else None)
  in
  let rec_principle_prefix =
    let inductive_path = List.hd inductive_paths in
    Codegen.calculate_rec_principle_prefix ~inductive_path ~context
  in
  let recursion_ctx =
    Ctx.
      {
        defined_handlers = inherited_handlers;
        implementing_handlers;
        suffix;
        handler_types;
        names;
        inductive;
        inductive_paths;
        arguments;
        rec_principle_prefix;
      }
  in
  Ctx.update recursion_ctx

let extend_argumets_with_inductive_case
    ~(inductive_names: Names.Id.t list)
    ~(recursors : Names.Id.t list)
    ~(constructor : Names.Id.t) ~(arguments : Names.Id.t list)
    ~(inductive : VernacInductive.t) =  
  let types =
    Termutils.flatten_inductive_constructor_type ~inductive_names ~inductive ~constructor
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
            "%s exptects %d arguments, but you provided %d" name types_len
            arg_len
        in
        Errors.fail ~info
  in
  result
  |> List.concat_map (fun (arg, ty) ->         
         match ty with
         | None -> [ arg ]
         | Some inductive_name ->
            let recursor = List.combine inductive_names recursors |> List.assoc inductive_name in
            let r = Names.Id.to_string recursor ^ "_" ^ Names.Id.to_string arg in
            let r = Names.Id.of_string r in
            [ arg; r ])

(* Given a recursor name `r` and an argument `n`
   replace the expression r n (i.e r applied to n) with the
   variable r_n *)
let replace_recursor ~(recursors : Names.Id.t list) (c : Constrexpr.constr_expr) =
  let recursor_qualids = recursors |> List.map (fun recursor -> Libnames.qualid_of_ident recursor) in
  let is_recursor (name: Libnames.qualid) =
    recursor_qualids
    |> List.exists (fun (recursor: Libnames.qualid) -> recursor.v = name.v)
  in 
  let rec aux _ (c : Constrexpr.constr_expr) =
    match c.v with
    | CApp (f, args) -> (
        match f.v with
        | CRef (ref_name, _) when is_recursor ref_name -> (
            match args with
            | ({ v = CRef (n, _); _ }, _) :: args ->
               let name = n |> Naming.path_to_list |> List.hd in
               let recursor = Naming.extract_path_base ref_name in 
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
        Naming.handler_name ~recursors:recursion_ctx.names ~case:name
      in
      let handler =
        match arguments with
        | None ->
            let handler =
              replace_recursor ~recursors:recursion_ctx.names handler
            in
            let handler = Termutils.mk_lambda recursion_ctx.arguments handler in
            handler
        | Some arguments ->
           let inductive_names = recursion_ctx.inductive_paths |> List.map Naming.extract_path_base in
           let arguments =
              extend_argumets_with_inductive_case
                ~inductive_names
                ~recursors:recursion_ctx.names
                ~constructor:name ~arguments ~inductive:recursion_ctx.inductive
           in
           let handler =
             replace_recursor ~recursors:recursion_ctx.names handler
           in
           let handler = Termutils.mk_lambda recursion_ctx.arguments handler in
           Termutils.mk_lambda arguments handler
      in
      let () =
        Definition.add_definition ~name:case_name ~body_type:ty handler
      in
      Ctx.add_handler name

let add_wildcard_handler ~handler = 
  let list_difference list1 list2 =
    List.filter
      (fun name -> list2 |> List.exists (Names.Id.equal name) |> not)
      list1
  in
  
  let Ctx.{ inductive; inductive_paths; implementing_handlers; defined_handlers; _ } = Ctx.get () in  
  let inductive_names = inductive_paths |> List.map Naming.extract_path_base in    
  let rest_handlers = list_difference implementing_handlers defined_handlers in 
  
  let cases = 
    rest_handlers 
    |> List.map (fun constructor -> 
       let types =
         Termutils.flatten_inductive_constructor_type ~inductive_names ~inductive ~constructor
         |> List.concat_map (function Some x -> [Some x; Some x] | None -> [None])
       in
       constructor, types |> List.map (fun _ -> Naming.fresh_name ~prefix:"arg"))
  in  
  cases 
  |> List.iter (fun (name, args) -> 
       let handler = Termutils.mk_lambda args handler in 
       add_handler ~name ~arguments:None ~handler)

(* Extra utilities/functions to support a nice syntax for FRecursion *)

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
  let args = [ Frec_arg.{ name; inductive = inductive_name; motive }  ] in
  open_recursion ~args ~suffix
    ~arguments:(List.map fst middle)
