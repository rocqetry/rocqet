open Types
open Env

(* TODO: This module should not know about the Vernac backend *)
module VB = Backend.Vernac

(* We need this becuase for some reason, VB doesn't seem to work
   if modules are not closed immediately(?) *)
module DB = Backend.Declare

(* Private store *)
module Ctx = struct
  type t = {
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    handler_types : (Names.Id.t * Constrexpr.constr_expr) list;
    handler_cases : (Names.Id.t * Constrexpr.constr_expr) list;
    module_name : Names.Id.t;
    compiled_context : CompiledModuleType.t;
    name : Names.Id.t;
    inductive : VernacInductive.t;
    provenance : Linkage.t;
    motive : CompiledModule.t;
    motive_expr : Constrexpr.constr_expr list;
    suffix : RecKind.t;
    arguments : Names.Id.t list;
        (* the name of the arguments to this FRecursion *)
    inductive_path : Libnames.qualid;
    rec_principle_prefix : Libnames.qualid option;
  }

  let store = Summary.ref ~name:"RecursionCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no recursion context open"
    | Some store -> store

  let clear () = store := None
  let update recursion_data = store := Some recursion_data

  let add_handler_case name expr =
    let ctx = get () in
    let ctx = { ctx with handler_cases = (name, expr) :: ctx.handler_cases } in
    update ctx
end

let close_recursion () =
  let Ctx.
        {
          handler_types;
          name;
          inductive;
          suffix;
          compiled_context;
          motive;
          provenance;
          parameters;
          module_name;
          handler_cases;
          motive_expr;
          arguments;
          inductive_path;
          rec_principle_prefix;
          _;
        } =
    Ctx.get ()
  in
  Checks.check_exhaustive ~name ~inductive ~handlers:handler_cases;
  module_name |> ignore;
  let module_name = DB.end_module () in
  let handlers = handler_types |> List.map fst in
  let compiled_impl, computational_axioms =
    Codegen.compile_recursive_definition_implementation ~rec_principle_prefix
      ~inductive ~provenance ~recursor_name:name ~handlers ~suffix
      ~ctx:parameters ~handler_cases:module_name
  in
  let compiled_signature =
    Codegen.compile_recursive_definition_signature ~names:[ name ]
      ~motive_module:motive ~handler_cases:module_name ~ctx:parameters
      ~family_name:name ~computational_behaviour:`Exposed ~computational_axioms
  in
  (* Feedback the defined Computational Axioms *)
  let print_constr_expr expr =
    let sigma, env = Termutils.global_env () in
    Ppconstr.pr_constr_expr env sigma expr
  in
  let print_name name = name |> Names.Id.to_string |> Pp.str in
  let print_single_equation (name, eq) =
    let open Pp in
    print_name name ++ Pp.str " : " ++ print_constr_expr eq
  in
  let _ =
    let open Pp in
    Feedback.msg_info
      (str "Computational Axioms for "
      ++ print_name name
      ++ str " are defined as follows:");
    computational_axioms
    |> List.iter (fun eq -> Feedback.msg_info (print_single_equation eq))
  in
  let elem =
    LinkageElem.RecursorDefinition
      {
        handler_cases;
        names = [ name ];
        inductive;
        inductive_path;
        recursor_module = module_name;
        motive_module = motive;
        motives = motive_expr;
        compiled_signature;
        compiled_impl;
        compiled_context;
        suffix;
        handler_types;
        arguments;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()

let open_recursion ~(name : Names.Id.t) ~(inductive_path : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) ~(suffix : RecKind.t)
    ~(arguments : Names.Id.t list) =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let family = context |> Context.family_name |> Names.Id.to_string in
  let module_name =
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Cases" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in
  let motive_expr = Resolver.resolve_constrexpr ~context ~expression:motive in
  let motive =
    Codegen.compile_motives ~names:[ name ] ~motives:[ motive_expr ]
      ~ctx:parameters ~family_name:name
  in
  let inductive, compiled_recursors, provenance =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let _module_name = DB.start_module module_name parameters in
  VB.run
  @@ Codegen.include_handler_types ~context ~inductive_provenance:provenance
       ~inductive_path ~recursor;
  let applied_motive =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr motive)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let _ = VB.(run (include_module ~module_expr:applied_motive)) in
  let handler_types = Termutils.handler_types_table name recursor in
  let rec_principle_prefix =
    Some
      (Codegen.calculate_rec_principle_prefix ~inductive_path ~context
         ~inductive_provenance:provenance)
  in
  let recursion_ctx =
    Ctx.
      {
        parameters;
        handler_cases = [];
        suffix;
        inductive_path;
        handler_types;
        module_name;
        name;
        compiled_context;
        motive;
        motive_expr = [ motive_expr ];
        inductive;
        provenance;
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
  let inductive_path, motives, handler_cases, suffix, arguments =
    match elem with
    | None -> Errors.fail ~info:"There is no such FRecursion in a base family"
    | Some
        (RecursorDefinition
          { inductive_path; suffix; motives; handler_cases; arguments; _ }) ->
        (inductive_path, motives, handler_cases, suffix, arguments)
    | _ -> Errors.fail ~info:"Expected to inherit an FRecrusion"
  in
  let module_name =
    let family = Names.Id.to_string linkage.name in
    let name = Nameops.add_suffix (Nameops.add_prefix family name) "Cases" in
    let name = Names.Id.to_string name in
    Naming.fresh_name ~prefix:name
  in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:module_name context
  in
  let motive =
    Codegen.compile_motives ~names:[ name ] ~motives ~ctx:parameters
      ~family_name:name
  in
  let inductive, compiled_recursors, provenance =
    Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let handler_types = Termutils.handler_types_table name recursor in
  let compiled_handler_types =
    Codegen.aggregate_handler_types context provenance inductive_path recursor
      parameters
  in
  let recursor_module =
    Codegen.compile_handler_cases ~name ~context ~motive ~handler_cases
      ~handler_types ~compiled_handler_types ~parameters ~provenance ~recursor
  in
  let _module_name = DB.start_module module_name parameters in
  (* PreviousCases module has the handler types *)
  let previous_cases =
    Termutils.apply_module
      ~functor_expr:(Termutils.ident_to_module_expr recursor_module)
      ~arguments:
        (parameters |> List.map fst |> List.map Libnames.qualid_of_ident)
  in
  let _ = VB.(run @@ include_module ~module_expr:previous_cases) in
  let rec_principle_prefix =
    Some
      (Codegen.calculate_rec_principle_prefix ~inductive_path ~context
         ~inductive_provenance:provenance)
  in
  let recursion_ctx =
    Ctx.
      {
        parameters;
        handler_cases;
        suffix;
        handler_types;
        module_name;
        name;
        compiled_context;
        motive;
        motive_expr = motives;
        inductive;
        inductive_path;
        provenance;
        arguments;
        rec_principle_prefix;
      }
  in
  Ctx.update recursion_ctx

let extend_argumets_with_inductive_case ~(recursor : Names.Id.t)
    ~(constructor : Names.Id.t) ~(arguments : Names.Id.t list)
    ~(inductive : VernacInductive.t) =
  (* TODO: We will need all the names for the case of
     mutual recursion *)
  let ind_name =
    VernacInductive.extract_inductive_name inductive |> Libnames.qualid_of_ident
  in
  let constructor_type =
    inductive
    |> List.map (fun (inductive_expr, _) ->
           inductive_expr |> VernacInductive.extract_type_and_cstrs)
    |> List.find_map (fun (_, ctrs) -> List.assoc_opt constructor ctrs)
  in
  let constructor_type =
    match constructor_type with
    | None -> Errors.fail ~info:"Couldn't find constructor"
    | Some c -> c
  in
  let rec unflatten (c : Constrexpr.constr_expr) =
    match c.v with
    | CNotation (_, (_, "_ -> _"), ([ domain; codomain ], _, _, _)) -> (
        match domain.v with
        | Constrexpr.CRef (ty_name, _) -> ty_name.v :: unflatten codomain
        | _ -> Errors.fail ~info:"Expected reference")
    | _ -> []
  in
  let types = unflatten constructor_type in
  Printf.printf "type length : %d\n" (List.length types);
  let result = List.combine arguments types in
  result
  |> List.concat_map (fun (arg, ty) ->
         let r = Names.Id.to_string recursor ^ "_" ^ Names.Id.to_string arg in
         let r = Names.Id.of_string r in
         if ty = ind_name.v then [ arg; r ] else [ arg ])

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
      Ctx.add_handler_case name handler;
      VB.run (VB.define_term ~name:case_name ~ty handler)

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
