open Types
open Env

let add_record_with_defaults ~rd ~inductive ~defaults =
  let context = Context.get () in
  let rd = Resolver.resolve_record ~context ~rd in
  let RecordDecl.{ name; ty; fields } = rd in  
  Inheritance.inherit_dependencies ~prefix:name;    
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in

  (* The record type *)
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let ty = Resolver.resolve_constrexpr ~context ~expression:ty in
  let compiled_signature =
    Codegen.compile_inductive_axiom ~name ~ty ~ctx:parameters
  in
  let family_name = Context.family_name context in
  let constructor_name = Naming.rocqet_record_constructor ~record_name:name ~family_name in
  let elem =
    LinkageElem.RecordDefinition
      {
        rd;
        original = inductive;
        defaults;
        constructor_name;
        compiled_context;
        compiled_signature;
        default_ctx_params;        
      }
  in  
  Context.add_field ~name ~elem;

  
  (* The *introduction* form *)
  let context = Context.get () in  
  let args_type = fields |> List.map snd in
  let record_type =
    let expression = Constrexpr_ops.mkIdentC name in
    Resolver.resolve_constrexpr ~context ~expression
  in 
  let constructor_type =
    Termutils.mk_arrow_ty ~args_type ~ret_type:record_type
  in
  (* Resolve it *)
  let constructor_type = Resolver.resolve_constrexpr ~context ~expression:constructor_type in   
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let compiled_signature =
    Codegen.compile_inductive_axiom ~name:constructor_name ~ty:constructor_type ~ctx:parameters
  in
  let elem =
    LinkageElem.RecordConstrAxiom {
        name = constructor_name;
        record_name = name;
        fields = fields |> List.map fst;
        defaults = [];
        main_constr_name = None;
        compiled_context;
        compiled_signature;
        default_ctx_params
    }
  in
  
  Context.add_field ~name:constructor_name ~elem;

  (* The *elimination* forms *)     
  fields
  |> List.map (fun (field_name, field_type) ->
         field_name, Termutils.mk_arrow_ty ~args_type:[record_type] ~ret_type:field_type)
  |> List.iter (fun (n, t) ->
         let context = Context.get () in
         let compiled_context, parameters =
           Codegen.compile_linkage_context ~field_name:n context
         in
         let compiled_signature =
           Codegen.compile_inductive_axiom ~name:n ~ty:t ~ctx:parameters
         in
         let elem = LinkageElem.InductiveAxiom { compiled_context; compiled_signature; default_ctx_params } in
         Context.add_field ~name:n ~elem
       )

let add_record rd inductive =
  add_record_with_defaults ~rd ~inductive ~defaults:[]
    
let extend_record
      ~(rd: RecordDecl.t)
      ~(inductive: VernacInductive.t)
      ~(defaults: (Names.Id.t * Constrexpr.constr_expr) list) =

  (* 1. Lookup the name in the base context *)
  let context = Context.get () in
  let rd = Resolver.resolve_record ~context ~rd in  
  let RecordDecl.{ name; fields; _ } = rd in
  Inheritance.inherit_dependencies ~prefix:name;
  let base_elem = Inheritance.lookup_field_in_base ~field:name ~context in
  
  (* 2. Ensure the linkage element we extract is a RecordDefinition *)
  let base_rd, base_inductive = 
    match base_elem with
    | None -> Errors.fail ~info:"No base record definition found to extend"
    | Some (LinkageElem.RecordDefinition br) -> (br.rd, br.original)
    | Some _ -> Errors.fail ~info:"Base element is not a RecordDefinition"
  in  
  
  (* 3. Concatenate VernacInductive.t relative to record definition *)
  let new_inductive = VernacInductive.concatenate ~base:base_inductive ~derived:inductive in
  
  (* 4. Concatenate the RecordDecl.t *)
  let new_rd = RecordDecl.{ base_rd with fields = base_rd.fields @ fields } in
    
  (* 5.  Keep track of default values *)
  let defaults =
    defaults
    |> List.map (fun (name, value) ->
        let internal_name_ident = Naming.fresh_name ~prefix:(Names.Id.to_string name) in           
        let internal_name = Libnames.qualid_of_ident internal_name_ident in
        let body_type =
          match List.assoc_opt name rd.fields with
          | None -> Errors.fail ~info:(Printf.sprintf "unbound field: %s" (Names.Id.to_string name))
          | Some ty -> ty 
        in           
        Definition.add_definition ~name:internal_name_ident ~body_type value ;            
        (name, internal_name))
  in
  
  add_record_with_defaults ~rd:new_rd ~inductive:new_inductive ~defaults

let resolve_record_constr (expr : Constrexpr.constr_expr) =
  let context = Context.get () in
  
  let rec transform_expr (expr: Constrexpr.constr_expr) =
    let loc = expr.CAst.loc in
    let open Constrexpr in
    match expr.CAst.v with
    | Constrexpr.CProj (false, (field_qualid, None), [], record_expr) ->
       let open Constrexpr_ops in
       mkAppC (mkRefC field_qualid, [transform_expr record_expr])
    | Constrexpr.CProj _ -> Errors.fail ~info:"Unable to interpret the projection expression"
    | Constrexpr.CRecord fields ->
       let prefix =
         match fields with
         | [] -> None
         | (prefix, _) :: _ ->
            let p = prefix |> Naming.path_to_list |> List.rev |> List.tl |> List.rev in
            if List.is_empty p then None else Some (Naming.list_to_path p)
       in
       let args = List.map (fun (n, _) -> Naming.extract_path_base n) fields in        
       let exprs = List.map (fun (_, e) -> transform_expr e) fields in 
       let record_constructor =
         match Context.lookup_fields ~prefix ~names:args ~context with
         | None ->
            (* We can either error out or just return the expression, untouched, back to Rocq *)
            Errors.fail ~info:"Cannot find a suitable constructor for record literal"
         | Some n -> n 
       in
       let record_constructor = Naming.qualid_point prefix record_constructor in
       let open Constrexpr_ops in
       mkAppC (mkRefC record_constructor, exprs)
    (* Leaf nodes - no recursion needed *)
    | CHole _ | CGenarg _ | CGenargGlob _ | CEvar _ | CPatVar _ | CSort _ | CPrim _ | CRef _ -> 
       expr
    | CApp (f, args) ->
       CAst.make ?loc (CApp (transform_expr f, List.map (fun (e, expl) -> (transform_expr e, expl)) args))
    | CAppExpl (f, args) ->
       CAst.make ?loc (CAppExpl (f, List.map transform_expr args))
    | CProdN (bl, e) ->
       CAst.make ?loc (CProdN (bl, transform_expr e))
    | CLambdaN (bl, e) ->
       CAst.make ?loc (CLambdaN (bl, transform_expr e))
    | CLetIn (name, e1, ty, e2) ->
       CAst.make ?loc (CLetIn (name, transform_expr e1, Option.map transform_expr ty, transform_expr e2))
    | CCases (style, rtn, cases, branches) ->
       let rtn' = Option.map transform_expr rtn in
       let cases' = List.map (fun (e, name, pat) -> (transform_expr e, name, pat)) cases in
       CAst.make ?loc (CCases (style, rtn', cases', branches))
    | CLetTuple (names, rtn, e1, e2) ->
       CAst.make ?loc (CLetTuple (names, (fst rtn, Option.map transform_expr (snd rtn)), transform_expr e1, transform_expr e2))
    | CIf (c, rtn, e1, e2) ->
       CAst.make ?loc (CIf (transform_expr c, (fst rtn, Option.map transform_expr (snd rtn)), transform_expr e1, transform_expr e2))
    | CFix (id, fixes) ->
       let fixes' = List.map (fun (id, order, bl, ty, body) -> 
         (id, order, bl, transform_expr ty, transform_expr body)) fixes in
       CAst.make ?loc (CFix (id, fixes'))
    | CCoFix (id, cofixes) ->
       let cofixes' = List.map (fun (id, bl, ty, body) -> 
         (id, bl, transform_expr ty, transform_expr body)) cofixes in
       CAst.make ?loc (CCoFix (id, cofixes'))
    | CCast (e0, cty, e1) ->       
       CAst.make ?loc (CCast (transform_expr e0, cty, transform_expr e1))
    
    | CGeneralization (kind, e) ->
       CAst.make ?loc (CGeneralization (kind, transform_expr e))
    | CDelimiters (scope, b, e) ->
       CAst.make ?loc (CDelimiters (scope, b, transform_expr e))
    | CNotation (scope_opt, notation, (constrs, constr_lists, binders, binder_lists)) ->
       let constrs' = List.map transform_expr constrs in
       let constr_lists' = List.map (List.map transform_expr) constr_lists in       
       CAst.make ?loc (CNotation (scope_opt, notation, (constrs', constr_lists', binders, binder_lists)))       
    | CArray (u, tys, def, ty) ->
       let tys' = Array.map transform_expr tys in
       let def' = transform_expr def in
       let ty' = transform_expr ty in
       CAst.make ?loc (CArray (u, tys', def', ty'))
  in
  transform_expr expr
    
