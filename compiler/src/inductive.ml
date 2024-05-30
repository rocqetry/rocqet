open Types
open Env

(* Contains information on how to compile inductive types *)

(* Compile a context *)
let compile_context ~ctx ~module_name =
  let (FamilyContext.Toplevel (name, ty)) = ctx in
  let FamilyType.{ body; _ } = ty in
  let open Codegen.VernacBackend in
  let module_name_ctx = Codegen.fresh_name ~prefix:(Nameops.add_suffix module_name "Ctx" |> Names.Id.to_string) in
  match body with
  | [] ->
      define_moduletype ~module_name:module_name_ctx ~parameters:[]
        ~body:(fun _arguments -> return ())
      |> run
  | (_, FamilyTypeElem.FInductive { compiled_signature; compiled_ctx; _ }) :: _
    ->
      define_moduletype ~module_name:module_name_ctx ~parameters:[]
        ~body:(fun _arguments ->
          let* () =
            include_module
              ~module_expr:(Termutils.ident_to_module_expr compiled_ctx)
          in
          let* () =
            include_module
              ~module_expr:(Termutils.ident_to_module_expr compiled_signature)
          in
          return ())
      |> run

(* Retrn the name of the compiled family field and return its compiled context's name *)
let inductive_to_famtype ~(ind_def : VernacInductive.t)
    ~(ctx : CompiledModuleType.t) ~family_name : CompiledModuleType.t =
  let ind_cstrs =
    ind_def
    |> List.map (fun ind ->
           ind |> fst |> VernacInductive.extract_type_and_cstrs)
    |> List.map (fun ((ind_name, ty), cstrs) ->
           ((ind_name, Option.get ty), cstrs))
  in
  let type_decls = ind_cstrs |> List.map fst in
  let original_ind_name = type_decls |> List.hd |> fst in
  let module_name =
    Codegen.fresh_name ~prefix:(original_ind_name |> Names.Id.to_string)
  in
  let constr_decls = List.concat_map snd ind_cstrs in
  let module Backend = Codegen.VernacBackend in
  let declare_typedecls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) type_decls
  in
  let declare_csts_decls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) constr_decls
  in
  let all_decls = declare_typedecls @ declare_csts_decls in
  let parameters =
    [
      ( Nameops.add_prefix "self__" family_name,
        Termutils.ident_to_module_expr ctx );
    ]
  in
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name ~parameters ~body:(fun _ ->
         let* () = flatmap all_decls in
         return ())

let inductive_to_famtype_for_extension
    ~(compiled_base : CompiledModuleType.t)    
    ~(ind_def : VernacInductive.t)
    ~(ctx : CompiledModuleType.t)
    ~family_name : CompiledModuleType.t =
  let ind_cstrs =
    ind_def
    |> List.map (fun ind ->
           ind |> fst |> VernacInductive.extract_type_and_cstrs)
    |> List.map (fun ((ind_name, ty), cstrs) ->
           ((ind_name, Option.get ty), cstrs))
  in
  let type_decls = ind_cstrs |> List.map fst in
  let original_ind_name = type_decls |> List.hd |> fst in
  let module_name =
    Codegen.fresh_name ~prefix:(original_ind_name |> Names.Id.to_string)
  in
  let constr_decls = List.concat_map snd ind_cstrs in
  let module Backend = Codegen.VernacBackend in  
  let declare_csts_decls =
    List.map (fun (name, ty) -> Backend.postulate_axiom ~name ~ty) constr_decls
  in
  let all_decls = declare_csts_decls in
  let self__family_name = Nameops.add_prefix "self__" family_name in
  let functor_expr = Termutils.ident_to_module_expr compiled_base in
  let arguments = [Libnames.qualid_of_ident self__family_name] in 
  let base_expr = Termutils.apply_module ~functor_expr ~arguments in 
  let parameters =
    [
      ( self__family_name,
        Termutils.ident_to_module_expr ctx );
    ]
  in
  let open Backend in
  Backend.run
  @@ Backend.define_moduletype ~module_name ~parameters ~body:(fun _ ->
         (* Apply module *)
         let* () = include_module ~module_expr:base_expr in
         let* () = flatmap all_decls in
         return ())

(* This is the instantiation of an inductive type and it's recursors *)
let inductive_to_famterm_and_recursor_type ~(ind_def : VernacInductive.t)
    ~(ctx : CompiledModuleType.t) ~family_name : CompiledModule.t =
  let all_names_with_type =
    ind_def
    |> List.map (fun (ind_expr, _) ->
           VernacInductive.extract_type_and_cstrs ind_expr)
  in
  let original_type_name =
    all_names_with_type
    |> List.map (fun ((ind_name, _), _) -> ind_name)
    |> List.hd
  in
  (* Generate a definition mapping of the inductive type and
     return the new inductive definition and the export of the correct names *)
  let modified_indcstrs, alias_all_name_term_type_decl =
    VernacInductive.definition_mapping ~prefix:"__internal_" ind_def
  in
  let module_name =
    Codegen.fresh_name ~prefix:(original_type_name |> Names.Id.to_string)
  in
  let open Codegen.VernacBackend in
  let parameters =
    [
      ( Nameops.add_prefix "self__" family_name,
        Termutils.ident_to_module_expr ctx );
    ]
  in
  let module_name =
    run
    @@ define_module ~module_name ~parameters ~body:(fun _ ->
           let* () = define_inductive modified_indcstrs in
           (* Some stuff with the recursors here *)
           let alias_all =
             List.map
               (fun (original_name, new_name, ty) ->
                 define_term ~name:original_name ~expr:new_name ~ty)
               alias_all_name_term_type_decl
           in
           let* _ = flatmap alias_all in
           return ())
  in
  module_name

let compile_inductive_definition ~(judgement : InhJudgement.t)
    ~(ind_def_name : Names.Id.t) ~(ind_def : VernacInductive.t)
    ~(ctx : FamilyContext.t) : InhJudgement.t =
  let InhJudgement.{ derived; body; _ } = judgement in
  let constructor_names = VernacInductive.extract_all_ident ind_def in
  let compiled_ctx = compile_context ~ctx ~module_name:ind_def_name in
  let family_name = derived.name in
  let compiled_signature =
    inductive_to_famtype ~ind_def ~ctx:compiled_ctx ~family_name
  in
  let compiled_impl =
    inductive_to_famterm_and_recursor_type ~ind_def ~ctx:compiled_ctx
      ~family_name
  in
  let ctx_elem =
    FamilyTypeElem.FInductive
      {
        original_inductive = ind_def;
        constructor_names;
        compiled_signature;
        compiled_impl;
        compiled_ctx;
      }
  in
  let derived_with_elem =
    FamilyType.extend ~name:ind_def_name ~elem:ctx_elem derived
  in
  let inh_elem = InhElement.CInhNew compiled_impl in
  {
    judgement with
    derived = derived_with_elem;
    body = (ind_def_name, inh_elem) :: body;
  }

let declare_inductive_definition ~ind_def_name ~ind_def =
  let ctx = InhJudgements.current_output_ctx () in
  match InhJudgements.pop () with
  | None -> Errors.fail ~info:"Expected a non empty inh context"
  | Some (family_name, judgement) ->
      let judgement =
        compile_inductive_definition ~judgement ~ind_def_name ~ind_def ~ctx
      in
      InhJudgements.push ~name:family_name ~judgement

let check_extended_inductive_compatible
      ~(base: VernacInductive.t)
      ~(derived: VernacInductive.t) ~base_name ~derived_name : VernacInductive.t =
  let base = base |> List.hd in (* No mutual inductive types *)
  let derived = derived |> List.hd in (* No mutual indcutive types *)
  
  let (_, _, _, oldcstrs) = fst base in 
  let (a, b, c, newcstrs) = fst derived in 
  let childcstrs = 
      match oldcstrs, newcstrs with 
      | Vernacexpr.Constructors a, Vernacexpr.Constructors b ->
         let base_name = Nameops.add_prefix "self__" base_name in
         let derived_name = Nameops.add_prefix "self__" derived_name in 
         let a = Naming.rename_ind_constructors a ~base_name ~derived_name in
        Vernacexpr.Constructors (a @ b)
      | _, _ -> Errors.fail ~info:"Record types are not yet supported"
  in
  let child_ind = (a, b, c, childcstrs) in 
  let child_ind_def = [(child_ind, [])] in
  child_ind_def
  

let extend_inductive_definition
      ~ind_def_name
      ~ind_def
      ~inherited_elem =  
  (* Compile deps *)
  let (name, judgement) = InhJudgements.peek () |> Option.get in
  let InhJudgement.{ base;  derived; _ } = judgement in
  let rec calculate_dependencies fields =
    match fields with
    | [] -> []
    | (found_name, _) :: fields when Names.Id.equal found_name ind_def_name ->
       (* Remove the fields in the that have already been extended by the derived family *)
       fields
       |> List.filter (fun (name, _) ->
              derived.body
              |> List.map fst
              |> List.exists (Names.Id.equal name)
              |> not)
    | _ :: fields -> calculate_dependencies fields 
  in  
  let deps = calculate_dependencies base.body in
  base.body |> List.iter (fun (name, _) -> Printf.printf "Base: %s\n" (Names.Id.to_string name));
  deps |> List.iter (fun (name, _) -> Printf.printf "Dep: %s\n" (Names.Id.to_string name));
  let derived = { derived with body = deps @ derived.body } in
  let inhs = deps |> List.map (fun (name, _) -> (name, InhElement.CInhInherit)) in
  let body = inhs @ judgement.body in 
  InhJudgements.push ~name ~judgement:{ judgement with derived; body; };  
  match inherited_elem with
  | FamilyTypeElem.FInductive { original_inductive; compiled_signature; _ } ->
     let ctx = InhJudgements.current_output_ctx () in
     let (_, judgement) = InhJudgements.pop () |> Option.get in
     let InhJudgement.{ base; derived; _ } = judgement in     
     let complete_ind_def =
       check_extended_inductive_compatible
         ~base:original_inductive
         ~derived:ind_def
         ~base_name:base.name
         ~derived_name:derived.name
     in
     let inh_elem = InhElement.CInhExtendInd { parent = original_inductive; increment = ind_def } in
     let constructor_names = VernacInductive.extract_all_ident complete_ind_def in     
     let compiled_ctx = compile_context ~ctx ~module_name:ind_def_name in
     let compiled_signature =
       inductive_to_famtype_for_extension
         ~ind_def ~ctx:compiled_ctx ~family_name:derived.name ~compiled_base:compiled_signature
     in
     let compiled_impl =
        inductive_to_famterm_and_recursor_type ~ind_def:complete_ind_def ~ctx:compiled_ctx
         ~family_name:derived.name
     in
     let ctx_elem =
    FamilyTypeElem.FInductive
      {
        original_inductive = complete_ind_def;
        constructor_names;
        compiled_signature;
        compiled_impl;
        compiled_ctx;
      }
     in
    let derived_with_elem =
      FamilyType.extend ~name:ind_def_name ~elem:ctx_elem derived
    in
    let judgement =
      {
         judgement with
         derived = derived_with_elem;
         body = (ind_def_name, inh_elem) :: judgement.body;
      }
    in 
     InhJudgements.push ~name:base.name ~judgement     
  

let add_inductive_definition ind_def =
  InhJudgements.ensure_open_judgememt ();
  let all_names = VernacInductive.extract_all_ident ind_def in
  let ind_def_name = List.hd all_names in
  (* Type checking of the inductive definition should happen here? *)
  (* let _ = inductive_to_famtype ([ind_def], current_ctx) in *)
  (* let _ = inductive_to_famterm_and_recursor_type ([ind_def], current_ctx) in *)
  match Inheritance.infer_field_inh_kind ind_def_name with
  | FieldInhKind.New -> declare_inductive_definition ~ind_def_name ~ind_def
  | FieldInhKind.Extend inherited_elem ->
      extend_inductive_definition ~ind_def_name ~ind_def ~inherited_elem
