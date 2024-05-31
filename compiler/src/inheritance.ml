open Types
open Env
open Bwd

let compile_linkage (linkage : Linkage.t) =
  let Linkage.{ name; fields; _ } = linkage in 
  let open Codegen.VernacBackend in
  let open Codegen in
  let rec compile_fields fields (ctx : ModuleTerm.t list) =
    match fields with
    | Bwd.Emp -> return ()
    | Bwd.Snoc (fields, (name, LinkageElem.InductiveDefinition { compiled_impl; _ })) ->
        let* _ = compile_fields fields ctx in
        let module_expr = Termutils.ident_to_module_expr compiled_impl in
        let* _ = include_module ~module_expr in
        return ()
  in
  define_module ~module_name:name ~parameters:[] ~body:(compile_fields fields)
  |> run
  |> ignore

let close_current_inheritance_judgement () =    
  let linkage = Context.close () in
  compile_linkage linkage;
  Linkages.add linkage
  

let open_new_inheritance_judgement name = Context.start_linkage name

let open_derived_inheritance_judgement ~base ~derived =
  Context.start_linkage_with_base ~name:derived ~base  

let infer_field_inh_kind name =
  let (LinkageCtx.Toplevel linkage) = Context.get () in
  let Linkage.{ base; _ } = linkage in 
    match base with 
    | None -> FieldInhKind.New
    | Some base ->
       match Linkages.lookup base.name with
       | None ->
           Errors.fail ~info:("Unbound family name " ^ Names.Id.to_string base.name)
       | Some linkage -> 
        let base_field =
          linkage.fields
          |> Bwd.find_opt (fun (found_name, _) ->
                 Names.Id.equal name found_name)
        in
        match base_field with
        | None -> FieldInhKind.New
        | Some (_, elem) -> FieldInhKind.Extend elem  
