open Types
open Env
open Bwd

let close_current_inheritance_judgement () = Context.close ()
  
let open_new_inheritance_judgement name = Context.start_linkage name

let open_derived_inheritance_judgement ~base ~derived =
  Context.start_linkage_with_base ~name:derived ~base

let infer_field_inh_kind name =
  let ctx = Context.get () in  
  let base =
    match Context.further_bound ctx with
    | Some further -> Some further
    | None ->
       match ctx with
       | LinkageCtx.Nested (_, linkage)
       | LinkageCtx.Toplevel linkage -> linkage.base
  in
  match base with
  | None -> FieldInhKind.New
  | Some base ->
     let base_field =
         base.fields
         |> Bwd.find_opt (fun (found_name, _) ->
                   Names.Id.equal name found_name)
     in
     match base_field with
     | None -> FieldInhKind.New
     | Some (_, elem) -> FieldInhKind.Extend elem
