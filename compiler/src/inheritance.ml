open Types
open Env
open Bwd

let close_current_inheritance_judgement () =
  let linkage = Context.close () in
  Codegen.compile_linkage linkage;
  Linkages.add linkage

let open_new_inheritance_judgement name = Context.start_linkage name

let open_derived_inheritance_judgement ~base ~derived =
  Context.start_linkage_with_base ~name:derived ~base

let infer_field_inh_kind name =
  let (LinkageCtx.Toplevel linkage) = Context.get () in
  let Linkage.{ base; _ } = linkage in
  match base with
  | None -> FieldInhKind.New
  | Some base -> (
      match Linkages.lookup base.name with
      | None ->
          Errors.fail
            ~info:("Unbound family name " ^ Names.Id.to_string base.name)
      | Some linkage -> (
          let base_field =
            linkage.fields
            |> Bwd.find_opt (fun (found_name, _) ->
                   Names.Id.equal name found_name)
          in
          match base_field with
          | None -> FieldInhKind.New
          | Some (_, elem) -> FieldInhKind.Extend elem))
