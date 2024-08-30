(* Allow vanilla Coq definitions to be used
   inside a family *)
open Env
open Types
module DB = Backend.Declare

(* Private store *)
module Ctx = struct
  type t = {
    name : Names.Id.t;
    compiled_impl : CompiledModule.t;
    compiled_context : CompiledModuleType.t;
  }

  let store = Summary.ref ~name:"MetaDataCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no metadata context open"
    | Some store -> store

  let clear () = store := None
  let update data = store := Some data
end

let open_metadata name =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let module_name = Naming.fresh_name ~prefix:"MetaData" in
  let compiled_impl = DB.start_module module_name parameters in
  let ctx = Ctx.{ name; compiled_impl; compiled_context } in
  Ctx.update ctx

let close_metadata () =
  let Ctx.{ name; compiled_impl; compiled_context } = Ctx.get () in
  let _ = DB.end_module () in
  let elem =
    LinkageElem.MetaDataSection { name; compiled_impl; compiled_context }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
