open Types
open Env

(* FLemma *)

module DB = Backend.Declare

(* Private store *)
module Ctx = struct
  type t = {
    name : Names.Id.t;
    compiled_context : CompiledModuleType.t;
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    goal : Constrexpr.constr_expr;
    module_name : Names.Id.t;
  }

  let store = Summary.ref ~name:"LemmaCtx" (None : t option)

  let get () =
    match !store with
    | None -> Errors.fail ~info:"There is no lemma context open"
    | Some store -> store

  let clear () = store := None
  let update data = store := Some data
end

let prepare_proving () =
  let Ctx.{ module_name; parameters; goal; name; _ } = Ctx.get () in
  let _ = DB.start_module module_name parameters in
  let sigma, env = Termutils.global_env () in
  let sigma, internalized_goal = Termutils.internalize env goal sigma in
  let info = Declare.Info.make () in
  let cinfo = Declare.CInfo.make ~name ~typ:internalized_goal () in
  let ongoing_proof = Declare.Proof.start ~info ~cinfo sigma in
  ongoing_proof

let open_flemma name t =
  let context = Context.get () in
  let goal = Resolver.resolve_constrexpr ~context ~expression:t in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let ctx = Ctx.{ name; compiled_context; parameters; goal; module_name } in
  Ctx.update ctx

let close_flemma () =
  let Ctx.{ parameters; goal; name; compiled_context; _ } = Ctx.get () in  
  let default_ctx_params =
    let context = Context.get () in
    context
    |> Context.family_linkage
    |> function { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_impl = DB.end_module () in
  let compiled_signature =
    Codegen.compile_lemma_signature ~name ~ty:goal ~parameters
  in
  let elem =
    LinkageElem.OpaqueFieldDefinition
      { compiled_context; compiled_impl; compiled_signature; default_ctx_params }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
