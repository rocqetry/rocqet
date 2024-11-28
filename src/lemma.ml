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
    module_name : Names.Id.t;
    type_name : Names.Id.t;
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
  let Ctx.{ module_name; parameters; type_name; name; _ } = Ctx.get () in
  let goal =
    let context = Context.get () in
    let expression = Constrexpr_ops.mkIdentC type_name in
    Resolver.resolve_constrexpr ~context ~expression
  in
  let _ = DB.start_module module_name parameters in
  let sigma, env = Termutils.global_env () in
  let sigma, internalized_goal = Termutils.internalize env goal sigma in
  let info = Declare.Info.make () in
  let cinfo = Declare.CInfo.make ~name ~typ:internalized_goal () in
  let ongoing_proof = Declare.Proof.start ~info ~cinfo sigma in
  let open Ltac_plugin in
  (* unfold LemmaTy *)
  let starting_operation =
    let self__motive =
      Resolver.resolve_qualid ~context:(Context.get ())
        ~qualid:(Libnames.qualid_of_ident type_name)
    in
    let self__motive_tactic = Tacexpr.TacCall (CAst.make (self__motive, [])) in
    let unfold_self_motive =
      CAst.make
        (Tacexpr.TacArg
           (Tacexpr.TacCall
              (CAst.make
                 ( Libnames.qualid_of_ident (Names.Id.of_string "__funfold"),
                   [ self__motive_tactic ] ))))
    in
    Tacinterp.interp unfold_self_motive
  in
  let ongoing_proof, _ = Declare.Proof.by starting_operation ongoing_proof in
  ongoing_proof

let open_flemma name t =
  Inheritance.inherit_dependencies ~prefix:name;
  let type_name = Naming.fresh_name ~prefix:"LemmaTy" in
  let _ = Definition.add_definition ~name:type_name t in
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let ctx =
    Ctx.{ name; compiled_context; parameters; type_name; module_name }
  in
  Ctx.update ctx

let override name =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let base_elem = Inheritance.lookup_field_in_base ~field:name ~context in
  let type_name =
    match base_elem with
    | None -> Errors.fail ~info:"Can't override. No such element in base"
    | Some (LinkageElem.OpaqueFieldDefinition { type_name; _ }) -> type_name
    | Some _ ->
        Errors.fail ~info:"Can't override. Only Opaque fields can be overriden"
  in
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let module_name = Naming.fresh_name ~prefix:(Names.Id.to_string name) in
  let ctx =
    Ctx.{ name; compiled_context; parameters; type_name; module_name }
  in
  Ctx.update ctx

let close_flemma () =
  let Ctx.{ parameters; type_name; name; compiled_context; _ } = Ctx.get () in
  let context = Context.get () in
  let default_ctx_params =
    context |> Context.family_linkage |> function
    | { default_ctx_params; _ } -> default_ctx_params
  in
  let compiled_impl = DB.end_module () in
  let goal =
    let expression = Constrexpr_ops.mkIdentC type_name in
    Resolver.resolve_constrexpr ~context ~expression
  in
  let compiled_signature =
    Codegen.compile_lemma_signature ~name ~ty:goal ~parameters
  in
  let elem =
    LinkageElem.OpaqueFieldDefinition
      {
        type_name;
        compiled_context;
        compiled_impl;
        compiled_signature;
        default_ctx_params;
      }
  in
  Context.add_field ~name ~elem;
  Ctx.clear ()
