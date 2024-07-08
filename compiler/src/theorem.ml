(* FInduction implementation for extensible proofs *)
open Env
open Types

(* Private store *)
module Ctx = struct
  type t = {
    name : Names.Id.t;
    compiled_context : CompiledModuleType.t;
    parameters : (Names.Id.t * Constrexpr.module_ast) list;
    compiled_motive : CompiledModuleType.t;
    motive : Constrexpr.constr_expr;
    goal : Constrexpr.constr_expr;
    inductive : VernacInductive.t;
  }

  let store = Summary.ref ~name:"TheoremCtx" (None : t option)
  let update data = store := Some data
end

let handler_types_table name (recursor : CompiledRecursor.t) =
  let motive = Naming.motive_of name in
  recursor.compiled_handlers
  |> List.map (fun (handler_name, _) ->
         let motive_term =
           Constrexpr_ops.mkRefC (Libnames.qualid_of_ident motive)
         in
         let handler_type = Naming.handler_type handler_name in
         let handler_type =
           Constrexpr_ops.mkRefC (Libnames.qualid_of_ident handler_type)
         in
         let handler_type =
           Constrexpr_ops.mkAppC (handler_type, [ motive_term ])
         in
         (handler_name, handler_type))

let open_theorem ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) =
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let family_name = Context.family_name context in
  let motive = Resolver.resolve_constrexpr ~context ~expression:motive in
  let compiled_motive =
    Codegen.compile_motives ~names:[ name ] ~ctx:parameters ~motives:[ motive ]
      ~family_name
  in
  let inductive, compiled_recursors, _provenance =
    Context.lookup_inductive_for_recursion ~name:inductive context
  in
  let suffix = RecKind.IndComplete in
  let recursor = RecursorStore.find suffix compiled_recursors.recursors in
  let handler_types = handler_types_table name recursor in
  let goal =
    let open Constrexpr_ops in
    let the_motive =
      name |> Naming.motive_of |> Libnames.qualid_of_ident |> mkRefC
    in
    let __True = mkIdentC (Names.Id.of_string "True") in
    let __prod l r =
      let using_prod_or_conj =
        match suffix with RecKind.IndComplete -> "and" | _ -> "prod"
      in
      mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [ l; r ])
    in
    let all_recur_name =
      List.map (fun (name, _) -> Naming.handler_type name) handler_types
    in
    let all_recur_ = List.map mkIdentC all_recur_name in
    let all_applied_recur =
      List.map (fun x -> mkAppC (x, [ the_motive ])) all_recur_
    in
    List.fold_right __prod all_applied_recur __True
  in
  let ctx =
    Ctx.
      {
        name;
        goal;
        inductive;
        compiled_context;
        compiled_motive;
        motive;
        parameters;
      }
  in
  Ctx.update ctx

let close_theorem () = ()
