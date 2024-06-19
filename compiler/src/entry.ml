open Types
open Env
(* The entry point to the plugin's functionalities *)

let finductive inductive_definitions =
  PluginScopes.ensure_in_scope ~scope:PluginCmd.Family;
  Inductive.add_inductive_definition inductive_definitions

let fend scope_name =
  match PluginScopes.pop scope_name with
  | None -> Errors.fail ~info:"There is no open scope"
  | Some scope ->
      let PluginCmdScope.{ close; _ } = scope in
      close ()

let family name =
  Family.open_family name;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Family; close = Family.close_family }

let family_extends ~derived ~base =
  Family.open_family_with_base ~base ~name:derived;
  PluginScopes.push
    PluginCmdScope.
      {
        name = derived;
        command = PluginCmd.Family;
        close = Family.close_family;
      }

let frecursor ~ind_decls ~rec_mod ~suffix =
  PluginScopes.ensure_in_scope ~scope:PluginCmd.Family;
  Recursion.add_recursor ~ind_decls ~rec_mod ~suffix

let definition ~name ~body_type ~body_expr =
  Inheritance.inherit_dependencies ~prefix:name;
  let context = Context.get () in
  let compiled_context, parameters =
    Codegen.compile_linkage_context ~field_name:name context
  in
  let compiled_impl =
    Codegen.compile_definition ~name ~body_type ~body_expr ~parameters
  in
  let elem =
    LinkageElem.FieldDefinition
      { body_expr; body_type; compiled_context; compiled_impl }
  in
  Context.add_field ~name ~elem

(* assert_in_scope OpenedFamily;
   add_new_field fname ~eT:(Some eT) e*)
