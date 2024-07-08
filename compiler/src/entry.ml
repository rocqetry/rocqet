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

(* let frecursor ~ind_decls ~rec_mod ~suffix =
   PluginScopes.ensure_in_scope ~scope:PluginCmd.Family;
   Recursion.add_recursor ~ind_decls ~rec_mod ~suffix*)

let definition ~name ?body_type body_expr =
  Definition.add_definition ~name ?body_type body_expr

let frecursion ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) ~(suffix : RecKind.t) =
  Recursion.open_recursion ~name ~inductive ~motive ~suffix;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Recursion; close = Recursion.close_recursion }

let frecursion_extension ~(name : Names.Id.t) =
  Recursion.open_recursion_extension ~name;
  PluginScopes.push
    PluginCmdScope.
      { name; command = PluginCmd.Recursion; close = Recursion.close_recursion }

let frecursion_handler = Recursion.add_handler

let finduction ~(name : Names.Id.t) ~(inductive : Libnames.qualid)
    ~(motive : Constrexpr.constr_expr) =
  Theorem.open_theorem ~name ~inductive ~motive
