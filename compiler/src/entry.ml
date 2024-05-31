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
  Inheritance.open_new_inheritance_judgement name;  
  PluginScopes.push
    PluginCmdScope.
      {
        name;
        command = PluginCmd.Family;
        close = (fun () -> Inheritance.close_current_inheritance_judgement ());
      };

  let message = Pp.(str "Family " ++ (name |> Names.Id.to_string |> str)) in
  Feedback.msg_info message

let family_extends ~derived ~base =
  Inheritance.open_derived_inheritance_judgement ~derived ~base;  
  PluginScopes.push
    PluginCmdScope.
      {
        name = derived;
        command = PluginCmd.Family;
        close =
          (fun () ->            
            Inheritance.close_current_inheritance_judgement ());
      }
