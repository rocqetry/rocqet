open Ftypes
(* The entry point to the plugin's functionalities *)

let finductive inductive_definitions =
  Fenv.PluginScopes.ensure_in_scope ~scope:Ftypes.PluginCmd.Family;
  Finh.add_inductive_definition inductive_definitions

let fend scope_name =
  match Fenv.PluginScopes.pop scope_name with
  | None -> Ferror.fail ~info:"There is no open scope"
  | Some scope ->
      let PluginCmdScope.{ close; _ } = scope in
      close ()

let family name =
  Scopes.open_new_inheritance_judgement name;
  Fenv.PluginScopes.push
    PluginCmdScope.
      {
        name;
        command = PluginCmd.Family;
        close =
          (fun () ->
            (* Finh.ScopeClosing.inherit_all_remained (); *)
            Scopes.close_current_inheritance_judgement ());
      };

  let message = Pp.(str "Family " ++ (name |> Names.Id.to_string |> str)) in
  Feedback.msg_info message

let family_extends ~derived ~base =
  Scopes.open_derived_inheritance_judgement ~derived ~base;
  Fenv.PluginScopes.push
    PluginCmdScope.
      {
        name = derived;
        command = PluginCmd.Family;
        close =
          (fun () ->
            Scopes.inherit_all_remained ();
            Scopes.close_current_inheritance_judgement ());
      }
