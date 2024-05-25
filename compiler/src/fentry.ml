(* The entry point to the plugin's functionalities *)

let finductive inductive_definitions =
  Fenv.PluginScopes.ensure_in_scope ~scope:Ftypes.PluginCmd.Family;
  Finh.add_inductive_definition inductive_definitions

let fend _scope_name = Feedback.msg_info (Pp.str "FEnd")

let family name =
  Finh.add_new_family name;
  Fenv.PluginScopes.push
    Ftypes.
      {
        PluginCmdScope.name;
        command = PluginCmd.Family;
        close =
          (fun () ->
            Finh.ScopeClosing.inherit_all_remained ();
            Finh.ScopeClosing.close_current_inheritance_judgement ());
      };

  let message = Pp.(str "Family " ++ (name |> Names.Id.to_string |> str)) in
  Feedback.msg_info message

let family_extends ~derived ~base =
  let message =
    Pp.(
      str "Family "
      ++ (derived |> Names.Id.to_string |> str)
      ++ str " extends "
      ++ (base |> Names.Id.to_string |> str))
  in
  Feedback.msg_info message
