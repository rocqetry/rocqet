(* The entry point to the plugin's functionalities *)

let finductive inductive_definitions = 
  Fenv.PluginScopes.ensure_in_scope ~scope:Ftypes.PluginCmd.Family;
  let name = 
    inductive_definitions
    |> Ftypes.VernacInductive.extract_type_ident  
    |> List.hd (* No mutual inductive types *)
  in
  
  Finh.add_inductive_definition inductive_definitions;
  (* let result = result |> List.map (fun name -> name |> Names.Id.to_string) in 
  let result = List.fold_left (^) "" result in *)
  Feedback.msg_info (name |> Names.Id.to_string |> Pp.str) 

let fend _scope_name = 
  Feedback.msg_info (Pp.str "FEnd")

(* We want to modify the internal state of the plugin to know that
   we are at a family command. We want to add the right parameters
   to the context *)
let family name = 
  (* Step 1: Ensure that the family name is not duplicated in the "context" *)  

  (* Step 2: Generate a new id for this family *)

  (* Step 3: Add a new inheritance judgement to the context *)

  Finh.add_new_family name;
  Fenv.PluginScopes.push Ftypes.{ 
      PluginCmdScope.name; 
      command = PluginCmd.Family;
      close = fun () -> ()
  };
  
  let message = 
      Pp.(str "Family " ++ (name |> Names.Id.to_string |> str))
    in
    Feedback.msg_info message

let family_extends ~derived ~base = 
    let message = 
      Pp.(str "Family " ++ 
          (derived |> Names.Id.to_string |> str) ++ 
          str " extends " ++ 
          (base |> Names.Id.to_string |> str))
    in
    Feedback.msg_info message



