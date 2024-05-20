(* The entry point to the plugin's functionalities *)

let finductive _inductive_definitions = Feedback.msg_info (Pp.str "FInductive") 

let fend _scope_name = Feedback.msg_info (Pp.str "FEnd")

let family name = 
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



