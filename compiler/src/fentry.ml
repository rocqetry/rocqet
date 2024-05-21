(* The entry point to the plugin's functionalities *)

let finductive _inductive_definitions = Feedback.msg_info (Pp.str "FInductive") 

let fend _scope_name = Feedback.msg_info (Pp.str "FEnd")

(* We want to modify the internal state of the plugin to know that
   we are at a family command. We want to add the right parameters
   to the context *)
let family name = 
  (* Step 1: Ensure that the family name is not duplicated in the "context" *)  

  (* Step 2: Generate a new id for this family *)

  (* Step 3: Add a new inheritance judgement to the context *)
  
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



