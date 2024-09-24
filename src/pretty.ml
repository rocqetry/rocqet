(* Pretty printing *)

let pretty_qualid (name : Libnames.qualid) =
  name |> Naming.path_to_list
  |> List.map Names.Id.to_string
  |> String.concat "."

(*
   let rec print_linkage_fields (linkage : Linkage.t) =
     linkage.fields
     |> Bwd.iter (fun (name, element) ->
            Feedback.msg_warning @@ Pp.str @@ Printf.sprintf "%s\n" (Names.Id.to_string name);
            match element with
            | LinkageElem.InductiveDefinition { inductive; _ } ->
               Feedback.msg_warning @@ Pp.str "Inductive:";
               let constructors = inductive |> VernacInductive.extract_all_names |> List.concat_map snd in
               constructors |> List.iter (fun name -> Feedback.msg_warning @@ Pp.str @@ Printf.sprintf "%s\n" (Names.Id.to_string name))
            | LinkageElem.FamilyDefinition { linkage; _ } ->
               Feedback.msg_warning @@ Pp.str "Inner:";
               print_linkage_fields linkage
            | _ -> ())
*)

(*

   let rec print_linkage_fields (linkage : Linkage.t) =
     linkage.fields
     |> Bwd.iter (fun (name, element) ->
            Printf.printf "%s\n" (Names.Id.to_string name);
            match element with
            | LinkageElem.InductiveDefinition { inductive; _ } ->
               Printf.printf "Inductive:\n";
               let constructors = inductive |> VernacInductive.extract_all_names |> List.concat_map snd in
               constructors |> List.iter (fun name -> Printf.printf "%s\n" (Names.Id.to_string name))
            | LinkageElem.FamilyDefinition { linkage; _ } ->
               print_endline "Inner:";
               print_linkage_fields linkage
            | _ -> ())
*)
