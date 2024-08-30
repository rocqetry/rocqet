let pretty_qualid (name : Libnames.qualid) =
  name |> Naming.path_to_list
  |> List.map Names.Id.to_string
  |> String.concat "."
