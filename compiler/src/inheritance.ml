open Env

let close_current_inheritance_judgement () = Context.close ()
let open_new_inheritance_judgement name = Context.start_linkage name

let open_derived_inheritance_judgement ~base ~derived =
  Context.start_linkage_with_base ~name:derived ~base
