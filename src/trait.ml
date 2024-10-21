
let open_with_base ~name ~base = 
  Inheritance.inherit_dependencies ~prefix:base;  
  ()
