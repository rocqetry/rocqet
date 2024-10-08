(* Some of these functions are copied verbatim from
   https://github.com/DKXXXL/FPOP/blob/main/src/utils.ml#L407*)

(* Magic constants embedded in these functions *)
let motive_of name = Nameops.add_prefix "__motiveT" name
let internal_name name = Nameops.add_prefix "__internal_" name

let inductive_axiom_name = Nameops.add_prefix "ind__"

let recursor_type ~inductive suffix =
  Nameops.add_prefix "__recursor_type_" (Nameops.add_suffix inductive suffix)

let handler_type name ~suffix =
  Nameops.add_suffix (Nameops.add_prefix "__handler_type_" name) suffix

let recursion_handler_type ~function_name ~case_name =
  let name =
    Printf.sprintf "%s_%s_type"
      (Names.Id.to_string function_name)
      (Names.Id.to_string case_name)
  in
  Names.Id.of_string name

let handler_name ~recursor ~case =
  Names.Id.to_string recursor ^ Names.Id.to_string case |> Names.Id.of_string

let principle_name ~inductive ~kind = Nameops.add_suffix inductive kind

let computational_axiom_name ~recursor_name ~constructor_name =
  Names.Id.to_string recursor_name
  ^ "_"
  ^ Names.Id.to_string constructor_name
  ^ "_eq"
  |> Names.Id.of_string

let partial_recursor_name ~(inductive_name: Names.Id.t) ~(family_name: Names.Id.t) = 
  Names.Id.to_string inductive_name
  ^ "_prect_"  
  ^ Names.Id.to_string family_name
  |> Names.Id.of_string

let prec_computational_axiom_name ~constructor_name ~family_name = 
  Names.Id.to_string constructor_name
  ^ "_eq_"
  ^ Names.Id.to_string family_name
  |> Names.Id.of_string

let point_qualid (f : Names.Id.t) (path : Libnames.qualid) : Libnames.qualid =
  let path, base = Libnames.repr_qualid path in
  let newpath = List.append (Names.DirPath.repr path) [ f ] in
  Libnames.make_qualid (Names.DirPath.make newpath) base

let _point_optionqualid (f : Names.Id.t) (path : Libnames.qualid option) :
    Libnames.qualid =
  match path with
  | None -> Libnames.qualid_of_ident f
  | Some x -> point_qualid f x

let qualid_point (path : Libnames.qualid option) (f : Names.Id.t) :
    Libnames.qualid =
  match path with
  | Some path ->
      let path, base = Libnames.repr_qualid path in
      let path = base :: Names.DirPath.repr path in
      let path = Names.DirPath.make path in
      Libnames.make_qualid path f
  | None -> Libnames.qualid_of_ident f

let _qualid_qualid_ (headpath : Libnames.qualid) (tailpath : Libnames.qualid) :
    Libnames.qualid =
  let tailpath1, base = Libnames.repr_qualid tailpath in
  let headpath_in_list =
    let headpath1, headpath2 = Libnames.repr_qualid headpath in
    let headpath1 = Names.DirPath.repr headpath1 in
    headpath2 :: headpath1
  in
  let tailpath1 = Names.DirPath.repr tailpath1 in
  let newtailpath1 = tailpath1 @ headpath_in_list in
  Libnames.make_qualid (Names.DirPath.make newtailpath1) base

(* extract a path into (path "." name) *)
let _to_qualid_name (path : Libnames.qualid) :
    Libnames.qualid option * Names.Id.t =
  let open Libnames in
  if qualid_is_ident path then (None, qualid_basename path)
  else
    let prefix_path, base = Libnames.repr_qualid path in
    match Names.DirPath.repr prefix_path with
    | [] -> Errors.fail ~info:"Unexpected Error"
    | newbase :: remained ->
        (Some (make_qualid (Names.DirPath.make remained) newbase), base)

let path_to_list (path : Libnames.qualid) : Names.Id.t list =
  let prefix, base = Libnames.repr_qualid path in
  let prefix = List.rev (Names.DirPath.repr prefix) in
  prefix @ [ base ]

(* Say path = A.B.C.D, we want (A.B.C, D) *)
let path_to_prefix (path : Libnames.qualid) :
    Libnames.qualid option * Names.Id.t =
  let prefix, base = Libnames.repr_qualid path in
  match Names.DirPath.repr prefix with
  | [] -> (None, base)
  | _ -> (Some (Libnames.qualid_of_dirpath prefix), base)

let make_module_path head path =
  let head = Libnames.qualid_of_ident head in
  List.fold_left
    (fun module_path x -> qualid_point (Some module_path) x)
    head path

let list_to_path (names : Names.Id.t list) : Libnames.qualid =
  match names with
  | [] -> Errors.fail ~info:"list_to_path: expected a non empty list"
  | head :: path -> make_module_path head path

(* extract a path into (name "." path) *)
let to_name_qualid (path : Libnames.qualid) : Names.Id.t * Libnames.qualid =
  let prefix_path, base = Libnames.repr_qualid path in
  let prefix_path = Names.DirPath.repr prefix_path in
  let rec extract_final l =
    match l with
    | [] -> Errors.fail ~info:"Not implemented"
    | [ t ] -> (t, [])
    | h :: t ->
        let final, t' = extract_final t in
        (final, h :: t')
  in
  let startingpoint, remained = extract_final prefix_path in
  let remained = Libnames.make_qualid (Names.DirPath.make remained) base in
  (startingpoint, remained)

let to_name_optionqualid (path : Libnames.qualid) :
    Names.Id.t * Libnames.qualid option =
  let open Libnames in
  if qualid_is_ident path then (qualid_basename path, None)
  else
    let head, tail = to_name_qualid path in
    (head, Some tail)

let replace_qualid_root ~source ~target =
  let open Constrexpr_ops in
  let open Constrexpr in
  let open Libnames in
  let take_root_of_path (t : qualid) : Names.Id.t = fst (to_name_qualid t) in
  let replace_root_of_path (t : qualid) (nr : Names.Id.t) : qualid =
    let _, tail = to_name_qualid t in
    point_qualid nr tail
  in
  let rec replace_qualid_path _ r =
    match r with
    | { CAst.loc = _; v = CRef (qid, us) } as x when not (qualid_is_ident qid)
      -> (
        (* rename the  *)
        match Names.Id.equal (take_root_of_path qid) source with
        | true ->
            let qid = replace_root_of_path qid target in
            CAst.make (CRef (qid, us))
        | false -> x)
    | cn ->
        map_constr_expr_with_binders (fun _ _ -> ()) replace_qualid_path () cn
  in
  replace_qualid_path ()

let self_version = Nameops.add_prefix "self__"

(* Strip self__ from the prefix of a name *)
let un_self_version name =
  let s = Names.Id.to_string name in
  if String.starts_with ~prefix:"self__" s then
    let newbeginning =
      String.sub s (String.length "self__")
        (String.length s - String.length "self__")
    in
    Names.Id.of_string newbeginning
  else name

let replace_self (path: Names.Id.t list) (name : Names.Id.t) = 
  let find_path lst target =
     let rec aux acc = function
       | [] -> None
       | hd :: tl ->
           if Names.Id.equal hd target then Some (List.rev (hd :: acc))
           else aux (hd :: acc) tl
     in
     aux [] lst
  in 
  let target = un_self_version name in   
  match find_path path target with 
  | None -> [name]
  | Some prefix -> prefix

let replace_self_qualification ~(target : Libnames.qualid option) =
  let open Constrexpr_ops in
  let open Constrexpr in
  let open Libnames in
  let take_root_of_path (t : qualid) : Names.Id.t = fst (to_name_qualid t) in
  let replace_root_of_path (t : qualid) : qualid =
    let name, tail = to_name_qualid t in
    let tail = path_to_list tail in
    match target with
    | None -> list_to_path tail
    | Some target ->
        let target = path_to_list target in
        let target = replace_self target name in 
        list_to_path (target @ tail)
  in
  let rec replace_qualid_path _ r =
    match r with
    | { CAst.loc = _; v = CRef (qid, us) } as x when not (qualid_is_ident qid)
      -> (
        (* rename the  *)
        let source = Names.Id.to_string (take_root_of_path qid) in
        match String.starts_with ~prefix:"self__" source with
        | true ->
            let qid = replace_root_of_path qid in            
            CAst.make (CRef (qid, us))
        | false -> x)
    | cn ->
        map_constr_expr_with_binders (fun _ _ -> ()) replace_qualid_path () cn
  in
  replace_qualid_path ()

let rename_ind_constructors (constructors : Vernacexpr.constructor_expr list)
    ~base_name ~derived_name : Vernacexpr.constructor_expr list =
  let rename_one_ind_constructor (constructor : Vernacexpr.constructor_expr) =
    let a, (b, term) = constructor in
    (a, (b, replace_qualid_root ~source:base_name ~target:derived_name term))
  in
  constructors |> List.map rename_one_ind_constructor

(* Adapted from Constexpr_ops.replace_vars_constr_expr to add paths. *)
let add_path_constr_expr path l r =
  let open Constrexpr_ops in
  let open Constrexpr in
  let open Libnames in
  let rec go l r =
    match r with
    | { CAst.loc; v = CRef (qid, us) } as x when qualid_is_ident qid ->
        let id = qualid_basename qid in
        if Names.Id.Set.mem id l then
          CAst.make ?loc
          @@ CRef (make_qualid ?loc (Names.DirPath.make [ path ]) id, us)
        else x
    | cn -> map_constr_expr_with_binders Names.Id.Set.remove go l cn
  in
  go l r

(** Add [path] as a prefix for every [name] in [names] which
    can be found in [target] *)
let add_prefix_path ~(path : Libnames.qualid) ~(names : Names.Id.Set.t)
    ~(target : Constrexpr.constr_expr) =
  let open Constrexpr_ops in
  let open Constrexpr in
  let open Libnames in
  let rec go names target =
    match target with
    | { CAst.loc; v = CRef (qid, us) } as x when qualid_is_ident qid ->
        (* Always assuming it's a basename we want! *)
        let id = qualid_basename qid in
        if Names.Id.Set.mem id names then
          let path = qualid_point (Some path) id in
          CAst.make ?loc @@ CRef (path, us)
        else x
    | cn -> map_constr_expr_with_binders Names.Id.Set.remove go names cn
  in
  go names target



let unique_id =
  let counter = Summary.ref ~name:"FreshCounter" 0 in
  fun () ->
    incr counter;
    !counter

let fresh_name ~prefix =
  let time_stamp = string_of_int @@ unique_id () in
  Names.Id.of_string (prefix ^ "回" ^ time_stamp)

let module_name_of ~family_name type_name =
  let prefix =
    type_name
    |> Nameops.add_prefix (Names.Id.to_string family_name)
    |> Names.Id.to_string
  in
  fresh_name ~prefix

let name_map_with f =
  List.fold_left
    (fun acc name -> Names.Id.Map.add name (f name) acc)
    Names.Id.Map.empty

let inv_name_map_with f =
  List.fold_left
    (fun acc name -> Names.Id.Map.add (f name) name acc)
    Names.Id.Map.empty

let concat_names names =
  names
  |> List.map Names.Id.to_string
  |> List.sort String.compare |> String.concat "_" |> Names.Id.of_string

let is_self_name name = 
    name |> Names.Id.to_string |> String.starts_with ~prefix:"self__"

let is_self_qualid path = 
      path |> path_to_list |> List.exists is_self_name

let remove_self_qualid name = 
    let rec remove_self_qual = function 
        | [] -> Errors.fail ~info:"remove_self_qual: empty list"
        | p :: path when is_self_name p -> list_to_path path
        | _ :: path -> remove_self_qual path                             
    in 
    remove_self_qual (path_to_list name)
