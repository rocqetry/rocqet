(* These functions are copied verbatim from
   https://github.com/DKXXXL/FPOP/blob/main/src/utils.ml#L407*)

let point_qualid (f : Names.Id.t) (path : Libnames.qualid) : Libnames.qualid =
  let path, base = Libnames.repr_qualid path in
  let newpath = List.append (Names.DirPath.repr path) [ f ] in
  Libnames.make_qualid (Names.DirPath.make newpath) base

let _point_optionqualid (f : Names.Id.t) (path : Libnames.qualid option) :
    Libnames.qualid =
  match path with
  | None -> Libnames.qualid_of_ident f
  | Some x -> point_qualid f x

let _qualid_point_ (path : Libnames.qualid option) (f : Names.Id.t) :
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

let rename_ind_constructors (constructors : Vernacexpr.constructor_expr list)
    ~base_name ~derived_name : Vernacexpr.constructor_expr list =
  let rename_one_ind_constructor (constructor : Vernacexpr.constructor_expr) =
    let a, (b, term) = constructor in
    (a, (b, replace_qualid_root ~source:base_name ~target:derived_name term))
  in
  constructors |> List.map rename_one_ind_constructor

let self_version = Nameops.add_prefix "self__"

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
