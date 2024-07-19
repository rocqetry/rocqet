open Types

(* Some functions are from https://github.com/tlringer/plugin-tutorial/blob/main/src/termutils.ml *)

(** Get the global environment *)
let global_env () =
  let env = Global.env () in
  (Evd.from_env env, env)

(** When you first start using a plugin, if you want to manipulate terms
 in an interesting way, you need to move from the external representation
 of terms to the internal representation of terms. This does that for you. *)
let internalize env trm sigma = Constrintern.interp_constr_evars env sigma trm

let checked_type_of trm =
  let sigma, env = global_env () in
  let sigma, trm = internalize env trm sigma in
  let sigma, typ = Typing.type_of env sigma trm in
  EConstr.to_constr sigma typ

let reflect_checked_term trm =
  let sigma, env = global_env () in
  Constrextern.extern_constr env sigma (EConstr.of_constr trm)

(* Call by name reduction *)
let cbn_type_check t : Constr.t =
  let sigma, env = global_env () in
  let sigma, internalized = Constrintern.interp_constr_evars env sigma t in
  let normalized_intern =
    Cbn.norm_cbn RedFlags.allnolet env sigma internalized
  in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in
  normalized_intern

type local_binder_expr_assume =
  Names.lname list * Constrexpr.binder_kind * Constrexpr.constr_expr

(* Verbatim from FPOP *)
let collect_argument_and_ret_of_type (f : Constrexpr.constr_expr) :
    (local_binder_expr_assume * Constrexpr.constr_expr) list
    * Constrexpr.constr_expr =
  let open Constrexpr in
  let open Constrexpr_ops in
  let isDepProd { CAst.v = t; _ } =
    match t with CProdN _ -> true | _ -> false
  in
  let isArrow { CAst.v = t; _ } =
    match t with CNotation (_, (_, "_ -> _"), _) -> true | _ -> false
  in
  let destDepProd { CAst.v = t; _ } =
    match t with
    | CProdN (al, b) ->
        (* assert_cerror (fun _ ->List.length al = 1); *)
        (al, b)
    | _ -> Errors.fail ~info:"Expected a CProdN"
  in
  let destArrow { CAst.v = t; _ } =
    match t with
    | CNotation (_, (_, "_ -> _"), ([ domain; codomain ], _, _, _)) ->
        (domain, codomain)
    | _ -> Errors.fail ~info:"Expected a CNotation"
  in
  let give_name ({ CAst.v = n; _ } : Names.lname) : Names.Id.t =
    match n with
    | Names.Anonymous -> Naming.fresh_name ~prefix:"arg"
    | Names.Name n -> n
  in
  let local_binders_to_list_of_local_binder (e : local_binder_expr) :
      (local_binder_expr_assume * Constrexpr.constr_expr) list =
    match e with
    | CLocalAssum (l, k, b) ->
        List.map
          (fun x ->
            let x = give_name x in
            ( ([ CAst.make (Names.Name x) ], k, b),
              mkRefC (Libnames.qualid_of_ident x) ))
          l
    | _ -> Errors.fail ~info:"Expected a CLocalAssum"
  in
  let ret : Constrexpr.constr_expr option ref = ref None in
  let rec collect_argument (f : Constrexpr.constr_expr) :
      (local_binder_expr_assume * Constrexpr.constr_expr) list =
    match f with
    | f when isDepProd f ->
        let parameters, body = destDepProd f in
        let all_parameters =
          List.map local_binders_to_list_of_local_binder parameters
        in
        let all_parameters = List.flatten all_parameters in
        all_parameters @ collect_argument body
    | f when isArrow f ->
        let domain, codomain = destArrow f in
        let newname = Naming.fresh_name ~prefix:"arg" in
        let binder =
          ( [ CAst.make (Names.Name newname) ],
            Default Glob_term.Explicit,
            domain )
        in
        (binder, mkRefC (Libnames.qualid_of_ident newname))
        :: collect_argument codomain
    | x ->
        ret := Some x;
        []
  in
  let res = collect_argument f in
  match !ret with
  | None -> Errors.fail ~info:"Expected Some"
  | Some res2 -> (res, res2)

(* a functional r will be lead to
     forall ..., (r ..) = (r ..)
     and do type check
   then we return
   [forall ...] and [r ..]
*)
let extract_variables_and_apply (r : Constrexpr.constr_expr) :
    (local_binder_expr_assume * Constrexpr.constr_expr) list
    * Constrexpr.constr_expr =
  (* let open Constrexpr in  *)
  let open Constrexpr_ops in
  let typeofr = reflect_checked_term @@ checked_type_of r in
  let all_binders_and_args = fst @@ collect_argument_and_ret_of_type typeofr in
  let all_args = List.map snd all_binders_and_args in
  (* let eq_cstr = Coqlib.lib_ref "core.eq.refl" in *)
  let fully_applied_r = mkAppC (r, all_args) in
  let _ =
    (* sanity type checking *)
    (* Now we construct (r ...) = (r ...) and wrap with universal quanitifer *)
    let eq_cstr =
      mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq"
    in
    let id_on_fully_applied_r =
      mkAppC (eq_cstr, [ fully_applied_r; fully_applied_r ])
    in
    let all_binders = List.map fst all_binders_and_args in
    let res =
      List.fold_right
        (fun (a, b, c) body -> mkProdC (a, b, c, body))
        all_binders id_on_fully_applied_r
    in
    checked_type_of res
  in
  (all_binders_and_args, fully_applied_r)

let ident_to_module_expr ident = CAst.make (Constrexpr.CMident ident)

let apply_module ~(functor_expr : Constrexpr.module_ast)
    ~(arguments : Libnames.qualid list) : Constrexpr.module_ast =
  let open Constrexpr in
  List.fold_left
    (fun op x -> CAst.make (CMapply (op, x)))
    functor_expr arguments

let calculate_computational_axiom_for_constructor ~recursor_name ~recursor_path
    ~constructor_name ~constructor_path =
  let open Constrexpr_ops in
  let constructor_params, fully_applied_constr =
    extract_variables_and_apply (mkRefC constructor_path)
  in
  let recursor_params, _ =
    recursor_path |> mkRefC |> checked_type_of |> reflect_checked_term
    |> collect_argument_and_ret_of_type
  in
  let recursor_parameter_wo_first = List.tl recursor_params in
  let recursor_remained_arguments = List.map snd recursor_parameter_wo_first in
  let params = constructor_params @ recursor_parameter_wo_first in
  let recursor_applied =
    mkAppC
      (mkRefC recursor_path, fully_applied_constr :: recursor_remained_arguments)
  in
  let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in
  (* let right =
       mkRefC @@
         Libnames.qualid_of_ident @@
           Nameops.add_suffix recursor_name (Names.Id.to_string constructor_name)
     in *)
  let id_on_fully_applied_r =
    mkAppC (eq_cstr, [ recursor_applied; recursor_applied ])
  in
  let closed_recursor_applied =
    List.fold_right
      (fun (a, b, c) body -> mkProdC (a, b, c, body))
      (List.map fst params) id_on_fully_applied_r
  in
  (* The final axiom is an equation *)
  let equation =
    let reflected =
      closed_recursor_applied |> cbn_type_check |> reflect_checked_term
    in
    (* let sigma, env = global_env () in
       let display = Pp.string_of_ppcmds @@ Ppconstr.pr_constr_expr env sigma reflected in
       Printf.printf "Display: %s\n" display;
       failwith "" |> ignore; *)
    let _, body = collect_argument_and_ret_of_type reflected in
    let destEq { CAst.v = t; _ } =
      match t with
      | Constrexpr.CNotation (_, (_, "_ = _"), ([ lhs; rhs ], _, _, _)) ->
          (lhs, rhs)
      | _ -> Errors.fail ~info:"Expected CNotation"
    in
    let normalized, _ = destEq body in
    let id_on_applied_and_normalized =
      mkAppC (eq_cstr, [ recursor_applied; normalized ])
    in
    (* let sigma, env = global_env () in
       let result =
         Pp.string_of_ppcmds @@  Ppconstr.pr_constr_expr env sigma normalized
       in
       Printf.printf "Result: %s\n" result;
       failwith "" |> ignore;*)
    List.fold_right
      (fun (a, b, c) body -> mkProdC (a, b, c, body))
      (List.map fst params) id_on_applied_and_normalized
  in
  let equation_name =
    Names.Id.to_string recursor_name
    ^ "_"
    ^ Names.Id.to_string constructor_name
    ^ "_eq"
    |> Names.Id.of_string
  in
  (equation_name, equation)

let generate_computational_axioms ~provenance ~constructors ~recursor =
  let prefix = Libnames.qualid_of_ident (Naming.self_version provenance) in
  let recursor_name = recursor in
  let recursor_path = Libnames.qualid_of_ident recursor in
  let constructors =
    constructors
    |> List.map (fun name -> (name, Naming.qualid_point (Some prefix) name))
  in
  constructors
  |> List.map (fun (constructor_name, constructor_path) ->
         calculate_computational_axiom_for_constructor ~recursor_name
           ~recursor_path ~constructor_name ~constructor_path)

(* Given a recursor name and a compiled recursor return the type
   each handler is supposed to be *)
let handler_types_table name (recursor : CompiledRecursor.t) =
  let motive = Naming.motive_of name in
  recursor.compiled_handlers
  |> List.map (fun (handler_name, _) ->
         let motive_term =
           Constrexpr_ops.mkRefC (Libnames.qualid_of_ident motive)
         in
         let handler_type = Naming.handler_type handler_name in
         let handler_type =
           Constrexpr_ops.mkRefC (Libnames.qualid_of_ident handler_type)
         in
         let handler_type =
           Constrexpr_ops.mkAppC (handler_type, [ motive_term ])
         in
         (handler_name, handler_type))

let rec extract_handlers_from_inductive_proof
    (all_recur_names : Names.Id.t list)
    (acc_case_handlers : Constrexpr.constr_expr) (suffix : RecKind.t) =
  let coq_fst x =
    let open Constrexpr_ops in
    let fst =
      let using_prod_or_conj =
        match suffix with RecKind.IndComplete -> "proj1" | _ -> "fst"
      in
      mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string using_prod_or_conj)
    in
    mkAppC (fst, [ x ])
  in
  let coq_snd x =
    let open Constrexpr_ops in
    let snd =
      let using_prod_or_conj =
        match suffix with RecKind.IndComplete -> "proj2" | _ -> "snd"
      in
      mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string using_prod_or_conj)
    in
    mkAppC (snd, [ x ])
  in
  match all_recur_names with
  | [] -> []
  | h :: t ->
      (h, coq_fst acc_case_handlers)
      :: extract_handlers_from_inductive_proof t
           (coq_snd acc_case_handlers)
           suffix

let calculate_inductive_proof_goal ~(theorem_name : Names.Id.t)
    ~(handlers : Names.Id.t list) ~(suffix : RecKind.t) =
  let open Constrexpr_ops in
  let the_motive =
    theorem_name |> Naming.motive_of |> Libnames.qualid_of_ident |> mkRefC
  in
  let __True = mkIdentC (Names.Id.of_string "True") in
  let __prod l r =
    let using_prod_or_conj =
      match suffix with RecKind.IndComplete -> "and" | _ -> "prod"
    in
    mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [ l; r ])
  in
  let all_recur_name =
    List.map (fun name -> Naming.handler_type name) handlers
  in
  let all_recur_ = List.map mkIdentC all_recur_name in
  let all_applied_recur =
    List.map (fun x -> mkAppC (x, [ the_motive ])) all_recur_
  in
  List.fold_right __prod all_applied_recur __True
