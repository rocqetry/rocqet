(* From https://github.com/tlringer/plugin-tutorial/blob/main/src/termutils.ml *)

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
  let env = Global.env() in 
  let sigma = Evd.from_env env in 
  let (sigma, internalized) = Constrintern.interp_constr_evars env sigma t in    
  let normalized_intern = Cbn.norm_cbn RedFlags.allnolet env sigma internalized in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in   
  normalized_intern

type local_binder_expr_assume = 
  Names.lname list * Constrexpr.binder_kind * Constrexpr.constr_expr

(* Verbatim from FPOP *)
let collect_argument_and_ret_of_type 
      (f : Constrexpr.constr_expr) 
    : (local_binder_expr_assume * Constrexpr.constr_expr) list * 
      Constrexpr.constr_expr =
    let open Constrexpr in 
    let open Constrexpr_ops in 
    let isDepProd {CAst.v = t; _} = match t with | CProdN _ -> true | _ -> false in
    let isArrow {CAst.v = t; _} = match t with | CNotation (_, (_, "_ -> _"), _) -> true | _ -> false in
    let destDepProd {CAst.v = t; _} = 
      match t with 
      | CProdN (al, b) -> 
         (* assert_cerror (fun _ ->List.length al = 1); *) 
         (al, b)
      | _ -> Errors.fail ~info:"Expected a CProdN" 
    in 
    let destArrow {CAst.v = t; _} = 
      match t with 
      | CNotation (_ ,(_, "_ -> _"), ([domain; codomain], _, _, _)) -> (domain, codomain) 
      | _ -> Errors.fail ~info:"Expected a CNotation" 
    in
    let give_name ({CAst.v = n; _} : Names.lname) : Names.Id.t =
      match n with 
      | Names.Anonymous -> Naming.fresh_name ~prefix:"arg"
      | Names.Name n -> n 
    in 
    let local_binders_to_list_of_local_binder 
          (e : local_binder_expr) : (local_binder_expr_assume * Constrexpr.constr_expr) list  = 
      match e with 
      | CLocalAssum (l, k, b) -> 
        List.map (fun x -> 
                    let x = give_name x in 
                      ([CAst.make (Names.Name x)], k, b), 
                      mkRefC (Libnames.qualid_of_ident x) ) l  
      | _ -> Errors.fail ~info:"Expected a CLocalAssum" 
    in
    let ret : Constrexpr.constr_expr option ref = ref None in 
    let rec collect_argument (f : Constrexpr.constr_expr) : (((local_binder_expr_assume) * Constrexpr.constr_expr) list) =
      match f with 
      | f when (isDepProd f) ->
        let parameters, body = destDepProd f in 
        let all_parameters = List.map local_binders_to_list_of_local_binder parameters in 
        let all_parameters = List.flatten all_parameters in 
        all_parameters @ (collect_argument body)
      | f when (isArrow f) -> 
        let domain, codomain = destArrow f in 
        let newname = Naming.fresh_name ~prefix:"arg" in
        let binder = (([CAst.make (Names.Name newname)], Default Glob_term.Explicit, domain)) in 
        (binder, mkRefC (Libnames.qualid_of_ident newname))::collect_argument codomain 
      | x -> 
        ret := (Some x);
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
let extract_variables_and_apply (r : Constrexpr.constr_expr) 
     : (local_binder_expr_assume * Constrexpr.constr_expr) list * 
       Constrexpr.constr_expr =
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
    let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in 
    let id_on_fully_applied_r =  mkAppC (eq_cstr, [fully_applied_r;fully_applied_r]) in  
    let all_binders = List.map fst all_binders_and_args in 
    let res = List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) all_binders id_on_fully_applied_r in 
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
