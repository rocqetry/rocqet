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
  let normalized_intern = Cbn.norm_cbn RedFlags.all env sigma internalized in
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

let flatten_inductive_constructor_type ~(inductive : VernacInductive.t)
    ~(constructor : Names.Id.t) =
  (* TODO: We will need all the names for the case of
     mutual recursion *)
  let ind_name =
    VernacInductive.extract_inductive_name inductive |> Libnames.qualid_of_ident
  in
  let constructor_type =
    inductive
    |> List.map (fun (inductive_expr, _) ->
           inductive_expr |> VernacInductive.extract_type_and_cstrs)
    |> List.find_map (fun (_, ctrs) -> List.assoc_opt constructor ctrs)
  in
  let constructor_type =
    match constructor_type with
    | None -> Errors.fail ~info:"Couldn't find constructor"
    | Some c -> c
  in
  let rec unflatten (c : Constrexpr.constr_expr) =
    match c.v with
    | CNotation (_, (_, "_ -> _"), ([ domain; codomain ], _, _, _)) -> (
        match domain.v with
        | Constrexpr.CRef (ty_name, _) when ind_name.v = ty_name.v ->
            Some ty_name.v :: unflatten codomain
        | _ -> None :: unflatten codomain)
    | _ -> []
  in
  unflatten constructor_type

(* This has to be called with recursor_path and constructor_path exposed *)
(* i.e is must be called inside a parameterized module *)
(* it must almost be called when there is LinkageCtx present *)
let generate_one_computational_axiom ~inductive ~recursor_name ~recursor_path
    ~constructor_name ~constructor_path ~context =
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
  let handler =
    let extract_name ({ CAst.v = n; _ } : Names.lname) : Names.Id.t =
      match n with
      | Names.Name n -> n
      | _ -> Errors.fail ~info:"Expected non anonymous argument"
    in
    let types =
      flatten_inductive_constructor_type ~inductive
        ~constructor:constructor_name
    in
    let arguments =
      constructor_params
      |> List.map (fun ((lnames, _, _), _) ->
             lnames |> List.hd |> extract_name |> Libnames.qualid_of_ident
             |> mkRefC)
    in
    let f ty arg =
      match ty with
      | None -> [ arg ]
      | Some _ ->
          let hypothesis = mkAppC (mkRefC recursor_path, [ arg ]) in
          [ arg; hypothesis ]
    in
    let arguments = List.concat (List.map2 f types arguments) in
    let handler =
      let handler_name =
        match context with
        | None ->
            Libnames.qualid_of_ident
            @@ Naming.handler_name ~recursor:recursor_name
                 ~case:constructor_name
        | Some context ->
            let prefix = Env.Context.family_name context in
            Naming.list_to_path
              [
                Naming.self_version prefix;
                Naming.handler_name ~recursor:recursor_name
                  ~case:constructor_name;
              ]
      in
      mkRefC @@ handler_name
    in
    mkAppC (handler, arguments)
  in
  let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in
  let id_on_fully_applied_r = mkAppC (eq_cstr, [ recursor_applied; handler ]) in
  let closed_recursor_applied =
    List.fold_right
      (fun (a, b, c) body -> mkProdC (a, b, c, body))
      (List.map fst params) id_on_fully_applied_r
  in
  (* The final axiom is an equation *)
  let equation = closed_recursor_applied in
  let equation_name =
    Naming.computational_axiom_name ~recursor_name ~constructor_name
  in
  (equation_name, equation)

let generate_computational_axioms ~(inductive : VernacInductive.t) ~recursor
    ~context ~prefix =
  (* let prefix = Libnames.qualid_of_ident (Naming.self_version provenance) in*)
  let recursor_name = recursor in
  let recursor_path = Libnames.qualid_of_ident recursor in
  let constructors =
    inductive |> List.hd |> fst |> VernacInductive.extract_type_and_cstrs |> snd
    |> List.map fst
  in
  let constructors =
    constructors
    |> List.map (fun name -> (name, Naming.qualid_point prefix name))
  in
  constructors
  |> List.map (fun (constructor_name, constructor_path) ->
         generate_one_computational_axiom ~inductive ~recursor_name ~context
           ~recursor_path ~constructor_name ~constructor_path)

(* Given a recursor name and a compiled recursor return the type
   each handler is supposed to be *)
let handler_types_table inductive_path name (recursor : CompiledRecursor.t)
    suffix =
  let motive = Naming.motive_of name in
  recursor.compiled_handlers
  |> List.map (fun (handler_name, _) ->
         let motive_term =
           let self =
             Naming.self_version (Env.Context.family_name (Env.Context.get ()))
           in
           let motive = Naming.list_to_path [ self; motive ] in
           Constrexpr_ops.mkRefC motive
         in
         let handler_type =
           Naming.recursion_handler_type ~function_name:name
             ~case_name:handler_name
         in
         inductive_path |> ignore;
         suffix |> ignore;
         let handler_type = Libnames.qualid_of_ident handler_type in
         let handler_type = Constrexpr_ops.mkRefC handler_type in
         let handler_type =
           Constrexpr_ops.mkAppC (handler_type, [ motive_term ])
         in
         (handler_name, handler_type))

let handler_type_for_recursion ~(name : Names.Id.t)
    ~(inductive_path : Libnames.qualid) ~(recursor : Recursor.t) :
    (Names.Id.t * Constrexpr.constr_expr) list =
  let motive_term =
    let motive = Naming.motive_of name in
    let self =
      Naming.self_version (Env.Context.family_name (Env.Context.get ()))
    in
    let motive = Naming.list_to_path [ self; motive ] in
    Constrexpr_ops.mkRefC motive
  in
  recursor.handlers
  |> List.map (fun (case_name, handler) ->
         let target =
           match inductive_path |> Naming.path_to_list |> List.rev with
           | [] | [ _ ] -> None
            (* Remove the inductive name, leave the family *)
           | _ :: path -> Some (path |> List.rev |> Naming.list_to_path)
         in         
         let handler = Naming.replace_self_qualification ~target handler in
         let handler =
           match target with
           | None -> handler
           | Some path ->
               let inductive_name =
                 inductive_path |> Naming.path_to_list |> List.rev |> List.hd
               in
               let names =
                 [ inductive_name; case_name ] |> Names.Id.Set.of_list
               in               
               Naming.add_prefix_path ~path ~names ~target:handler
         in         
         let handler =
           Resolver.resolve_constrexpr ~context:(Env.Context.get ())
             ~expression:handler
         in         
         let handler_type = Constrexpr_ops.mkAppC (handler, [ motive_term ]) in
         (case_name, handler_type))

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

let calculate_inductive_proof_goal
    ~(handler_types : Constrexpr.constr_expr list) ~(suffix : RecKind.t) =
  let open Constrexpr_ops in
  let __True = mkIdentC (Names.Id.of_string "True") in
  let __prod l r =
    let using_prod_or_conj =
      match suffix with RecKind.IndComplete -> "and" | _ -> "prod"
    in
    mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [ l; r ])
  in
  List.fold_right __prod handler_types __True

let mk_lambda arguments body =
  let f (n : Names.Id.t) =
    Constrexpr.CLocalPattern
      (CAst.make (Constrexpr.CPatAtom (Some (Libnames.qualid_of_ident n))))
  in
  let arguments = List.map f arguments in
  List.fold_right
    (fun arg body -> Constrexpr_ops.mkLambdaCN [ arg ] body)
    arguments body

let mk_lambda_with_type arguments body =
  let f ((n : Names.Id.t), (ty : Constrexpr.constr_expr)) =
    Constrexpr.CLocalAssum
      ( [ CAst.make @@ Names.Name.mk_name n ],
        Constrexpr.Default Glob_term.Explicit,
        ty )
  in
  let arguments = List.map f arguments in
  List.fold_right
    (fun arg body -> Constrexpr_ops.mkLambdaCN [ arg ] body)
    arguments body

(* https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/termutils/funutils.ml *)
let rec lambda_to_prod (trm : Constrexpr.constr_expr) =
  match trm.v with
  | Constrexpr.CLambdaN (binder, body) ->
      Constrexpr_ops.mkProdCN binder (lambda_to_prod body)
  | _ -> trm

(** Given a module application [F (A) (B) (C)] return [F] *)
let rec extract_functor_name (name : Constrexpr.module_ast) =
  match name.v with
  | Constrexpr.CMident name -> name
  | CMapply (name, _) -> extract_functor_name name
  | CMwith (name, _) -> extract_functor_name name

let extract_handler_types_from_principle ~(inductive : VernacInductive.t)
    ~(principles : (Names.Id.t list * Constrexpr.constr_expr) RecursorStore.t) :
    Recursors.t =
  let all_names = inductive |> VernacInductive.extract_all_names in
  let compile_one_recursor _suffix (inductive_names, recursor) =
    (* Future-proofing for mutually inductive types *)
    let relevant_cstrs =
      inductive_names |> List.concat_map (fun n -> List.assoc n all_names)
    in
    let handlers =
      (* Copied from FPOP almost verbatim: *)
      let from_recursor_type_to_subcase_handlers_constructor
          (cstname : Names.Id.t list) (recursor : Constrexpr.constr_expr) :
          (Names.Id.t * Constrexpr.constr_expr) list =
        let open Constrexpr in
        let open Constrexpr_ops in
        let isArrow { CAst.v = t; _ } =
          match t with CNotation (_, (_, "_ -> _"), _) -> true | _ -> false
        in
        let destDepProd { CAst.v = t; _ } =
          match t with
          | CProdN (al, b) -> (al, b)
          | _ -> Errors.fail ~info:"unexpected"
        in
        let destArrow { CAst.v = t; _ } =
          match t with
          | CNotation (_, (_, "_ -> _"), ([ domain; codomain ], _, _, _)) ->
              (domain, codomain)
          | _ -> Errors.fail ~info:"unreachable"
        in
        let _inputP, _body = destDepProd recursor in
        let rec collect_handler cstname f =
          match (cstname, f) with
          | _ :: t, f when isArrow f ->
              let currentT, remained_f = destArrow f in
              let ret, otherparts = collect_handler t remained_f in
              (ret, currentT :: otherparts)
          | [], f -> (f, [])
          | _, _ -> Errors.fail ~info:"unexpected"
        in
        let _, all_recursor_handlers = collect_handler cstname _body in
        let cst_name_corresponding_recursor_handlers_sig =
          List.combine cstname
            (* decorate each ai case with a _inputP *)
            (List.map
               (fun body -> mkLambdaCN _inputP body)
               all_recursor_handlers)
        in
        cst_name_corresponding_recursor_handlers_sig
      in
      from_recursor_type_to_subcase_handlers_constructor relevant_cstrs recursor
    in
    Recursor.{ inductive_names; recursor; handlers }
  in
  principles |> RecursorStore.mapi compile_one_recursor

let rec constants_in_econstr sigma e = 
  let constants = constants_in_econstr sigma in 
  let kind = EConstr.kind sigma e in 
  match kind with
  | Constr.Int _
  | Constr.Float _
  | Constr.Construct _
  | Constr.Ind _ 
  | Constr.Rel _ 
  | Constr.Var _
  | Constr.Meta _ 
  | Constr.Evar _ 
  | Constr.Sort _ -> []
  | Constr.Cast (a, _, c) -> constants a @ constants c
  | Constr.Prod (_, b, c) 
  | Constr.Lambda (_, b, c) -> constants b @ constants c
  | Constr.LetIn (_, a, b, c) -> constants a @ constants b @ constants c
  | Constr.App (a, b) -> 
     let b = 
       b 
       |> Array.to_list 
       |> List.concat_map constants 
     in 
     constants a @ b
  | Constr.Const (const, _) -> 
     let name = 
       const
       |> Names.Constant.to_string 
       |> Libnames.qualid_of_string
     in
     [name]
  | Constr.Array (_, a, b, c) ->
      let a = 
       a
       |> Array.to_list 
       |> List.concat_map constants 
      in
      a @ constants b @ constants c 
  | Constr.Case (_, _, pcms, ((_, p), _), Constr.NoInvert, c, bl) ->
     let constants_list x = 
       x
       |> Array.to_list 
       |> List.concat_map constants 
      in
      constants_list pcms @ constants p @ constants c @ constants_list (Array.map snd bl)
  | Constr.Case
       (_, _, pcms, ((_, p), _), Constr.CaseInvert { indices }, c, bl)  ->
     let constants_list x = 
       x
       |> Array.to_list 
       |> List.concat_map constants 
      in
      constants_list pcms @ constants p @ constants_list indices @ constants c @ constants_list (Array.map snd bl)     
  | Constr.Fix (_,(_lna,tl,bl))
  | Constr.CoFix (_,(_lna,tl,bl)) ->
     let constants x = 
       x
       |> Array.to_list 
       |> List.concat_map constants 
      in
      constants tl @ constants bl
  | Constr.Proj (_, _, c) -> constants c

let compute_partial_recursor_signature 
      ~context 
      ~(inductive_path: Libnames.qualid) =   
  let _inductive, recursors, _ =
    Env.Context.lookup_inductive_for_recursion ~name:inductive_path context
  in
  let suffix = RecKind.Rect in
  let Recursor.{ recursor; _ } = RecursorStore.find suffix recursors in  
  let open Constrexpr_ops in
  
  let is_P (c : Constrexpr.constr_expr) : bool = 
    let all_params, _ = collect_argument_and_ret_of_type recursor in 
    let (ps, _, _), _ = List.hd all_params in
    let {CAst.v = p; _} = List.hd ps in     
    let p =
      match p with 
      | Names.Name p -> p 
      | _ -> Errors.fail ~info:"compute_partial_recursor_signature: expected Names.Name" 
    in 
    match c with 
    | {CAst.v = CRef (c, _); _} when (Libnames.qualid_is_ident c) -> 
      let c = Libnames.qualid_basename c in p = c
    | _ -> false 
  in  
  
  let _option_decoration = 
    let _option = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "option" in
    fun t -> mkAppC (_option, [t])
  in

  let flipped_indrec_type = 
    let all_params, ret = collect_argument_and_ret_of_type recursor in 
    (* make the last parameter into the front *)
    let rec heads_tail (l) = 
      match l with 
      | [] -> Errors.fail ~info:"heads_tail: expected non empty list"
      | h :: [] -> ([], h) 
      | h :: t -> 
         let th, tt = heads_tail t in 
         (h::th, tt) 
    in 
    let heads_param, tail_param = heads_tail all_params in 
    let all_params = List.map fst @@ tail_param :: heads_param in 
    let res = List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) all_params ret in 
    res 
  in 

  let ind_rect_type = flipped_indrec_type in 
  (* then we flip the argument order in ind_rect_type
      s.t.  *)
  (* we replace the P t into option (P t) *)
  let replaced_ind_rect_type = 
    let rec replace_helper _ r =
      match r with
      | { CAst.v = (Constrexpr.CApp (f, _)) ; _ } as original 
          when (is_P f)  ->
          (* rename the  *)
        (_option_decoration original)
      | cn -> map_constr_expr_with_binders (fun _ _ -> ()) replace_helper () cn 
    in
    replace_helper () ind_rect_type
  in
  
  replaced_ind_rect_type
