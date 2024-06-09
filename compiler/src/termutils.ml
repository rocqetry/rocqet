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

let ident_to_module_expr ident = CAst.make (Constrexpr.CMident ident)

let apply_module ~(functor_expr : Constrexpr.module_ast)
    ~(arguments : Libnames.qualid list) : Constrexpr.module_ast =
  let open Constrexpr in
  List.fold_left
    (fun op x -> CAst.make (CMapply (op, x)))
    functor_expr arguments
