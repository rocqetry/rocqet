(* From https://github.com/tlringer/plugin-tutorial/blob/main/src/termutils.ml *)

(** Get the global environment *)
let global_env () =
  let env = Global.env () in
  (Evd.from_env env, env)

(** When you first start using a plugin, if you want to manipulate terms
 in an interesting way, you need to move from the external representation
 of terms to the internal representation of terms. This does that for you. *)
let internalize env trm sigma = Constrintern.interp_constr_evars env sigma trm

let ident_to_module_expr ident = CAst.make (Constrexpr.CMident ident)

let apply_module ~(functor_expr : Constrexpr.module_ast)
    ~(arguments : Libnames.qualid list) : Constrexpr.module_ast =
  let open Constrexpr in
  List.fold_left
    (fun op x -> CAst.make (CMapply (op, x)))
    functor_expr arguments
