open AST
open BinInt
open BinNums
open Cminor
open Coqlib
open Csharpminor
open Datatypes
open Errors
open Integers
open List0
open Maps
open Mergesort

module S = Csharpminor
module T = Cminor

type compilenv = coq_Z PTree.t

(** val var_addr : compilenv -> ident -> Cminor.expr **)

let var_addr cenv id =
  match PTree.get id cenv with
  | Some ofs -> Cminor.Econst (Oaddrstack (Ptrofs.repr ofs))
  | None -> Cminor.Econst (Oaddrsymbol (id, Ptrofs.zero))

(** val transl_constant : constant -> Cminor.constant **)

let transl_constantOintconst x =
      T.Ointconst x

    (** val transl_constantOfloatconst : float -> __motiveTtransl_constant **)

    let transl_constantOfloatconst x =
      T.Ofloatconst x

    (** val transl_constantOsingleconst : float32 -> __motiveTtransl_constant **)

    let transl_constantOsingleconst x =
      T.Osingleconst x

    (** val transl_constantOlongconst : Int64.int -> __motiveTtransl_constant **)

    let transl_constantOlongconst x =
      T.Olongconst x

    (** val transl_constant : S.__internal_constant -> __motiveTtransl_constant **)

    let transl_constant =
      S.constant_rect transl_constantOintconst transl_constantOfloatconst
        transl_constantOsingleconst transl_constantOlongconst



(** val transl_expr : compilenv -> expr -> Cminor.expr res **)

let transl_exprEvar id _ =
   OK (T.Evar id)

    (** val transl_exprEconst : S.constant -> __motiveTtransl_expr **)

let transl_exprEconst c _ =
 OK (T.Econst (transl_constant c))

    (** val transl_exprEunop :
        unary_operation -> S.expr -> __motiveTtransl_expr -> __motiveTtransl_expr **)

let transl_exprEunop op _ transl_expr_e1 arg =
  bind (transl_expr_e1 arg) (fun te1 -> OK (T.Eunop (op, te1)))

    (** val transl_exprEbinop :
        binary_operation -> S.expr -> __motiveTtransl_expr -> S.expr ->
        __motiveTtransl_expr -> __motiveTtransl_expr **)

let transl_exprEbinop op _ transl_expr_e1 _ transl_expr_e2 arg =
      bind (transl_expr_e1 arg) (fun te1 ->
        bind (transl_expr_e2 arg) (fun te2 -> OK (T.Ebinop (op, te1, te2))))

    (** val transl_exprEaddrof : ident -> __motiveTtransl_expr **)

let transl_exprEaddrof id arg =
      OK (var_addr arg id)

    (** val transl_exprEload :
        memory_chunk -> S.expr -> __motiveTtransl_expr -> __motiveTtransl_expr **)

 let transl_exprEload chunk _ transl_expr_e arg =
      bind (transl_expr_e arg) (fun te -> OK (T.Eload (chunk, te)))

    (** val transl_expr : S.__internal_expr -> __motiveTtransl_expr **)

let transl_expr =
      S.expr_rect transl_exprEvar transl_exprEconst transl_exprEunop
        transl_exprEbinop transl_exprEaddrof transl_exprEload
let transl_expr cenv e = transl_expr e cenv

(** val transl_exprlist : compilenv -> expr list -> Cminor.expr list res **)

let rec transl_exprlist cenv = function
| [] -> OK []
| e1 :: e2 ->
  (match transl_expr cenv e1 with
   | OK x ->
     (match transl_exprlist cenv e2 with
      | OK x0 -> OK (x :: x0)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)

type exit_env = bool list

(** val shift_exit : exit_env -> nat -> nat **)

let rec shift_exit e n =
  match e with
  | [] -> n
  | b :: e' ->
    if b
    then (match n with
          | O -> O
          | S m -> S (shift_exit e' m))
    else S (shift_exit e' n)

(** val switch_table : lbl_stmt -> nat -> (coq_Z * nat) list * nat **)

(*
let rec switch_table ls k =
  match ls with
  | LSnil -> ([], k)
  | LScons (o, _, rem) ->
    (match o with
     | Some ni ->
       let (tbl, dfl) = switch_table rem (S k) in (((ni, k) :: tbl), dfl)
     | None -> let (tbl, _) = switch_table rem (S k) in (tbl, k)) *)

let switch_tableLSnil k = ([], k)

    (** val switch_tableLScons :
        coq_Z option -> S.stmt -> S.lbl_stmts -> __motiveTswitch_table ->
        __motiveTswitch_table **)

let switch_tableLScons lbl _ _ switch_table_rem k =
  match lbl with
  | Some ni ->
     let (tbl, dfl) = switch_table_rem (S k) in
     (((ni, k) :: tbl), dfl)    
  | None ->
    let (tbl, _) = switch_table_rem (S k) in (tbl, k)

let switch_table =
  S.lbl_stmts_rect switch_tableLSnil switch_tableLScons

(** val switch_env : lbl_stmt -> exit_env -> exit_env **)

let switch_envLSnil e = e

    (** val switch_envLScons :
        coq_Z option -> S.stmt -> S.lbl_stmts -> __motiveTswitch_env ->
        __motiveTswitch_env **)

let switch_envLScons _ _ _ switch_env_ls' e =
      false :: (switch_env_ls' e)

    (** val switch_env : S.__internal_lbl_stmts -> __motiveTswitch_env **)

let switch_env =
   S.lbl_stmts_rect switch_envLSnil switch_envLScons

(** val transl_stmt : compilenv -> exit_env -> stmt -> Cminor.stmt res **)

let transl_lbl_stmt_transl_stmtSskip _ = OK T.Sskip

    (** val transl_lbl_stmt_transl_stmtSassign :
        ident -> S.expr -> __motiveTtransl_stmt **)

let transl_lbl_stmt_transl_stmtSassign id e (cenv, xenv) =
      bind (transl_expr cenv e) (fun te -> OK (T.Sassign (id, te)))

    (** val transl_lbl_stmt_transl_stmtSseq :
        S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt ->
        __motiveTtransl_stmt **)

let transl_lbl_stmt_transl_stmtSseq _ transl_stmt_s1 _ transl_stmt_s2 arg =
      bind (transl_stmt_s1 arg) (fun ts1 ->
        bind (transl_stmt_s2 arg) (fun ts2 -> OK (T.Sseq (ts1, ts2))))

    (** val transl_lbl_stmt_transl_stmtSreturn :
        S.expr option -> __motiveTtransl_stmt **)

let transl_lbl_stmt_transl_stmtSreturn e (cenv, xenv) =
      match e with
      | Some e0 ->
        bind (transl_expr cenv e0) (fun te -> OK (T.Sreturn (Some te)))
      | None -> OK (T.Sreturn None)

    (** val transl_lbl_stmt_transl_stmtSlabel :
        S.label -> S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSlabel lbl _ transl_stmt_s arg =
      bind (transl_stmt_s arg) (fun ts -> OK (T.Slabel (lbl, ts)))

    (** val transl_lbl_stmt_transl_stmtSgoto : S.label -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSgoto lbl _ =
      OK (T.Sgoto lbl)

    (** val transl_lbl_stmt_transl_stmtSifthenelse :
        S.expr -> S.stmt -> __motiveTtransl_stmt -> S.stmt -> __motiveTtransl_stmt
        -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSifthenelse e _ transl_stmt_s1 _ transl_stmt_s2 (cenv, xenv) =
      bind (transl_expr cenv e) (fun te ->
        bind (transl_stmt_s1 (cenv, xenv)) (fun ts1 ->
          bind (transl_stmt_s2 (cenv, xenv)) (fun ts2 -> OK (T.Sifthenelse (te, ts1, ts2)))))

    (** val transl_lbl_stmt_transl_stmtLSnil : __motiveTtransl_lbl_stmt **)

    let transl_lbl_stmt_transl_stmtLSnil _ body =
      OK (T.Sseq ((T.Sblock body), T.Sskip))

    (** val transl_lbl_stmt_transl_stmtLScons :
        coq_Z option -> S.stmt -> __motiveTtransl_stmt -> S.lbl_stmts ->
        __motiveTtransl_lbl_stmt -> __motiveTtransl_lbl_stmt **)

    let transl_lbl_stmt_transl_stmtLScons _ _ transl_stmt_s _ transl_lbl_stmt_ls' (cenv, xenv) body =
      bind (transl_stmt_s (cenv, xenv)) (fun ts ->
        transl_lbl_stmt_ls' (cenv, tl xenv)
          (T.Sseq ((T.Sblock body), ts)))

    (** val transl_lbl_stmt_transl_stmtSexit : nat -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSexit n (cenv, xenv) =
      OK (T.Sexit (shift_exit xenv n))

    (** val transl_lbl_stmt_transl_stmtSloop :
        S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSloop _ transl_stmt_body arg =
      bind (transl_stmt_body arg) (fun ts -> OK (T.Sloop ts))

    (** val transl_lbl_stmt_transl_stmtSblock :
        S.stmt -> __motiveTtransl_stmt -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSblock _ transl_stmt_body (cenv, xenv) =
      bind
        (transl_stmt_body (cenv, true :: xenv)) (fun ts -> OK (T.Sblock ts))

    (** val transl_lbl_stmt_transl_stmtSswitch :
        bool -> S.expr -> S.lbl_stmts -> __motiveTtransl_lbl_stmt ->
        __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSswitch long e ls transl_lbl_stmt_ls (cenv, xenv) =
      let (tbl, dfl) = switch_table ls O in
      bind (transl_expr cenv e) (fun te ->
        transl_lbl_stmt_ls (cenv, switch_env ls xenv)
          (T.Sswitch (long, te, tbl, dfl)))

    (** val transl_lbl_stmt_transl_stmtSbuiltin :
        ident option -> external_function -> S.expr list -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSbuiltin optid ef el (cenv, _) =
      bind (transl_exprlist cenv el) (fun tel -> OK (T.Sbuiltin (optid, ef, tel)))

    (** val transl_lbl_stmt_transl_stmtSstore :
        memory_chunk -> S.expr -> S.expr -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtSstore chunk e1 e2 (cenv, xenv) =
      bind (transl_expr cenv e1) (fun te1 ->
        bind (transl_expr cenv e2) (fun te2 -> OK (T.Sstore (chunk, te1, te2))))

    (** val transl_lbl_stmt_transl_stmtScall :
        ident option -> signature -> S.expr -> S.expr list -> __motiveTtransl_stmt **)

    let transl_lbl_stmt_transl_stmtScall optid sig0 e el (cenv, xenv) =
      bind (transl_expr cenv e) (fun te ->
        bind (transl_exprlist cenv el) (fun tel -> OK
          (T.Scall (optid, sig0, te, tel))))

    (** val transl_stmt : S.__internal_stmt -> __motiveTtransl_stmt **)

    let _transl_stmt =
      S.stmt_lbl_stmts_stmt_rect transl_lbl_stmt_transl_stmtSskip
        transl_lbl_stmt_transl_stmtSassign transl_lbl_stmt_transl_stmtSseq
        transl_lbl_stmt_transl_stmtSreturn transl_lbl_stmt_transl_stmtSlabel
        transl_lbl_stmt_transl_stmtSgoto transl_lbl_stmt_transl_stmtSifthenelse
        transl_lbl_stmt_transl_stmtSbuiltin transl_lbl_stmt_transl_stmtScall
        transl_lbl_stmt_transl_stmtSstore transl_lbl_stmt_transl_stmtSblock
        transl_lbl_stmt_transl_stmtSloop transl_lbl_stmt_transl_stmtSexit
        transl_lbl_stmt_transl_stmtSswitch transl_lbl_stmt_transl_stmtLSnil
        transl_lbl_stmt_transl_stmtLScons



(** val block_alignment : coq_Z -> coq_Z **)

let block_alignment sz =
  if zlt sz (Zpos (Coq_xO Coq_xH))
  then Zpos Coq_xH
  else if zlt sz (Zpos (Coq_xO (Coq_xO Coq_xH)))
       then Zpos (Coq_xO Coq_xH)
       else if zlt sz (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
            then Zpos (Coq_xO (Coq_xO Coq_xH))
            else Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))

(** val assign_variable :
    (compilenv * coq_Z) -> (ident * coq_Z) -> compilenv * coq_Z **)

let assign_variable cenv_stacksize = function
| (id, sz) ->
  let (cenv, stacksize) = cenv_stacksize in
  let ofs = align stacksize (block_alignment sz) in
  ((PTree.set id ofs cenv), (Z.add ofs (Z.max Z0 sz)))

(** val assign_variables :
    (compilenv * coq_Z) -> (ident * coq_Z) list -> compilenv * coq_Z **)

let assign_variables cenv_stacksize vars =
  fold_left assign_variable vars cenv_stacksize

module VarOrder =
 struct
  type t = ident * coq_Z

  (** val leb : t -> t -> bool **)

  let leb v1 v2 =
    (fun x -> x) (zle (snd v1) (snd v2))
 end

module VarSort = Sort(VarOrder)

(** val build_compilenv : coq_function -> compilenv * coq_Z **)

let build_compilenv f =
  assign_variables (PTree.empty, Z0) (VarSort.sort f.fn_vars)

(** val transl_funbody :
    compilenv -> coq_Z -> coq_function -> Cminor.coq_function res **)

let transl_stmt = _transl_stmt

let transl_funbody cenv stacksize f =
  match _transl_stmt f.fn_body (cenv, [])  with
  | OK x ->
    OK { Cminor.fn_sig = f.fn_sig; Cminor.fn_params = f.fn_params;
      Cminor.fn_vars = f.fn_temps; fn_stackspace = stacksize;
      Cminor.fn_body = x }
  | Error msg0 -> Error msg0

(** val transl_function : coq_function -> Cminor.coq_function res **)

let transl_function f =
  let (cenv, stacksize) = build_compilenv f in
  if zle stacksize Ptrofs.max_unsigned
  then transl_funbody cenv stacksize f
  else Error
         (msg
           ('C'::('m'::('i'::('n'::('o'::('r'::('g'::('e'::('n'::(':'::(' '::('t'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('l'::('o'::('c'::('a'::('l'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::(','::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::(' '::('e'::('x'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val transl_fundef : fundef -> Cminor.fundef res **)

let transl_fundef f =
  transf_partial_fundef transl_function f

(** val transl_program : program -> Cminor.program res **)

let transl_program p =
  transform_partial_program transl_fundef p
