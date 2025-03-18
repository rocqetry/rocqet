open AST
open BinNums
open Cminor
open Compare_dec
open Datatypes
open Op

type expr =
| Evar of ident
| Eop of operation * exprlist
| Eload of memory_chunk * addressing * exprlist
| Econdition of condexpr * expr * expr
| Elet of expr * expr
| Eletvar of nat
| Ebuiltin of external_function * exprlist
| Eexternal of ident * signature * exprlist
and exprlist =
| Enil
| Econs of expr * exprlist
and condexpr =
| CEcond of condition * exprlist
| CEcondition of condexpr * condexpr * condexpr
| CElet of expr * condexpr

let rec expr_rect f f0 f1 f2 f3 f4 f5 f6 = function
    | Evar i -> f i
    | Econdition (__i0, __i1, __i2) ->
      f0 __i0 __i1 (expr_rect f f0 f1 f2 f3 f4 f5 f6 __i1) __i2
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 __i2)
    | Eop (o, __i0) -> f1 o __i0
    | Elet (__i0, __i1) ->
      f2 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 __i1)
    | Eletvar n -> f3 n
    | Ebuiltin (e, __i0) -> f4 e __i0
    | Eexternal (i, s, __i0) -> f5 i s __i0
    | Eload (m, a, __i0) -> f6 m a __i0

 let rec exprlist_rect f f0 = function
    | Enil -> f
    | Econs (__i0, __i1) -> f0 __i0 __i1 (exprlist_rect f f0 __i1)

 let rec condexpr_rect f f0 f1 = function
    | CEcond (c, __i0) -> f c __i0
    | CEcondition (__i0, __i1, __i2) ->
      f0 __i0 (condexpr_rect f f0 f1 __i0) __i1 (condexpr_rect f f0 f1 __i1) __i2
        (condexpr_rect f f0 f1 __i2)
    | CElet (__i0, __i1) -> f1 __i0 __i1 (condexpr_rect f f0 f1 __i1)

 (* for cond *)

 let condexpr_condexpr_expr_exprlist_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =
      let rec f12 = function
      | Evar i -> f i
      | Econdition (__i0, __i1, __i2) -> f0 __i0 (f14 __i0) __i1 (f12 __i1) __i2 (f12 __i2)
      | Eop (o, __i0) -> f1 o __i0 (f13 __i0)
      | Elet (__i0, __i1) -> f2 __i0 (f12 __i0) __i1 (f12 __i1)
      | Eletvar n -> f3 n
      | Ebuiltin (e, __i0) -> f4 e __i0 (f13 __i0)
      | Eexternal (i, s, __i0) -> f5 i s __i0 (f13 __i0)
      | Eload (m, a, __i0) -> f6 m a __i0 (f13 __i0)
      and f13 = function
      | Enil -> f7
      | Econs (__i0, __i1) -> f8 __i0 (f12 __i0) __i1 (f13 __i1)
      and f14 = function
      | CEcond (c, __i0) -> f9 c __i0 (f13 __i0)
      | CEcondition (__i0, __i1, __i2) -> f10 __i0 (f14 __i0) __i1 (f14 __i1) __i2 (f14 __i2)
      | CElet (__i0, __i1) -> f11 __i0 (f12 __i0) __i1 (f14 __i1)
      in f14

 (* for exprlist *)
let exprlist_condexpr_expr_exprlist_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =
      let rec f12 = function
      | Evar i -> f i
      | Econdition (__i0, __i1, __i2) -> f0 __i0 (f14 __i0) __i1 (f12 __i1) __i2 (f12 __i2)
      | Eop (o, __i0) -> f1 o __i0 (f13 __i0)
      | Elet (__i0, __i1) -> f2 __i0 (f12 __i0) __i1 (f12 __i1)
      | Eletvar n -> f3 n
      | Ebuiltin (e, __i0) -> f4 e __i0 (f13 __i0)
      | Eexternal (i, s, __i0) -> f5 i s __i0 (f13 __i0)
      | Eload (m, a, __i0) -> f6 m a __i0 (f13 __i0)
      and f13 = function
      | Enil -> f7
      | Econs (__i0, __i1) -> f8 __i0 (f12 __i0) __i1 (f13 __i1)
      and f14 = function
      | CEcond (c, __i0) -> f9 c __i0 (f13 __i0)
      | CEcondition (__i0, __i1, __i2) -> f10 __i0 (f14 __i0) __i1 (f14 __i1) __i2 (f14 __i2)
      | CElet (__i0, __i1) -> f11 __i0 (f12 __i0) __i1 (f14 __i1)
      in f13

(* for expr *)

let expr_condexpr_expr_exprlist_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =
      let rec f12 = function
      | Evar i -> f i
      | Econdition (__i0, __i1, __i2) -> f0 __i0 (f14 __i0) __i1 (f12 __i1) __i2 (f12 __i2)
      | Eop (o, __i0) -> f1 o __i0 (f13 __i0)
      | Elet (__i0, __i1) -> f2 __i0 (f12 __i0) __i1 (f12 __i1)
      | Eletvar n -> f3 n
      | Ebuiltin (e, __i0) -> f4 e __i0 (f13 __i0)
      | Eexternal (i, s, __i0) -> f5 i s __i0 (f13 __i0)
      | Eload (m, a, __i0) -> f6 m a __i0 (f13 __i0)
      and f13 = function
      | Enil -> f7
      | Econs (__i0, __i1) -> f8 __i0 (f12 __i0) __i1 (f13 __i1)
      and f14 = function
      | CEcond (c, __i0) -> f9 c __i0 (f13 __i0)
      | CEcondition (__i0, __i1, __i2) -> f10 __i0 (f14 __i0) __i1 (f14 __i1) __i2 (f14 __i2)
      | CElet (__i0, __i1) -> f11 __i0 (f12 __i0) __i1 (f14 __i1)
      in f12

type exitexpr =
| XEexit of nat
| XEjumptable of expr * nat list
| XEcondition of condexpr * exitexpr * exitexpr
| XElet of expr * exitexpr

type stmt =
| Sskip
| Sassign of ident * expr
| Sstore of memory_chunk * addressing * exprlist * expr
| Scall of ident option * signature * (expr, ident) sum * exprlist
| Stailcall of signature * (expr, ident) sum * exprlist
| Sbuiltin of ident builtin_res * external_function * expr builtin_arg list
| Sseq of stmt * stmt
| Sifthenelse of condexpr * stmt * stmt
| Sloop of stmt
| Sblock of stmt
| Sexit of nat
| Sswitch of exitexpr
| Sreturn of expr option
| Slabel of label * stmt
| Sgoto of label

let rec stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
    | Sskip -> f
    | Sassign (i, e) -> f0 i e
    | Sseq (__i0, __i1) ->
      f1 __i0 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i0) __i1
        (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i1)
    | Sreturn o -> f2 o
    | Slabel (l, __i0) ->
      f3 l __i0 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i0)
    | Sgoto l -> f4 l
    | Sifthenelse (c, __i0, __i1) ->
      f5 c __i0 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i0) __i1
        (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i1)
    | Sbuiltin (b, e, l) -> f6 b e l
    | Scall (o, s, s0, e) -> f7 o s s0 e
    | Stailcall (s, s0, e) -> f8 s s0 e
    | Sstore (m, a, e, e0) -> f9 m a e e0
    | Sblock __i0 ->
      f10 __i0 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i0)
    | Sexit n -> f11 n
    | Sloop __i0 ->
      f12 __i0 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 __i0)
    | Sswitch e -> f13 e

type coq_function = { fn_sig : signature; fn_params : ident list;
                      fn_vars : ident list; fn_stackspace : coq_Z;
                      fn_body : stmt }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

(** val lift_expr : nat -> expr -> expr **)

let rec lift_expr p = function
| Evar id -> Evar id
| Eop (op, bl) -> Eop (op, (lift_exprlist p bl))
| Eload (chunk, addr, bl) -> Eload (chunk, addr, (lift_exprlist p bl))
| Econdition (a0, b, c) ->
  Econdition ((lift_condexpr p a0), (lift_expr p b), (lift_expr p c))
| Elet (b, c) -> Elet ((lift_expr p b), (lift_expr (S p) c))
| Eletvar n -> if le_gt_dec p n then Eletvar (S n) else Eletvar n
| Ebuiltin (ef, bl) -> Ebuiltin (ef, (lift_exprlist p bl))
| Eexternal (id, sg, bl) -> Eexternal (id, sg, (lift_exprlist p bl))

(** val lift_exprlist : nat -> exprlist -> exprlist **)

and lift_exprlist p = function
| Enil -> Enil
| Econs (b, cl) -> Econs ((lift_expr p b), (lift_exprlist p cl))

(** val lift_condexpr : nat -> condexpr -> condexpr **)

and lift_condexpr p = function
| CEcond (c, al) -> CEcond (c, (lift_exprlist p al))
| CEcondition (a0, b, c) ->
  CEcondition ((lift_condexpr p a0), (lift_condexpr p b), (lift_condexpr p c))
| CElet (a0, b) -> CElet ((lift_expr p a0), (lift_condexpr (S p) b))

(** val lift : expr -> expr **)

let lift a =
  lift_expr O a
