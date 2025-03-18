open AST
open BinNums
open Cminor
open Datatypes
open Floats
open Integers

type constant =
| Ointconst of Int.int
| Ofloatconst of float
| Osingleconst of float32
| Olongconst of Int64.int

let constant_rect f f0 f1 f2 = function
    | Ointconst i -> f i
    | Ofloatconst f3 -> f0 f3
    | Osingleconst f3 -> f1 f3
    | Olongconst i -> f2 i

type unary_operation = Cminor.unary_operation

type binary_operation = Cminor.binary_operation

type expr =
| Evar of ident
| Eaddrof of ident
| Econst of constant
| Eunop of unary_operation * expr
| Ebinop of binary_operation * expr * expr
| Eload of memory_chunk * expr

let rec expr_rect f f0 f1 f2 f3 f4 = function
| Evar i -> f i
| Econst c -> f0 c
| Eunop (u, __i0) ->
  f1 u __i0 (expr_rect f f0 f1 f2 f3 f4 __i0)
| Ebinop (b, __i0, __i1) ->
  f2 b __i0 (expr_rect f f0 f1 f2 f3 f4 __i0) __i1
    (expr_rect f f0 f1 f2 f3 f4 __i1)
| Eaddrof i -> f3 i
| Eload (m, __i0) ->
  f4 m __i0 (expr_rect f f0 f1 f2 f3 f4 __i0)

type label = ident

type stmt =
| Sskip
| Sset of ident * expr
| Sstore of memory_chunk * expr * expr
| Scall of ident option * signature * expr * expr list
| Sbuiltin of ident option * external_function * expr list
| Sseq of stmt * stmt
| Sifthenelse of expr * stmt * stmt
| Sloop of stmt
| Sblock of stmt
| Sexit of nat
| Sswitch of bool * expr * lbl_stmt
| Sreturn of expr option
| Slabel of label * stmt
| Sgoto of label
and lbl_stmt =
| LSnil
| LScons of coq_Z option * stmt * lbl_stmt

let rec stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Sskip -> f
| Sset (i, e) -> f0 i e
| Sseq (__i0, __i1) ->
  f1 __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
    __i1 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i1)
| Sreturn o -> f2 o
| Slabel (l, __i0) ->
  f3 l __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
| Sgoto l -> f4 l
| Sifthenelse (e, __i0, __i1) ->
  f5 e __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
    __i1 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i1)
| Sbuiltin (o, e, l) -> f6 o e l
| Scall (o, s, e, l) -> f7 o s e l
| Sstore (m, e, e0) -> f8 m e e0
| Sblock __i0 ->
  f9 __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
| Sloop __i0 ->
  f10 __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
| Sexit n -> f11 n
| Sswitch (b, e, __i0) -> f12 b e __i0

let rec lbl_stmts_rect f f0 = function
    | LSnil -> f
    | LScons (o, __i0, __i1) ->
      f0 o __i0 __i1 (lbl_stmts_rect f f0 __i1)

let lbl_stmts_lbl_stmts_stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 =
      let rec f15 = function
      | Sskip -> f
      | Sset (i, e) -> f0 i e
      | Sseq (__i0, __i1) -> f1 __i0 (f15 __i0) __i1 (f15 __i1)
      | Sreturn o -> f2 o
      | Slabel (l, __i0) -> f3 l __i0 (f15 __i0)
      | Sgoto l -> f4 l
      | Sifthenelse (e, __i0, __i1) ->
        f5 e __i0 (f15 __i0) __i1 (f15 __i1)
      | Sbuiltin (o, e, l) -> f6 o e l
      | Scall (o, s, e, l) -> f7 o s e l
      | Sstore (m, e, e0) -> f8 m e e0
      | Sblock __i0 -> f9 __i0 (f15 __i0)
      | Sloop __i0 -> f10 __i0 (f15 __i0)
      | Sexit n -> f11 n
      | Sswitch (b, e, __i0) -> f12 b e __i0 (f16 __i0)
      and f16 = function
      | LSnil -> f13
      | LScons (o, __i0, __i1) ->
        f14 o __i0 (f15 __i0) __i1 (f16 __i1)
      in f16

let stmt_lbl_stmts_stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 =
      let rec f15 = function
      | Sskip -> f
      | Sset (i, e) -> f0 i e
      | Sseq (__i0, __i1) -> f1 __i0 (f15 __i0) __i1 (f15 __i1)
      | Sreturn o -> f2 o
      | Slabel (l, __i0) -> f3 l __i0 (f15 __i0)
      | Sgoto l -> f4 l
      | Sifthenelse (e, __i0, __i1) ->
        f5 e __i0 (f15 __i0) __i1 (f15 __i1)
      | Sbuiltin (o, e, l) -> f6 o e l
      | Scall (o, s, e, l) -> f7 o s e l
      | Sstore (m, e, e0) -> f8 m e e0
      | Sblock __i0 -> f9 __i0 (f15 __i0)
      | Sloop __i0 -> f10 __i0 (f15 __i0)
      | Sexit n -> f11 n
      | Sswitch (b, e, __i0) -> f12 b e __i0 (f16 __i0)
      and f16 = function
      | LSnil -> f13
      | LScons (o, __i0, __i1) ->
        f14 o __i0 (f15 __i0) __i1 (f16 __i1)
      in f15

type coq_function = { fn_sig : signature; fn_params : ident list;
                      fn_vars : (ident * coq_Z) list; fn_temps : ident list;
                      fn_body : stmt }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program
