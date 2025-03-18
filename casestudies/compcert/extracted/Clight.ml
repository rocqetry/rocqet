open AST
open BinNums
open Cop
open Ctypes
open Floats
open Integers
open List0

type expr =
| Econst_int of Int.int * coq_type
| Econst_float of float * coq_type
| Econst_single of float32 * coq_type
| Econst_long of Int64.int * coq_type
| Evar of ident * coq_type
| Etempvar of ident * coq_type
| Ederef of expr * coq_type
| Eaddrof of expr * coq_type
| Eunop of unary_operation * expr * coq_type
| Ebinop of binary_operation * expr * expr * coq_type
| Ecast of expr * coq_type
| Efield of expr * ident * coq_type
| Esizeof of coq_type * coq_type
| Ealignof of coq_type * coq_type

let rec expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
    | Econst_int (i, t) -> f i t
    | Econst_float (f13, t) -> f0 f13 t
    | Econst_single (f13, t) -> f1 f13 t
    | Econst_long (i, t) -> f2 i t
    | Etempvar (i, t) -> f3 i t
    | Esizeof (t, t0) -> f4 t t0
    | Ecast (__i0, t) ->
      f5 __i0
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0) t
    | Ealignof (t, t0) -> f6 t t0
    | Eunop (u, __i0, t) ->
      f7 u __i0
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0) t
    | Ebinop (b, __i0, __i1, t) ->
      f8 b __i0
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
        __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i1) t
    | Evar (i, t) -> f9 i t
    | Ederef (__i0, t) ->
      f10 __i0
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0) t
    | Eaddrof (__i0, t) ->
      f11 __i0
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0) t
    | Efield (__i0, i, t) ->
      f12 __i0
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0) i t
       
let typeof = function
| Econst_int (_, ty) -> ty
| Econst_float (_, ty) -> ty
| Econst_single (_, ty) -> ty
| Econst_long (_, ty) -> ty
| Evar (_, ty) -> ty
| Etempvar (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty

(*
let typeofEconst_int _ ty =
  ty
let typeofEconst_float _ ty =
  ty
let typeofEconst_single _ ty =
  ty
let typeofEconst_long _ ty =
  ty
let typeofEtempvar _ ty =
  ty
let typeofEsizeof _ ty =
  ty
let typeofEalignof _ ty =
  ty
let typeofEcast _ _ ty =
  ty
let typeofEunop _ _ _ ty =
  ty
let typeofEbinop _ _ _ _ _ ty =
  ty
let typeofEaddrof _ _ t =
  t
let typeofEderef _ _ t =
  t
let typeofEvar _ t =
  t
let typeofEfield _ _ _ ty =
  ty

let typeof =
  expr_rect typeofEconst_int typeofEconst_float typeofEconst_single
    typeofEconst_long typeofEtempvar typeofEsizeof typeofEcast typeofEalignof
    typeofEunop typeofEbinop typeofEvar typeofEderef typeofEaddrof typeofEfield *)

type label = ident

type statement =
| Sskip
| Sassign of expr * expr
| Sset of ident * expr
| Scall of ident option * expr * expr list
| Sbuiltin of ident option * external_function * coq_type list * expr list
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Sloop of statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of coq_Z option * statement * labeled_statements

let rec stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Sskip -> f
| Sset (i, e) -> f0 i e
| Ssequence (__i0, __i1) ->
  f1 __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
    __i1 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i1)
| Sifthenelse (e, __i0, __i1) ->
  f2 e __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
    __i1 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i1)
| Sreturn o -> f3 o
| Slabel (l, __i0) ->
  f4 l __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
| Sgoto l -> f5 l
| Sbuiltin (o, e, l, l0) -> f6 o e l l0
| Scall (o, e, l) -> f7 o e l
| Sassign (e, e0) -> f8 e e0
| Sloop (__i0, __i1) ->
  f9 __i0
    (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i0)
    __i1 (stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 __i1)
| Sbreak -> f10
| Scontinue -> f11
| Sswitch (e, __i0) -> f12 e __i0

let lbl_stmts_lbl_stmts_stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 =
  let rec f15 = function
  | Sskip -> f
  | Sset (i, e) -> f0 i e
  | Ssequence (__i0, __i1) -> f1 __i0 (f15 __i0) __i1 (f15 __i1)
  | Sifthenelse (e, __i0, __i1) ->
    f2 e __i0 (f15 __i0) __i1 (f15 __i1)
  | Sreturn o -> f3 o
  | Slabel (l, __i0) -> f4 l __i0 (f15 __i0)
  | Sgoto l -> f5 l
  | Sbuiltin (o, e, l, l0) -> f6 o e l l0
  | Scall (o, e, l) -> f7 o e l
  | Sassign (e, e0) -> f8 e e0
  | Sloop (__i0, __i1) -> f9 __i0 (f15 __i0) __i1 (f15 __i1)
  | Sbreak -> f10
  | Scontinue -> f11
  | Sswitch (e, __i0) -> f12 e __i0 (f16 __i0)
  and f16 = function
  | LSnil -> f13
  | LScons (o, __i0, __i1) ->
    f14 o __i0 (f15 __i0) __i1 (f16 __i1)
  in f16

  let stmt_lbl_stmts_stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 =
    let rec f15 = function
    | Sskip -> f
    | Sset (i, e) -> f0 i e
    | Ssequence (__i0, __i1) -> f1 __i0 (f15 __i0) __i1 (f15 __i1)
    | Sifthenelse (e, __i0, __i1) ->
      f2 e __i0 (f15 __i0) __i1 (f15 __i1)
    | Sreturn o -> f3 o
    | Slabel (l, __i0) -> f4 l __i0 (f15 __i0)
    | Sgoto l -> f5 l
    | Sbuiltin (o, e, l, l0) -> f6 o e l l0
    | Scall (o, e, l) -> f7 o e l
    | Sassign (e, e0) -> f8 e e0
    | Sloop (__i0, __i1) -> f9 __i0 (f15 __i0) __i1 (f15 __i1)
    | Sbreak -> f10
    | Scontinue -> f11
    | Sswitch (e, __i0) -> f12 e __i0 (f16 __i0)
    and f16 = function
    | LSnil -> f13
    | LScons (o, __i0, __i1) ->
      f14 o __i0 (f15 __i0) __i1 (f16 __i1)
    in f15

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list;
                      fn_temps : (ident * coq_type) list; fn_body : statement }

(** val var_names : (ident * coq_type) list -> ident list **)

let var_names vars =
  map fst vars

type fundef = coq_function Ctypes.fundef

(** val type_of_function : coq_function -> coq_type **)

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)

type program = coq_function Ctypes.program
