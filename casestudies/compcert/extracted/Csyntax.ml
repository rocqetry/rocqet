open AST
open BinNums
open Cop
open Ctypes
open Integers
open List0
open Values

type expr =
| Eval of coq_val * coq_type
| Evar of ident * coq_type
| Efield of expr * ident * coq_type
| Evalof of expr * coq_type
| Ederef of expr * coq_type
| Eaddrof of expr * coq_type
| Eunop of unary_operation * expr * coq_type
| Ebinop of binary_operation * expr * expr * coq_type
| Ecast of expr * coq_type
| Eseqand of expr * expr * coq_type
| Eseqor of expr * expr * coq_type
| Econdition of expr * expr * expr * coq_type
| Esizeof of coq_type * coq_type
| Ealignof of coq_type * coq_type
| Eassign of expr * expr * coq_type
| Eassignop of binary_operation * expr * expr * coq_type * coq_type
| Epostincr of incr_or_decr * expr * coq_type
| Ecomma of expr * expr * coq_type
| Ecall of expr * exprlist * coq_type
| Ebuiltin of external_function * coq_type list * exprlist * coq_type
| Eloc of block * Ptrofs.int * bitfield * coq_type
| Eparen of expr * coq_type * coq_type
and exprlist =
| Enil
| Econs of expr * exprlist

(** val coq_Eindex : expr -> expr -> coq_type -> expr **)

let coq_Eindex r1 r2 ty =
  Ederef ((Ebinop (Oadd, r1, r2, (Tpointer (ty, noattr)))), ty)

(** val coq_Epreincr : incr_or_decr -> expr -> coq_type -> expr **)

let coq_Epreincr id l ty =
  Eassignop ((match id with
              | Incr -> Oadd
              | Decr -> Osub), l, (Eval ((Vint Int.one), type_int32s)),
    (typeconv ty), ty)

(** val coq_Eselection : expr -> expr -> expr -> coq_type -> expr **)

let coq_Eselection r1 r2 r3 ty =
  let t = inj_type (typ_of_type ty) in
  let sg = { sig_args = (Xint :: (t :: (t :: []))); sig_res = t; sig_cc =
    cc_default }
  in
  Ebuiltin ((EF_builtin
  (('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('s'::('e'::('l'::[]))))))))))))),
  sg)), (type_bool :: (ty :: (ty :: []))), (Econs (r1, (Econs (r2, (Econs
  (r3, Enil)))))), ty)

(** val typeof : expr -> coq_type **)

let rec expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 = function
    | Eval (v, t) -> f v t
    | Evar (i, t) -> f0 i t
    | Ecast (__i0, t) -> f1 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t
    | Eseqand (__i0, __i1, t) ->
      f2 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) t
    | Eseqor (__i0, __i1, t) ->
      f3 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) t
    | Econdition (__i0, __i1, __i2, t) ->
      f4 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) __i2
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i2) t
    | Esizeof (t, t0) -> f5 t t0
    | Ealignof (t, t0) -> f6 t t0
    | Ecomma (__i0, __i1, t) ->
      f7 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) t
    | Eparen (__i0, t, t0) -> f8 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t t0
    | Eunop (u, __i0, t) -> f9 u __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t
    | Ebinop (b, __i0, __i1, t) ->
      f10 b __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) t
    | Ebuiltin (e, l, __i0, t) -> f11 e l __i0 t
    | Ecall (__i0, __i1, t) -> f12 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1 t
    | Eloc (b, i, b0, t) -> f13 b i b0 t
    | Epostincr (i, __i0, t) -> f14 i __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t
    | Eassignop (b, __i0, __i1, t, t0) ->
      f15 b __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) t t0
    | Eaddrof (__i0, t) -> f16 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t
    | Ederef (__i0, t) -> f17 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t
    | Evalof (__i0, t) -> f18 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) t
    | Eassign (__i0, __i1, t) ->
      f19 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) __i1
        (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i1) t
    | Efield (__i0, i, t) -> f20 __i0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 __i0) i t

let rec exprlist_rect f f0 = function
    | Enil -> f
    | Econs (__i0, __i1) -> f0 __i0 __i1 (exprlist_rect f f0 __i1)

let exprlist_expr_exprlist_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 =
      let rec f23 = function
      | Eval (v, t) -> f v t
      | Evar (i, t) -> f0 i t
      | Ecast (__i0, t) -> f1 __i0 (f23 __i0) t
      | Eseqand (__i0, __i1, t) -> f2 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Eseqor (__i0, __i1, t) -> f3 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Econdition (__i0, __i1, __i2, t) -> f4 __i0 (f23 __i0) __i1 (f23 __i1) __i2 (f23 __i2) t
      | Esizeof (t, t0) -> f5 t t0
      | Ealignof (t, t0) -> f6 t t0
      | Ecomma (__i0, __i1, t) -> f7 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Eparen (__i0, t, t0) -> f8 __i0 (f23 __i0) t t0
      | Eunop (u, __i0, t) -> f9 u __i0 (f23 __i0) t
      | Ebinop (b, __i0, __i1, t) -> f10 b __i0 (f23 __i0) __i1 (f23 __i1) t
      | Ebuiltin (e, l, __i0, t) -> f11 e l __i0 (f24 __i0) t
      | Ecall (__i0, __i1, t) -> f12 __i0 (f23 __i0) __i1 (f24 __i1) t
      | Eloc (b, i, b0, t) -> f13 b i b0 t
      | Epostincr (i, __i0, t) -> f14 i __i0 (f23 __i0) t
      | Eassignop (b, __i0, __i1, t, t0) -> f15 b __i0 (f23 __i0) __i1 (f23 __i1) t t0
      | Eaddrof (__i0, t) -> f16 __i0 (f23 __i0) t
      | Ederef (__i0, t) -> f17 __i0 (f23 __i0) t
      | Evalof (__i0, t) -> f18 __i0 (f23 __i0) t
      | Eassign (__i0, __i1, t) -> f19 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Efield (__i0, i, t) -> f20 __i0 (f23 __i0) i t
      and f24 = function
      | Enil -> f21
      | Econs (__i0, __i1) -> f22 __i0 (f23 __i0) __i1 (f24 __i1)
      in f24

let expr_expr_exprlist_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 =
      let rec f23 = function
      | Eval (v, t) -> f v t
      | Evar (i, t) -> f0 i t
      | Ecast (__i0, t) -> f1 __i0 (f23 __i0) t
      | Eseqand (__i0, __i1, t) -> f2 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Eseqor (__i0, __i1, t) -> f3 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Econdition (__i0, __i1, __i2, t) -> f4 __i0 (f23 __i0) __i1 (f23 __i1) __i2 (f23 __i2) t
      | Esizeof (t, t0) -> f5 t t0
      | Ealignof (t, t0) -> f6 t t0
      | Ecomma (__i0, __i1, t) -> f7 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Eparen (__i0, t, t0) -> f8 __i0 (f23 __i0) t t0
      | Eunop (u, __i0, t) -> f9 u __i0 (f23 __i0) t
      | Ebinop (b, __i0, __i1, t) -> f10 b __i0 (f23 __i0) __i1 (f23 __i1) t
      | Ebuiltin (e, l, __i0, t) -> f11 e l __i0 (f24 __i0) t
      | Ecall (__i0, __i1, t) -> f12 __i0 (f23 __i0) __i1 (f24 __i1) t
      | Eloc (b, i, b0, t) -> f13 b i b0 t
      | Epostincr (i, __i0, t) -> f14 i __i0 (f23 __i0) t
      | Eassignop (b, __i0, __i1, t, t0) -> f15 b __i0 (f23 __i0) __i1 (f23 __i1) t t0
      | Eaddrof (__i0, t) -> f16 __i0 (f23 __i0) t
      | Ederef (__i0, t) -> f17 __i0 (f23 __i0) t
      | Evalof (__i0, t) -> f18 __i0 (f23 __i0) t
      | Eassign (__i0, __i1, t) -> f19 __i0 (f23 __i0) __i1 (f23 __i1) t
      | Efield (__i0, i, t) -> f20 __i0 (f23 __i0) i t
      and f24 = function
      | Enil -> f21
      | Econs (__i0, __i1) -> f22 __i0 (f23 __i0) __i1 (f24 __i1)
      in f23

(*
let typeof = function
| Eval (_, ty) -> ty
| Evar (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Evalof (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Eseqand (_, _, ty) -> ty
| Eseqor (_, _, ty) -> ty
| Econdition (_, _, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty
| Eassign (_, _, ty) -> ty
| Eassignop (_, _, _, _, ty) -> ty
| Epostincr (_, _, ty) -> ty
| Ecomma (_, _, ty) -> ty
| Ecall (_, _, ty) -> ty
| Ebuiltin (_, _, _, ty) -> ty
| Eloc (_, _, _, ty) -> ty
| Eparen (_, _, ty) -> ty *)

let typeofEval _ ty =
      ty

    (** val typeofEvar : ident -> coq_type -> __motiveTtypeof **)

    let typeofEvar _ ty =
      ty

    (** val typeofEcast : expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEcast _ _ ty =
      ty

    (** val typeofEseqand : expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEseqand _ _ _ _ ty =
      ty

    (** val typeofEseqor : expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEseqor _ _ _ _ ty =
      ty

    (** val typeofEcondition : expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEcondition _ _ _ _ _ _ ty =
      ty

    (** val typeofEsizeof : coq_type -> coq_type -> __motiveTtypeof **)

    let typeofEsizeof _ ty =
      ty

    (** val typeofEalignof : coq_type -> coq_type -> __motiveTtypeof **)

    let typeofEalignof _ ty =
      ty

    (** val typeofEcomma : expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEcomma _ _ _ _ ty =
      ty

    (** val typeofEparen : expr -> __motiveTtypeof -> coq_type -> coq_type -> __motiveTtypeof **)

    let typeofEparen _ _ _ ty =
      ty

    (** val typeofEunop : unary_operation -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEunop _ _ _ ty =
      ty

    (** val typeofEbinop : binary_operation -> expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEbinop _ _ _ _ _ ty =
      ty

    (** val typeofEbuiltin : external_function -> coq_type list -> exprlist -> coq_type -> __motiveTtypeof **)

    let typeofEbuiltin _ _ _ ty =
      ty

    (** val typeofEassign : expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEassign _ _ _ _ ty =
      ty

    (** val typeofEvalof : expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEvalof _ _ ty =
      ty

    (** val typeofEderef : expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEderef _ _ ty =
      ty

    (** val typeofEaddrof : expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEaddrof _ _ ty =
      ty

    (** val typeofEassignop : binary_operation -> expr -> __motiveTtypeof -> expr -> __motiveTtypeof -> coq_type -> coq_type -> __motiveTtypeof **)

    let typeofEassignop _ _ _ _ _ _ ty =
      ty

    (** val typeofEpostincr : incr_or_decr -> expr -> __motiveTtypeof -> coq_type -> __motiveTtypeof **)

    let typeofEpostincr _ _ _ ty =
      ty

    (** val typeofEloc : block -> Ptrofs.int -> bitfield -> coq_type -> __motiveTtypeof **)

    let typeofEloc _ _ _ ty =
      ty

    (** val typeofEfield : expr -> __motiveTtypeof -> ident -> coq_type -> __motiveTtypeof **)

    let typeofEfield _ _ _ ty =
      ty

    (** val typeofEcall : expr -> __motiveTtypeof -> exprlist -> coq_type -> __motiveTtypeof **)

    let typeofEcall _ _ _ t =
      t

    (** val typeof : __internal_expr -> __motiveTtypeof **)

    let typeof =
      expr_rect typeofEval typeofEvar typeofEcast typeofEseqand typeofEseqor typeofEcondition typeofEsizeof typeofEalignof typeofEcomma typeofEparen typeofEunop
        typeofEbinop typeofEbuiltin typeofEcall typeofEloc typeofEpostincr typeofEassignop typeofEaddrof typeofEderef typeofEvalof typeofEassign typeofEfield

type label = ident

type statement =
| Sskip
| Sdo of expr
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Swhile of expr * statement
| Sdowhile of expr * statement
| Sfor of statement * expr * statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of coq_Z option * statement * labeled_statements

let stmt_lbl_stmts_stmt_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 =
      let rec f14 = function
      | Ssequence (__i0, __i1) -> f __i0 (f14 __i0) __i1 (f14 __i1)
      | Sskip -> f0
      | Sdo e -> f1 e
      | Sifthenelse (e, __i0, __i1) -> f2 e __i0 (f14 __i0) __i1 (f14 __i1)
      | Sreturn o -> f3 o
      | Slabel (l, __i0) -> f4 l __i0 (f14 __i0)
      | Sgoto l -> f5 l
      | Sfor (__i0, e, __i1, __i2) -> f6 __i0 (f14 __i0) e __i1 (f14 __i1) __i2 (f14 __i2)
      | Sdowhile (e, __i0) -> f7 e __i0 (f14 __i0)
      | Swhile (e, __i0) -> f8 e __i0 (f14 __i0)
      | Sbreak -> f9
      | Scontinue -> f10
      | Sswitch (e, __i0) -> f11 e __i0 (f15 __i0)
      and f15 = function
      | LSnil -> f12
      | LScons (o, __i0, __i1) -> f13 o __i0 (f14 __i0) __i1 (f15 __i1)
      in f14

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list; fn_body : statement }

(** val var_names : (ident * coq_type) list -> ident list **)

let var_names vars =
  map fst vars

type fundef = coq_function Ctypes.fundef

(** val type_of_function : coq_function -> coq_type **)

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)

(** val type_of_fundef : fundef -> coq_type **)

let type_of_fundef = function
| Internal fd -> type_of_function fd
| External (_, args, res, cc) -> Tfunction (args, res, cc)

type program = coq_function Ctypes.program
