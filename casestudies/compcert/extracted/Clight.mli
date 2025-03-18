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

val expr_rect :
        (Int.int -> coq_type -> 'a1) -> (float -> coq_type -> 'a1) -> (float32 ->
        coq_type -> 'a1) -> (Int64.int -> coq_type -> 'a1) -> (ident -> coq_type ->
        'a1) -> (coq_type -> coq_type -> 'a1) -> (expr -> 'a1 ->
        coq_type -> 'a1) -> (coq_type -> coq_type -> 'a1) -> (unary_operation
        -> expr -> 'a1 -> coq_type -> 'a1) -> (binary_operation ->
        expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) ->
        (ident -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1)
        -> (expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1
        -> ident -> coq_type -> 'a1) -> expr -> 'a1

val typeof : expr -> coq_type

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

val lbl_stmts_lbl_stmts_stmt_rect :
        'a1 -> (ident -> expr -> 'a1) -> (statement -> 'a1 -> statement
        -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> statement -> 'a1
        -> 'a1) -> (expr option -> 'a1) -> (label -> statement -> 'a1 -> 'a1)
        -> (label -> 'a1) -> (ident option -> external_function -> coq_type list ->
        expr list -> 'a1) -> (ident option -> expr -> expr list -> 'a1) -> (expr ->
        expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1)
        -> 'a1 -> 'a1 -> (expr -> labeled_statements -> 'a2 -> 'a1) -> 'a2 ->
        (coq_Z option -> statement -> 'a1 -> labeled_statements -> 'a2 ->
        'a2) -> labeled_statements -> 'a2 

val stmt_lbl_stmts_stmt_rect :
        'a1 -> (ident -> expr -> 'a1) -> (statement -> 'a1 -> statement
        -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> statement -> 'a1
        -> 'a1) -> (expr option -> 'a1) -> (label -> statement -> 'a1 -> 'a1)
        -> (label -> 'a1) -> (ident option -> external_function -> coq_type list ->
        expr list -> 'a1) -> (ident option -> expr -> expr list -> 'a1) -> (expr ->
        expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1)
        -> 'a1 -> 'a1 -> (expr -> labeled_statements -> 'a2 -> 'a1) -> 'a2 ->
        (coq_Z option -> statement -> 'a1 -> labeled_statements -> 'a2 ->
        'a2) -> statement -> 'a1

val stmt_rect :
        'a1 -> (ident -> expr -> 'a1) -> (statement -> 'a1 -> statement
        -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> statement -> 'a1
        -> 'a1) -> (expr option -> 'a1) -> (label -> statement -> 'a1 -> 'a1)
        -> (label -> 'a1) -> (ident option -> external_function -> coq_type list ->
        expr list -> 'a1) -> (ident option -> expr -> expr list -> 'a1) -> (expr ->
        expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1)
        -> 'a1 -> 'a1 -> (expr -> labeled_statements -> 'a1) -> statement
        -> 'a1

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list;
                      fn_temps : (ident * coq_type) list; fn_body : statement }

val var_names : (ident * coq_type) list -> ident list

type fundef = coq_function Ctypes.fundef

val type_of_function : coq_function -> coq_type

type program = coq_function Ctypes.program
