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

val constant_rect :
        (Int.int -> 'a1) -> (float -> 'a1) -> (float32 -> 'a1) -> (Int64.int ->
        'a1) -> constant -> 'a1

type unary_operation = Cminor.unary_operation

type binary_operation = Cminor.binary_operation

type expr =
| Evar of ident
| Eaddrof of ident
| Econst of constant
| Eunop of unary_operation * expr
| Ebinop of binary_operation * expr * expr
| Eload of memory_chunk * expr

val expr_rect :
        (ident -> 'a1) -> (constant -> 'a1) -> (unary_operation -> expr
        -> 'a1 -> 'a1) -> (binary_operation -> expr -> 'a1 ->
        expr -> 'a1 -> 'a1) -> (ident -> 'a1) -> (memory_chunk ->
        expr -> 'a1 -> 'a1) -> expr -> 'a1

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

val stmt_rect :
   'a1 -> (ident -> expr -> 'a1) -> (stmt -> 'a1 -> stmt
   -> 'a1 -> 'a1) -> (expr option -> 'a1) -> (label -> stmt -> 'a1
   -> 'a1) -> (label -> 'a1) -> (expr -> stmt -> 'a1 ->
   stmt -> 'a1 -> 'a1) -> (ident option -> external_function ->
   expr list -> 'a1) -> (ident option -> signature -> expr -> expr list ->
   'a1) -> (memory_chunk -> expr -> expr -> 'a1) -> (stmt -> 'a1 ->
   'a1) -> (stmt -> 'a1 -> 'a1) -> (nat -> 'a1) -> (bool -> expr ->
   lbl_stmt -> 'a1) -> stmt -> 'a1

val lbl_stmts_rect :
        'a1 -> (coq_Z option -> stmt -> lbl_stmt -> 'a1 ->
        'a1) -> lbl_stmt -> 'a1

val lbl_stmts_lbl_stmts_stmt_rect :
        'a1 -> (ident -> expr -> 'a1) -> (stmt -> 'a1 -> stmt
        -> 'a1 -> 'a1) -> (expr option -> 'a1) -> (label -> stmt -> 'a1
        -> 'a1) -> (label -> 'a1) -> (expr -> stmt -> 'a1 ->
        stmt -> 'a1 -> 'a1) -> (ident option -> external_function ->
        expr list -> 'a1) -> (ident option -> signature -> expr -> expr list ->
        'a1) -> (memory_chunk -> expr -> expr -> 'a1) -> (stmt -> 'a1 ->
        'a1) -> (stmt -> 'a1 -> 'a1) -> (nat -> 'a1) -> (bool -> expr ->
        lbl_stmt -> 'a2 -> 'a1) -> 'a2 -> (coq_Z option ->
        stmt -> 'a1 -> lbl_stmt -> 'a2 -> 'a2) ->
        lbl_stmt -> 'a2

val stmt_lbl_stmts_stmt_rect :
        'a1 -> (ident -> expr -> 'a1) -> (stmt -> 'a1 -> stmt
        -> 'a1 -> 'a1) -> (expr option -> 'a1) -> (label -> stmt -> 'a1
        -> 'a1) -> (label -> 'a1) -> (expr -> stmt -> 'a1 ->
        stmt -> 'a1 -> 'a1) -> (ident option -> external_function ->
        expr list -> 'a1) -> (ident option -> signature -> expr -> expr list ->
        'a1) -> (memory_chunk -> expr -> expr -> 'a1) -> (stmt -> 'a1 ->
        'a1) -> (stmt -> 'a1 -> 'a1) -> (nat -> 'a1) -> (bool -> expr ->
        lbl_stmt -> 'a2 -> 'a1) -> 'a2 -> (coq_Z option ->
        stmt -> 'a1 -> lbl_stmt -> 'a2 -> 'a2) ->
        stmt -> 'a1

type coq_function = { fn_sig : signature; fn_params : ident list;
                      fn_vars : (ident * coq_Z) list; fn_temps : ident list;
                      fn_body : stmt }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program
