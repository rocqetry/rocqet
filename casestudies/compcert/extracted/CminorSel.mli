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

val expr_rect :
    (ident -> 'a1) -> (condexpr -> expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (operation -> exprlist -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1)
    -> (nat -> 'a1) -> (external_function -> exprlist -> 'a1) -> (ident -> signature ->
    exprlist -> 'a1) -> (memory_chunk -> addressing -> exprlist -> 'a1) ->
    expr -> 'a1

val exprlist_rect :
       'a1 -> (expr -> exprlist -> 'a1 -> 'a1) -> exprlist -> 'a1

val condexpr_rect :
        (condition -> exprlist -> 'a1) -> (condexpr -> 'a1 -> condexpr -> 'a1
        -> condexpr -> 'a1 -> 'a1) -> (expr -> condexpr -> 'a1 -> 'a1) ->
        condexpr -> 'a1

val condexpr_condexpr_expr_exprlist_rect :
   (ident -> 'a1) -> (condexpr -> 'a3 -> expr -> 'a1 -> expr -> 'a1 ->
   'a1) -> (operation -> exprlist -> 'a2 -> 'a1) -> (expr -> 'a1 -> expr
   -> 'a1 -> 'a1) -> (nat -> 'a1) -> (external_function -> exprlist -> 'a2 -> 'a1) -> (ident ->
   signature -> exprlist -> 'a2 -> 'a1) -> (memory_chunk -> addressing -> exprlist ->
   'a2 -> 'a1) -> 'a2 -> (expr -> 'a1 -> exprlist -> 'a2 -> 'a2) -> (condition ->
   exprlist -> 'a2 -> 'a3) -> (condexpr -> 'a3 -> condexpr -> 'a3 ->
   condexpr -> 'a3 -> 'a3) -> (expr -> 'a1 -> condexpr -> 'a3 -> 'a3) ->
   condexpr -> 'a3

val exprlist_condexpr_expr_exprlist_rect :
   (ident -> 'a1) -> (condexpr -> 'a3 -> expr -> 'a1 -> expr -> 'a1 ->
   'a1) -> (operation -> exprlist -> 'a2 -> 'a1) -> (expr -> 'a1 -> expr
   -> 'a1 -> 'a1) -> (nat -> 'a1) -> (external_function -> exprlist -> 'a2 -> 'a1) -> (ident ->
   signature -> exprlist -> 'a2 -> 'a1) -> (memory_chunk -> addressing -> exprlist ->
   'a2 -> 'a1) -> 'a2 -> (expr -> 'a1 -> exprlist -> 'a2 -> 'a2) -> (condition ->
   exprlist -> 'a2 -> 'a3) -> (condexpr -> 'a3 -> condexpr -> 'a3 ->
   condexpr -> 'a3 -> 'a3) -> (expr -> 'a1 -> condexpr -> 'a3 -> 'a3) ->
   exprlist -> 'a2

val expr_condexpr_expr_exprlist_rect :
    (ident -> 'a1) -> (condexpr -> 'a3 -> expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (operation -> exprlist -> 'a2 -> 'a1) -> (expr -> 'a1 -> expr
    -> 'a1 -> 'a1) -> (nat -> 'a1) -> (external_function -> exprlist -> 'a2 -> 'a1) -> (ident ->
    signature -> exprlist -> 'a2 -> 'a1) -> (memory_chunk -> addressing -> exprlist ->
    'a2 -> 'a1) -> 'a2 -> (expr -> 'a1 -> exprlist -> 'a2 -> 'a2) -> (condition ->
    exprlist -> 'a2 -> 'a3) -> (condexpr -> 'a3 -> condexpr -> 'a3 ->
    condexpr -> 'a3 -> 'a3) -> (expr -> 'a1 -> condexpr -> 'a3 -> 'a3) ->
    expr -> 'a1

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

val stmt_rect :
   'a1 -> (ident -> expr -> 'a1) -> (stmt -> 'a1 -> stmt -> 'a1 -> 'a1) -> (expr
   option -> 'a1) -> (label -> stmt -> 'a1 -> 'a1) -> (label -> 'a1) -> (condexpr ->
   stmt -> 'a1 -> stmt -> 'a1 -> 'a1) -> (ident builtin_res -> external_function ->
   expr builtin_arg list -> 'a1) -> (ident option -> signature -> (expr, ident) sum -> exprlist -> 'a1) ->
   (signature -> (expr, ident) sum -> exprlist -> 'a1) -> (memory_chunk -> addressing -> exprlist -> expr
   -> 'a1) -> (stmt -> 'a1 -> 'a1) -> (nat -> 'a1) -> (stmt -> 'a1 -> 'a1) ->
   (exitexpr -> 'a1) -> stmt -> 'a1

type coq_function = { fn_sig : signature; fn_params : ident list;
                      fn_vars : ident list; fn_stackspace : coq_Z;
                      fn_body : stmt }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

val lift_expr : nat -> expr -> expr

val lift_exprlist : nat -> exprlist -> exprlist

val lift_condexpr : nat -> condexpr -> condexpr

val lift : expr -> expr
