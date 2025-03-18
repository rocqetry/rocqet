open AST
open BinNums
open Datatypes
open Locations
open Machregs
open Op

type label = positive

type instruction =
| Lgetstack of slot * coq_Z * typ * mreg
| Lsetstack of mreg * slot * coq_Z * typ
| Lop of operation * mreg list * mreg
| Lload of memory_chunk * addressing * mreg list * mreg
| Lstore of memory_chunk * addressing * mreg list * mreg
| Lcall of signature * (mreg, ident) sum
| Ltailcall of signature * (mreg, ident) sum
| Lbuiltin of external_function * loc builtin_arg list * mreg builtin_res
| Llabel of label
| Lgoto of label
| Lcond of condition * mreg list * label
| Ljumptable of mreg * label list
| Lreturn

let instruction_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Lop (o, l, m) -> f o l m
    | Lcond (c, l, l0) -> f0 c l l0
    | Llabel l -> f1 l
    | Lgoto l -> f2 l
    | Lreturn -> f3
    | Lgetstack (s, z, t0, m) -> f4 s z t0 m
    | Lsetstack (m, s, z, t0) -> f5 m s z t0
    | Lbuiltin (e, l, b) -> f6 e l b
    | Lcall (s, s0) -> f7 s s0
    | Ltailcall (s, s0) -> f8 s s0
    | Ljumptable (m, l) -> f9 m l
    | Lload (m, a, l, m0) -> f10 m a l m0
    | Lstore (m, a, l, m0) -> f11 m a l m0

type code = instruction list

type coq_function = { fn_sig : signature; fn_stacksize : coq_Z; fn_code : code }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program
