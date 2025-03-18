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

val instruction_rect :
    (operation -> mreg list -> mreg -> 'a1) -> (condition -> mreg list -> label -> 'a1) -> (label -> 'a1) -> (label -> 'a1)
    -> 'a1 -> (slot -> coq_Z -> typ -> mreg -> 'a1) -> (mreg -> slot -> coq_Z -> typ -> 'a1) -> (external_function -> loc
    builtin_arg list -> mreg builtin_res -> 'a1) -> (signature -> (mreg, ident) sum -> 'a1) -> (signature -> (mreg, ident)
    sum -> 'a1) -> (mreg -> label list -> 'a1) -> (memory_chunk -> addressing -> mreg list -> mreg -> 'a1) -> (memory_chunk
    -> addressing -> mreg list -> mreg -> 'a1) -> instruction -> 'a1

type code = instruction list

type coq_function = { fn_sig : signature; fn_stacksize : coq_Z; fn_code : code }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program
