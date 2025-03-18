open AST
open BinNums
open Datatypes
open Locations
open Machregs
open Maps
open Op

type node = positive

type instruction =
| Lop of operation * mreg list * mreg
| Lload of memory_chunk * addressing * mreg list * mreg
| Lgetstack of slot * coq_Z * typ * mreg
| Lsetstack of mreg * slot * coq_Z * typ
| Lstore of memory_chunk * addressing * mreg list * mreg
| Lcall of signature * (mreg, ident) sum
| Ltailcall of signature * (mreg, ident) sum
| Lbuiltin of external_function * loc builtin_arg list * mreg builtin_res
| Lbranch of node
| Lcond of condition * mreg list * node * node
| Ljumptable of mreg * node list
| Lreturn

val instruction_rect :
  (operation -> mreg list -> mreg -> 'a1) ->
  (slot -> coq_Z -> typ -> mreg -> 'a1) ->
  (mreg -> slot -> coq_Z -> typ -> 'a1) ->
  (node -> 'a1) ->
  (condition -> mreg list -> node -> node -> 'a1) -> 'a1 ->
  (signature -> (mreg, ident) sum -> 'a1) ->
  (signature -> (mreg, ident) sum -> 'a1) ->
  (mreg -> node list -> 'a1) ->
  (memory_chunk -> addressing -> mreg list -> mreg -> 'a1) ->
  (memory_chunk -> addressing -> mreg list -> mreg -> 'a1) ->
  (AST.external_function ->
            Locations.loc AST.builtin_arg list ->
            Machregs.mreg AST.builtin_res -> 'a1) ->
        instruction -> 'a1 


type bblock = instruction list

type code = bblock PTree.t

type coq_function = { fn_sig : signature; fn_stacksize : coq_Z;
                      fn_code : code; fn_entrypoint : node }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

val destroyed_by_getstack : slot -> mreg list

val successors_block : bblock -> node list
