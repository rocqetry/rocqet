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

let instruction_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
    | Lop (o, l, m) -> f o l m
    | Lgetstack (s, z, t0, m) -> f0 s z t0 m
    | Lsetstack (m, s, z, t0) -> f1 m s z t0
    | Lbranch n -> f2 n
    | Lcond (c, l, n, n0) -> f3 c l n n0
    | Lreturn -> f4
    | Lcall (s, s0) -> f5 s s0
    | Ltailcall (s, s0) -> f6 s s0
    | Ljumptable (m, l) -> f7 m l
    | Lload (m, a, l, m0) -> f8 m a l m0
    | Lstore (m, a, l, m0) -> f9 m a l m0
    | Lbuiltin (ef, args, res) -> f10 ef args res

type bblock = instruction list

type code = bblock PTree.t

type coq_function = { fn_sig : signature; fn_stacksize : coq_Z;
                      fn_code : code; fn_entrypoint : node }

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

(** val destroyed_by_getstack : slot -> mreg list **)

let destroyed_by_getstack = function
| Incoming -> temp_for_parent_frame :: []
| _ -> []

(** val successors_block : bblock -> node list **)

let successors_instrLop _ _ _ rest =
      rest

    (** val successors_instrLgetstack :
        slot -> coq_Z -> typ -> mreg -> __motiveTsuccessors_instr **)

    let successors_instrLgetstack _ _ _ _ rest =
      rest

    (** val successors_instrLsetstack :
        mreg -> slot -> coq_Z -> typ -> __motiveTsuccessors_instr **)

    let successors_instrLsetstack _ _ _ _ rest =
      rest

    (** val successors_instrLbranch : node -> __motiveTsuccessors_instr **)

    let successors_instrLbranch s _ =
      s :: []      

    (** val successors_instrLcond :
        condition -> mreg list -> node -> node -> __motiveTsuccessors_instr **)

    let successors_instrLcond _ _ s1 s2 _ =
       s1 :: (s2 :: [])      

    (** val successors_instrLreturn : __motiveTsuccessors_instr **)

    let successors_instrLreturn rest =
      rest

    (** val successors_instrLload :
        memory_chunk -> addressing -> mreg list -> mreg -> __motiveTsuccessors_instr **)

    let successors_instrLload _ _ _ _ rest =
      rest

    (** val successors_instrLstore :
        memory_chunk -> addressing -> mreg list -> mreg -> __motiveTsuccessors_instr **)

    let successors_instrLstore _ _ _ _ rest =
      rest

    (** val successors_instrLjumptable :
        mreg -> node list -> __motiveTsuccessors_instr **)

    let successors_instrLjumptable _ tbl _ =
      tbl

    (** val successors_instrLcall :
        signature -> (mreg, ident) sum -> __motiveTsuccessors_instr **)

    let successors_instrLcall _ _ rest =
      rest

    (** val successors_instrLtailcall :
        signature -> (mreg, ident) sum -> __motiveTsuccessors_instr **)

    let successors_instrLtailcall _ _ rest =
      rest

    let successors_instrLbuiltin _  _ _ rest =
      rest

    (** val successors_instr :
        __internal_instruction -> __motiveTsuccessors_instr **)

    let successors_instr =
      instruction_rect successors_instrLop successors_instrLgetstack
        successors_instrLsetstack successors_instrLbranch successors_instrLcond
        successors_instrLreturn successors_instrLcall successors_instrLtailcall
        successors_instrLjumptable successors_instrLload successors_instrLstore successors_instrLbuiltin

    (** val successors_block : bblock -> node list **)

let rec successors_block = function
| [] -> []
| op :: b' -> successors_instr op (successors_block b')
