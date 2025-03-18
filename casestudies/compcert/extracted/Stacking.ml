open AST
open BinInt
open BinNums
open Bounds
open Coqlib
open Datatypes
open Errors
open Integers
open Linear
open Lineartyping
open List0
open Locations
open Mach
open Machregs
open Op
open Stacklayout

(** val offset_local : frame_env -> coq_Z -> coq_Z **)

let offset_local fe x =
  Z.add fe.fe_ofs_local (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) x)

(** val offset_arg : coq_Z -> coq_Z **)

let offset_arg x =
  Z.add fe_ofs_arg (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) x)

(** val save_callee_save_rec : mreg list -> coq_Z -> code -> code **)

let rec save_callee_save_rec rl ofs k =
  match rl with
  | [] -> k
  | r :: rl0 ->
    let ty = mreg_type r in
    let sz = AST.typesize ty in
    let ofs1 = align ofs sz in
    (Msetstack (r, (Ptrofs.repr ofs1),
    ty)) :: (save_callee_save_rec rl0 (Z.add ofs1 sz) k)

(** val save_callee_save : frame_env -> code -> code **)

let save_callee_save fe k =
  save_callee_save_rec fe.fe_used_callee_save fe.fe_ofs_callee_save k

(** val restore_callee_save_rec : mreg list -> coq_Z -> code -> code **)

let rec restore_callee_save_rec rl ofs k =
  match rl with
  | [] -> k
  | r :: rl0 ->
    let ty = mreg_type r in
    let sz = AST.typesize ty in
    let ofs1 = align ofs sz in
    (Mgetstack ((Ptrofs.repr ofs1), ty,
    r)) :: (restore_callee_save_rec rl0 (Z.add ofs1 sz) k)

(** val restore_callee_save : frame_env -> code -> code **)

let restore_callee_save fe k =
  restore_callee_save_rec fe.fe_used_callee_save fe.fe_ofs_callee_save k

(** val simplify_store : memory_chunk -> memory_chunk **)

let simplify_store chunk = match chunk with
| Mbool -> Mint8unsigned
| Mint8signed -> Mint8unsigned
| Mint16signed -> Mint16unsigned
| _ -> chunk

(** val simplify_load : memory_chunk -> memory_chunk **)

let simplify_load chunk = match chunk with
| Mbool -> Mint8unsigned
| _ -> chunk

(** val transl_op : frame_env -> operation -> operation **)

let transl_op fe op =
  shift_stack_operation fe.fe_stack_data op

(** val transl_addr : frame_env -> addressing -> addressing **)

let transl_addr fe addr =
  shift_stack_addressing fe.fe_stack_data addr

(** val transl_builtin_arg :
    frame_env -> loc builtin_arg -> mreg builtin_arg **)

let rec transl_builtin_arg fe = function
| BA x ->
  (match x with
   | R r -> BA r
   | S (sl, ofs, ty) ->
     (match sl with
      | Local ->
        BA_loadstack ((chunk_of_type ty), (Ptrofs.repr (offset_local fe ofs)))
      | _ -> BA_int Int.zero))
| BA_int n -> BA_int n
| BA_long n -> BA_long n
| BA_float n -> BA_float n
| BA_single n -> BA_single n
| BA_loadstack (chunk, ofs) ->
  BA_loadstack (chunk, (Ptrofs.add ofs (Ptrofs.repr fe.fe_stack_data)))
| BA_addrstack ofs ->
  BA_addrstack (Ptrofs.add ofs (Ptrofs.repr fe.fe_stack_data))
| BA_loadglobal (chunk, id, ofs) -> BA_loadglobal (chunk, id, ofs)
| BA_addrglobal (id, ofs) -> BA_addrglobal (id, ofs)
| BA_splitlong (hi, lo) ->
  BA_splitlong ((transl_builtin_arg fe hi), (transl_builtin_arg fe lo))
| BA_addptr (a1, a2) ->
  BA_addptr ((transl_builtin_arg fe a1), (transl_builtin_arg fe a2))

(** val transl_instr : frame_env -> Linear.instruction -> code -> code **)

module S = Linear
module T = Mach

(** val transl_instrLgetstack : slot -> coq_Z -> typ -> mreg -> __motiveTtransl_instr **)

 let transl_instrLgetstack sl ofs ty r fe k =
      match sl with
      | Local -> (T.Mgetstack ((Ptrofs.repr (offset_local fe ofs)), ty, r)) :: k
      | Incoming -> (T.Mgetparam ((Ptrofs.repr (offset_arg ofs)), ty, r)) ::  k
      | Outgoing -> (T.Mgetstack ((Ptrofs.repr (offset_arg ofs)), ty, r)) :: k

    (** val transl_instrLsetstack : mreg -> slot -> coq_Z -> typ -> __motiveTtransl_instr **)

    let transl_instrLsetstack r sl ofs ty fe k =
      match sl with
      | Local -> (T.Msetstack (r, (Ptrofs.repr (offset_local fe ofs)), ty)) :: k
      | Incoming -> k
      | Outgoing -> (T.Msetstack (r, (Ptrofs.repr (offset_arg ofs)), ty)) ::  k

    (** val transl_instrLop : operation -> mreg list -> mreg -> __motiveTtransl_instr **)

    let transl_instrLop op args res0 fe k =
      (T.Mop ((transl_op fe op), args, res0)) ::  k

    (** val transl_instrLlabel : S.label -> __motiveTtransl_instr **)

    let transl_instrLlabel lbl _ k =
      ((T.Mlabel lbl)) ::  k

    (** val transl_instrLgoto : S.label -> __motiveTtransl_instr **)

    let transl_instrLgoto lbl _ k =
      (T.Mgoto lbl) ::  k

    (** val transl_instrLcond : condition -> mreg list -> S.label -> __motiveTtransl_instr **)

    let transl_instrLcond cond args lbl _ k =
      (T.Mcond (cond, args, lbl)) :: k

    (** val transl_instrLreturn : __motiveTtransl_instr **)

    let transl_instrLreturn fe k =
      restore_callee_save fe (T.Mreturn ::  k)

    (** val transl_instrLbuiltin : external_function -> loc builtin_arg list -> mreg builtin_res -> __motiveTtransl_instr **)

    let transl_instrLbuiltin ef args dst fe k =
      (T.Mbuiltin (ef, (map (transl_builtin_arg fe) args), dst)) :: k

    (** val transl_instrLload : memory_chunk -> addressing -> mreg list -> mreg -> __motiveTtransl_instr **)

    let transl_instrLload chunk addr args dst fe k =
      (Mload ((simplify_load chunk), (transl_addr fe addr), args, dst)) :: k
      (*(T.Mload (chunk, (transl_addr fe addr), args, dst)) :: k*)

    (** val transl_instrLstore : memory_chunk -> addressing -> mreg list -> mreg -> __motiveTtransl_instr **)

    let transl_instrLstore chunk addr args src fe k =
      (Mstore ((simplify_store chunk), (transl_addr fe addr), args, src)) :: k
      (*(T.Mstore (chunk, (transl_addr fe addr), args, src)) :: k*)

    (** val transl_instrLjumptable : mreg -> S.label list -> __motiveTtransl_instr **)

    let transl_instrLjumptable arg tbl _ k =
      (T.Mjumptable (arg, tbl)) :: k

    (** val transl_instrLcall : signature -> (mreg, ident) sum -> __motiveTtransl_instr **)

    let transl_instrLcall sig0 ros _ k =
      (T.Mcall (sig0, ros)) ::  k

    (** val transl_instrLtailcall : signature -> (mreg, ident) sum -> __motiveTtransl_instr **)

    let transl_instrLtailcall sig0 ros fe k =
      restore_callee_save fe (T.Mtailcall (sig0, ros) :: k)

    (** val transl_instr : S.__internal_instruction -> __motiveTtransl_instr **)

    let transl_instr =
      S.instruction_rect transl_instrLop transl_instrLcond transl_instrLlabel transl_instrLgoto transl_instrLreturn
        transl_instrLgetstack transl_instrLsetstack transl_instrLbuiltin transl_instrLcall transl_instrLtailcall
        transl_instrLjumptable transl_instrLload transl_instrLstore

    let transl_instr fe i k = transl_instr i fe k

(** val transl_code : frame_env -> Linear.instruction list -> code **)

let transl_code fe il =
  list_fold_right (transl_instr fe) il []

(** val transl_body : Linear.coq_function -> frame_env -> code **)

let transl_body f fe =
  save_callee_save fe (transl_code fe f.Linear.fn_code)

(** val transf_function : Linear.coq_function -> coq_function res **)

let transf_function f =
  let fe = make_env (function_bounds f) in
  if negb (wt_function f)
  then Error
         (msg
           ('I'::('l'::('l'::('-'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('L'::('i'::('n'::('e'::('a'::('r'::(' '::('c'::('o'::('d'::('e'::[])))))))))))))))))))))))
  else if zlt Ptrofs.max_unsigned fe.fe_size
       then Error
              (msg
                ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('s'::('p'::('i'::('l'::('l'::('e'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::(','::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::(' '::('e'::('x'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))
       else OK { fn_sig = f.Linear.fn_sig; fn_code = (transl_body f fe);
              fn_stacksize = fe.fe_size; fn_link_ofs =
              (Ptrofs.repr fe.fe_ofs_link); fn_retaddr_ofs =
              (Ptrofs.repr fe.fe_ofs_retaddr) }

(** val transf_fundef : Linear.fundef -> fundef res **)

let transf_fundef f =
  transf_partial_fundef transf_function f

(** val transf_program : Linear.program -> program res **)

let transf_program p =
  transform_partial_program transf_fundef p
