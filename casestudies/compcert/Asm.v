From Rocqet Require Import Loader.

From Rocqet Require Import Coqlib.
From Rocqet Require Import Errors.
From Rocqet Require Import Values.
From Rocqet Require Import AST.
From Rocqet Require Import Integers.
From Rocqet Require Import Floats.
From Rocqet Require Import Memory.
From Rocqet Require Import Globalenvs.
From Rocqet Require Import Smallstep.
From Rocqet Require Import Events.
From Rocqet Require Import Maps.
From Rocqet Require Import Linking.
Require Import Rocqet.CompCert.lib.Ctypes.
From Rocqet Require Import Cop.
From Rocqet Require Import Mon.
From Rocqet Require Import Zbits.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From Rocqet Require Import Prelude.
From Rocqet Require Import Op.

Local Open Scope string_scope.
Local Open Scope list_scope.
Open Scope asm.

(* RISC-V *)
Trait RV.

Family Common.


MetaData offset.
Inductive offset : Type :=
| Ofsimm (ofs: ptrofs)
| Ofslow (id: ident) (ofs: ptrofs).
FEnd offset.

FDefinition label := positive.

FInductive instruction : Type :=
(* Pseudo-instructions *)
| Plabel : label -> instruction  (**r define a code label *)
| Pbtbl  : ireg -> list label -> instruction (**r N-way branch through a jump table *)
  (* Unconditional jumps.  Links are always to X1/RA. *)
| Pj_l : label -> instruction  (**r jump to label *)
| Pj_s : ident -> signature -> instruction     (**r jump to symbol *)
| Pj_r :  ireg -> signature -> instruction     (**r jump register *)
| Pjal_s : ident -> signature -> instruction    (**r jump-and-link symbol *)
| Pjal_r : ireg -> signature -> instruction     (**r jump-and-link register *)
| Pcfi_rel_offset : int -> instruction (**r .cfi_rel_offset debug directive *)
| Pallocframe : Z -> ptrofs -> instruction (**r allocate new stack frame *)
| Pfreeframe  : Z -> ptrofs -> instruction (**r deallocate stack frame and restore previous frame *)
| Ploadsymbol : ireg -> ident -> ptrofs -> instruction (**r load the address of a symbol *)
| Ploadsymbol_high : ireg -> ident -> ptrofs  -> instruction
| Pnop : instruction (**r nop instruction *)
| Pbuiltin: external_function -> list (builtin_arg preg)
     -> builtin_res preg -> instruction.    (**r built-in function (pseudo) *)

FDefinition code := list instruction.
MetaData function binds fn_sig, fn_code.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
FEnd function.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

(* Operational Semantics *)
FDefinition regset := Pregmap.t val.
FDefinition genv := Genv.t fundef unit.

Open Scope asm.

MetaData undef_regs.
Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
match l with
| nil => rs
| r :: l' => undef_regs l' (rs#r <- Vundef)
end.
FEnd undef_regs.

MetaData set_regs.
Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
match rl, vl with
| r1 :: rl', v1 :: vl' =>  set_regs rl' vl' (rs#r1 <- v1)
| _, _ => rs
end.
FEnd set_regs.

MetaData find_instr.
Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
match c with
| nil => None
| i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
end.
FEnd find_instr.

FRecursion is_label about instruction motive (fun (_ : instruction) => label -> bool) by _rect.
Case Plabel lbl' := (fun lbl => peq lbl lbl').
Case _ := (fun lbl => false).
FEnd is_label.

MetaData label_pos.
Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
match c with
| nil => None
| instr :: c' =>
  if is_label instr lbl then Some (pos + 1) else label_pos lbl (pos + 1) c'
end.
FEnd label_pos.

MetaData outcome binds Next, Stuck.
Inductive outcome: Type :=
| Next: regset -> mem -> outcome
| Stuck: outcome.
FEnd outcome.

FDefinition nextinstr := fun (rs: regset) =>
  Pregmap.set PC (Val.offset_ptr (rs PC) Ptrofs.one) rs.

FDefinition goto_label := fun (f: function) (lbl: label) (rs: regset) (m: mem) =>
match label_pos lbl 0 (fn_code f) with
| None => Stuck
| Some pos =>
    match (rs PC) with
    | Vptr b ofs => Next (Pregmap.set PC (Vptr b (Ptrofs.repr pos)) rs) m
    | _          => Stuck
    end
end.

MetaData low_half binds high_half.
Parameter low_half: genv -> ident -> ptrofs -> ptrofs.

Parameter high_half: genv -> ident -> ptrofs -> val.

Axiom low_high_half:
  forall ge id ofs,
  Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.
FEnd low_half.

FDefinition eval_offset : genv -> offset -> ptrofs := fun ge ofs =>
match ofs with
| self__Common.Ofsimm n => n
| self__Common.Ofslow id delta => low_half ge id delta
end.

FDefinition exec_load := fun (ge : genv) (chunk: memory_chunk) (rs: regset) (m: mem)
    (d: preg) (a: ireg) (ofs: offset) =>
match  Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ge ofs)) with
| None => Stuck
| Some v => Next (nextinstr (Pregmap.set d v rs)) m
end.

FDefinition exec_store := fun (ge : genv) (chunk: memory_chunk) (rs: regset) (m: mem)
  (s: preg) (a: ireg) (ofs: offset) =>
match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ge ofs)) (rs s) with
| None => Stuck
| Some m' => Next (nextinstr rs) m'
end.

FDefinition eval_branch := fun (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) =>
match res with
| Some true  => goto_label f l rs m
| Some false => Next (nextinstr rs) m
| None => Stuck
end.

FRecursion exec_instr about instruction motive (fun (_ : instruction) => genv -> function -> regset -> mem -> outcome) by _rect.
Case Plabel lbl := (fun ge f rs m => Next (nextinstr rs) m).
Case Pbtbl r tbl :=
(fun ge f rs m =>
  match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#X5 <- Vundef #X31 <- Vundef) m
          end
      | _ => Stuck
      end).
Case Pj_l lbl := (fun ge f rs m => goto_label f lbl rs m).
Case Pj_r r sg := (fun ge f rs m => Next (rs#PC <- (rs#r)) m).
Case Pj_s s sg := (fun ge f rs m =>  Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero) #X31 <- Vundef) m).
Case Pjal_s s sg :=
(fun ge f rs m =>
   Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)
         #RA <- (Val.offset_ptr rs#PC Ptrofs.one)) m).
Case Pjal_r r sg :=
(fun ge f rs m =>
    Next (rs#PC <- (rs#r)
          #RA <- (Val.offset_ptr rs#PC Ptrofs.one)) m).
(** The following instructions and directives are not generated directly by Asmgen,
    so we do not model them. *)
Case Pnop := (fun ge f rs m => Stuck).
Case Pbuiltin ef args res := (fun ge f rs m => Stuck). (**r treated specially below *)
Case Pcfi_rel_offset a := (fun ge f rs m =>   Next (nextinstr rs) m).
Case Pallocframe sz pos :=
(fun ge f rs m =>
   let (m1, stk) := Mem.alloc m 0 sz in
   let sp := (Vptr stk Ptrofs.zero) in
   match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
   | None => Stuck
   | Some m2 => Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m2
   end).
Case Pfreeframe sz pos :=
(fun ge f rs m =>
  match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
  | None => Stuck
  | Some v =>
      match rs SP with
      | Vptr stk ofs =>
          match Mem.free m stk 0 sz with
          | None => Stuck
          | Some m' => Next (nextinstr (rs#SP <- v #X31 <- Vundef)) m'
          end
      | _ => Stuck
      end
  end).
Case Ploadsymbol rd s ofs :=
  (fun ge f rs m => Next (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m).
Case Ploadsymbol_high rd s ofs :=
  (fun ge f rs m =>  Next (nextinstr (rs#rd <- (high_half ge s ofs))) m).
FEnd exec_instr.

(** Execution of the instruction at [rs PC]. *)

MetaData state binds State.
Inductive state: Type :=
| State: regset -> mem -> state.
FEnd state.

MetaData set_res.
Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.
FEnd set_res.

From Rocqet Require Import Locations.
MetaData extcall_arg.
Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = (* Stacklayout.fe_ofs_arg*)0 + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.
FEnd extcall_arg.

MetaData extcall_arg_pair.
Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (AST.One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).
FEnd extcall_arg_pair.

From Rocqet Require Import Conventions1.
FDefinition extcall_arguments
    := fun (rs: regset) (m: mem) (sg: signature) (args: list val) =>
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

FDefinition loc_external_result := fun (sg: signature) =>
  map_rpair preg_of (loc_result sg).

FDefinition set_pair := fun (p: rpair preg) (v: val) (rs: regset) =>
  match p with
  | AST.One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

FDefinition undef_caller_save_regs := fun(rs: regset) =>
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

From Rocqet Require Import Machregs.
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_step_internal:
    forall ge b ofs f i rs m rs' m',
    rs PC = Vptr b ofs ->
    Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    exec_instr i ge f rs m = Next rs' m' ->
    step ge (State rs m) E0 (State rs' m')
| exec_step_builtin:
      forall ge b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      eval_builtin_args (Genv.to_senv ge) rs (rs SP) m args vargs ->
      external_call ef (Genv.to_senv ge) vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs #X1 <- Vundef #X31 <- Vundef))) ->
      step ge (State rs m) t (State rs' m')
  | exec_step_external:
      forall (ge: genv) b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (AST.External ef) ->
      external_call ef (Genv.to_senv ge) args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step ge (State rs m) t (State rs' m').

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall m0,
    let ge := Genv.globalenv p in
    let rs0 :=
      (Pregmap.init Vundef)
      # PC <- (Genv.symbol_address ge p.(AST.prog_main) Ptrofs.zero)
      # SP <- Vnullptr
      # RA <- Vnullptr in
    Genv.init_mem p = Some m0 ->
    initial_state p (State rs0 m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall rs m r,
   rs PC = Vnullptr ->
   rs X10 = Vint r ->
    final_state (State rs m) r.
FEnd final_state.

FEnd Common.

(* Base integer instruction set, 32-bit *)
Family RV32I extends Common.

FInductive instruction : Type :=
| Pmv : ireg -> ireg -> instruction
(** 32-bit integer register-immediate instructions *)
| Paddiw  : ireg -> ireg0 -> int -> instruction        (**r add immediate *)
| Psltiw  : ireg -> ireg0 -> int -> instruction        (**r set-less-than immediate *)
| Psltiuw : ireg -> ireg0 -> int -> instruction        (**r set-less-than unsigned immediate *)
| Pandiw  : ireg -> ireg0 -> int -> instruction        (**r and immediate *)
| Poriw   : ireg -> ireg0 -> int -> instruction        (**r or immediate *)
| Pxoriw  : ireg -> ireg0 -> int -> instruction        (**r xor immediate *)
| Pslliw  : ireg -> ireg0 -> int -> instruction        (**r shift-left-logical immediate *)
| Psrliw  : ireg -> ireg0 -> int -> instruction        (**r shift-right-logical immediate *)
| Psraiw  : ireg -> ireg0 -> int -> instruction        (**r shift-right-arith immediate *)
| Pluiw  : ireg ->  int -> instruction        (**r load upper-immediate *)
(** 32-bit integer register-register instructions *)
| Paddw  : ireg -> ireg0 -> ireg0 -> instruction  (**r integer addition *)
| Psubw  : ireg -> ireg0 -> ireg0 -> instruction  (**r integer subtraction *)
| Psltw  : ireg -> ireg0 -> ireg0 -> instruction  (**r set-less-than *)
| Psltuw : ireg -> ireg0 -> ireg0 -> instruction  (**r set-less-than unsigned *)
| Pseqw  : ireg -> ireg0 -> ireg0 -> instruction  (**r [rd <- rs1 == rs2] (pseudo) *)
| Psnew  : ireg -> ireg0 -> ireg0 -> instruction  (**r [rd <- rs1 != rs2] (pseudo) *)
| Pandw  : ireg -> ireg0 -> ireg0 -> instruction  (**r bitwise and *)
| Porw   : ireg -> ireg0 -> ireg0 -> instruction  (**r bitwise or *)
| Pxorw  : ireg -> ireg0 -> ireg0 -> instruction  (**r bitwise xor *)
| Psllw  : ireg -> ireg0 -> ireg0 -> instruction  (**r shift-left-logical *)
| Psrlw  : ireg -> ireg0 -> ireg0 -> instruction  (**r shift-right-logical *)
| Psraw  : ireg -> ireg0 -> ireg0 -> instruction  (**r shift-right-arith *)
(* Conditional branches, 32-bit comparisons *)
| Pbeqw   : ireg0 -> ireg0 -> label -> instruction  (**r branch-if-equal *)
| Pbnew   : ireg0 -> ireg0 -> label -> instruction  (**r branch-if-not-equal signed *)
| Pbltw   : ireg0 -> ireg0 -> label -> instruction  (**r branch-if-less signed *)
| Pbltuw  : ireg0 -> ireg0 -> label -> instruction  (**r branch-if-less unsigned *)
| Pbgew   : ireg0 -> ireg0 -> label -> instruction  (**r branch-if-greater-or-equal signed *)
| Pbgeuw  : ireg0 -> ireg0 -> label -> instruction  (**r branch-if-greater-or-equal unsigned *)
(* Loads and stores *)
| Plb  : ireg -> ireg -> offset -> instruction     (**r load signed int8 *)
| Plbu : ireg -> ireg -> offset -> instruction     (**r load unsigned int8 *)
| Plh  : ireg -> ireg -> offset -> instruction     (**r load signed int16 *)
| Plhu : ireg -> ireg -> offset -> instruction     (**r load unsigned int16 *)
| Plw  : ireg -> ireg -> offset -> instruction     (**r load int32 *)
| Psb  : ireg -> ireg -> offset -> instruction     (**r store int8 *)
| Psh  : ireg -> ireg -> offset -> instruction     (**r store int16 *)
| Psw  : ireg -> ireg -> offset -> instruction     (**r store int32 *)
| Plw_a : ireg -> ireg -> offset -> instruction    (**r load any32 *)
| Psw_a : ireg -> ireg -> offset -> instruction.    (**r store any32 *)

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pmv d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (rs#s))) m).
Case Paddiw d s i :=  (fun ge f rs m => Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m).
Case Psltiw  d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m).
Case Psltiuw d s i :=  (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m).
Case Pandiw d s i := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.and rs##s (Vint i)))) m).
Case Poriw d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.or rs##s (Vint i)))) m).
Case Pxoriw d s i := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i)))) m).
Case Pslliw d s i := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i)))) m).
Case Psrliw d s i := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i)))) m).
Case Psraiw d s i := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i)))) m).
Case Pluiw d i := (fun ge f rs m => Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m).
Case Paddw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m).
Case Psubw d s1 s2 :=  (fun ge f rs m => Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m).
Case Psltw d s1 s2 :=  (fun ge f rs m => Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m).
Case Psltuw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m).
Case Pseqw d s1 s2 :=  (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m).
Case Psnew d s1 s2 :=  (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m).
Case Pandw d s1 s2 :=  (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m).
Case Porw d s1 s2 :=  (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m).
Case Pxorw d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m).
Case Psllw d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m).
Case Psrlw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m).
Case Psraw d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m).
Case Pbeqw s1 s2 l :=  (fun ge f rs m =>  eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 rs##s2)).
Case Pbnew s1 s2 l :=  (fun ge f rs m =>  eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 rs##s2)).
Case Pbltw s1 s2 l :=  (fun ge f rs m => eval_branch f l rs m (Val.cmp_bool Clt rs##s1 rs##s2)).
Case Pbltuw s1 s2 l := (fun ge f rs m => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##s1 rs##s2)).
Case Pbgew s1 s2 l :=  (fun ge f rs m => eval_branch f l rs m (Val.cmp_bool Cge rs##s1 rs##s2)).
Case Pbgeuw s1 s2 l := (fun ge f rs m => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs##s1 rs##s2)).
Case Plb d a ofs  := (fun ge f rs m => exec_load  ge Mint8signed rs m d a ofs).
Case Plbu d a ofs := (fun ge f rs m => exec_load  ge Mint8unsigned rs m d a ofs).
Case Plh d a ofs  := (fun ge f rs m =>  exec_load ge  Mint16signed rs m d a ofs).
Case Plhu d a ofs := (fun ge f rs m =>  exec_load ge  Mint16unsigned rs m d a ofs).
Case Plw d a ofs  := (fun ge f rs m =>  exec_load ge  Mint32 rs m d a ofs).
Case Psb s a ofs  := (fun ge f rs m =>  exec_store ge Mint8unsigned rs m s a ofs).
Case Psh s a ofs  := (fun ge f rs m => exec_store ge Mint16unsigned rs m s a ofs).
Case Psw s a ofs  := (fun ge f rs m =>  exec_store ge Mint32 rs m s a ofs).
Case Plw_a d a ofs := (fun ge f rs m =>  exec_load ge Many32 rs m d a ofs).
Case Psw_a s a ofs := (fun ge f rs m =>  exec_store ge Many32 rs m s a ofs).
FEnd exec_instr.

FEnd RV32I.

(* Base integer instruction set, 64-bit *)
Family RV64I extends RV32I.
FInductive instruction : Type :=
(** 64-bit integer register-immediate instructions *)
| Paddil : ireg -> ireg0 -> int64 -> instruction      (**r add immediate *)
| Psltil : ireg -> ireg0 -> int64 -> instruction      (**r set-less-than immediate *)
| Psltiul : ireg -> ireg0 -> int64 -> instruction    (**r set-less-than unsigned immediate *)
| Pandil : ireg -> ireg0 -> int64 -> instruction      (**r and immediate *)
| Poril : ireg -> ireg0 -> int64 -> instruction       (**r or immediate *)
| Pxoril : ireg -> ireg0 -> int64 -> instruction      (**r xor immediate *)
| Psllil : ireg -> ireg0 -> int -> instruction      (**r shift-left-logical immediate *)
| Psrlil : ireg -> ireg0 -> int -> instruction      (**r shift-right-logical immediate *)
| Psrail : ireg -> ireg0 -> int -> instruction      (**r shift-right-arith immediate *)
| Pluil : ireg -> int64 -> instruction       (**r load upper-immediate *)
(** 64-bit integer register-register instructions *)
| Paddl  : ireg -> ireg0 -> ireg0 -> instruction (**r integer addition *)
| Psubl  : ireg -> ireg0 -> ireg0 -> instruction (**r integer subtraction *)
| Psltl  : ireg -> ireg0 -> ireg0 -> instruction (**r set-less-than *)
| Psltul : ireg -> ireg0 -> ireg0 -> instruction (**r set-less-than unsigned *)
| Pseql  : ireg -> ireg0 -> ireg0 -> instruction (**r [rd <- rs1 == rs2] (pseudo) *)
| Psnel  : ireg -> ireg0 -> ireg0 -> instruction (**r [rd <- rs1 != rs2] (pseudo) *)
| Pandl  : ireg -> ireg0 -> ireg0 -> instruction (**r bitwise and *)
| Porl   : ireg -> ireg0 -> ireg0 -> instruction (**r bitwise or *)
| Pxorl  : ireg -> ireg0 -> ireg0 -> instruction (**r bitwise xor *)
| Pslll  : ireg -> ireg0 -> ireg0 -> instruction (**r shift-left-logical *)
| Psrll  : ireg -> ireg0 -> ireg0 -> instruction (**r shift-right-logical *)
| Psral  : ireg -> ireg0 -> ireg0 -> instruction (**r shift-right-arith *)
| Pcvtl2w : ireg -> ireg0 -> instruction (**r int64->int32 (pseudo) *)
| Pcvtw2l : ireg -> instruction (**r int32 signed -> int64 (pseudo) *)
(* Conditional branches, 64-bit comparisons *)
| Pbeql   : ireg0 -> ireg0 -> label -> instruction (**r branch-if-equal *)
| Pbnel   : ireg0 -> ireg0 -> label -> instruction (**r branch-if-not-equal signed *)
| Pbltl   : ireg0 -> ireg0 -> label -> instruction (**r branch-if-less signed *)
| Pbltul  : ireg0 -> ireg0 -> label -> instruction (**r branch-if-less unsigned *)
| Pbgel   : ireg0 -> ireg0 -> label -> instruction (**r branch-if-greater-or-equal signed *)
| Pbgeul  : ireg0 -> ireg0 -> label -> instruction (**r branch-if-greater-or-equal unsigned *)
| Pld : ireg -> ireg -> offset -> instruction     (**r load int64 *)
| Psd : ireg -> ireg -> offset -> instruction     (**r store int64 *)
| Ploadli : ireg -> int64 -> instruction (**r load an immediate int64 *)
| Pld_a   : ireg -> ireg -> offset -> instruction (**r load any64 *)
| Psd_a   : ireg -> ireg -> offset -> instruction. (**r store any64 *)

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Paddil d s i := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m).
Case Psltil d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (Vlong i))))) m).
Case Psltiul d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (Vlong i))))) m).
Case Pandil d s i := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m).
Case Poril d s i := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.orl rs###s (Vlong i)))) m).
Case Pxoril d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.xorl rs###s (Vlong i)))) m).
Case Psllil d s i := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.shll rs###s (Vint i)))) m).
Case Psrlil d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m).
Case Psrail d s i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.shrl rs###s (Vint i)))) m).
Case Pluil d i := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Vlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m).
Case Paddl d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m).
Case Psubl d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m).
(* Case Pmull d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m).*)
(* Case Pmulhl d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m).*)
(* Case Pmulhul d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m).*)
(* Case Pdivl d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m).*)
(* Case Pdivul d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m).*)
(* Case Preml d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m).*)
(* Case Premul d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m).*)
Case Psltl d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m).
Case Psltul d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m).
Case Pseql d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m).
Case Psnel d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m).
Case Pandl d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m).
Case Porl d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m).
Case Pxorl d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.xorl rs###s1 rs###s2))) m).
Case Pslll d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m).
Case Psrll d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m).
Case Psral d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m).
Case Pcvtl2w d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.loword rs##s))) m).
Case Pcvtw2l r := (fun ge f rs m =>  Next (nextinstr (rs#r <- (Val.longofint rs#r))) m).
Case Pbeql s1 s2 l :=  (fun ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs###s1 rs###s2)).
Case Pbnel s1 s2 l :=  (fun ge f rs m =>   eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs###s1 rs###s2)).
Case Pbltl s1 s2 l :=  (fun ge f rs m =>  eval_branch f l rs m (Val.cmpl_bool Clt rs###s1 rs###s2)).
Case Pbltul s1 s2 l := (fun ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###s1 rs###s2)).
Case Pbgel s1 s2 l :=  (fun ge f rs m =>  eval_branch f l rs m (Val.cmpl_bool Cge rs###s1 rs###s2)).
Case Pbgeul s1 s2 l := (fun ge f rs m =>  eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge rs###s1 rs###s2)).
Case Pld d a ofs := (fun ge f rs m =>  exec_load ge Mint64 rs m d a ofs).
Case Psd s a ofs := (fun ge f rs m => exec_store ge Mint64 rs m s a ofs).
Case Ploadli rd i :=  (fun ge f rs m => Next (nextinstr (rs#X31 <- Vundef #rd <- (Vlong i))) m).
Case Pld_a d a ofs := (fun ge f rs m => exec_load ge Many64 rs m d a ofs).
Case Psd_a s a ofs := (fun ge f rs m => exec_store ge Many64 rs m s a ofs).
FEnd exec_instr.

FEnd RV64I.

(* Standard extension for integer multiplication and division *)
Family M extends Common.
FInductive instruction : Type :=
| Pmulw   : ireg -> ireg0 -> ireg0 -> instruction  (**r integer multiply low *)
| Pmulhw  : ireg -> ireg0 -> ireg0 -> instruction  (**r integer multiply high signed *)
| Pmulhuw : ireg -> ireg0 -> ireg0 -> instruction  (**r integer multiply high unsigned *)
| Pdivw   : ireg -> ireg0 -> ireg0 -> instruction  (**r integer division *)
| Pdivuw  : ireg -> ireg0 -> ireg0 -> instruction  (**r unsigned integer division *)
| Premw   : ireg -> ireg0 -> ireg0 -> instruction  (**r integer remainder *)
| Premuw  : ireg -> ireg0 -> ireg0 -> instruction  (**r unsigned integer remainder *)
(* 64-bit *)
| Pmull   : ireg -> ireg0 -> ireg0 -> instruction  (**r integer multiply low *)
| Pmulhl  : ireg -> ireg0 -> ireg0 -> instruction  (**r integer multiply high signed *)
| Pmulhul : ireg -> ireg0 -> ireg0 -> instruction  (**r integer multiply high unsigned *)
| Pdivl   : ireg -> ireg0 -> ireg0 -> instruction  (**r integer division *)
| Pdivul  : ireg -> ireg0 -> ireg0 -> instruction  (**r unsigned integer division *)
| Preml   : ireg -> ireg0 -> ireg0 -> instruction  (**r integer remainder *)
| Premul  : ireg -> ireg0 -> ireg0 -> instruction.  (**r unsigned integer remainder *)

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pmulw d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m).
Case Pmulhw d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m).
Case Pmulhuw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m).
Case Pdivw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m).
Case Pdivuw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m).
Case Premw d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m).
Case Premuw d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m).
Case Pmull d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m).
Case Pmulhl d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m).
Case Pmulhul d s1 s2 := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m).
Case Pdivl d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m).
Case Pdivul d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m).
Case Preml d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m).
Case Premul d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m).
FEnd exec_instr.

FEnd M.

(* Standard extension for single-precision floating-point *)
Family F extends Common.
FInductive instruction : Type :=
(* floating point register move *)
| Pfmv   : freg -> freg -> instruction (**r move *)
| Pfmvxs : ireg -> freg -> instruction (**r move FP single to integer register *)
| Pfmvsx : freg -> ireg -> instruction (**r move integer register to FP single *)
| Pfmvxd : ireg -> freg -> instruction (**r move FP double to integer register *)
| Pfmvdx : freg -> ireg -> instruction (**r move integer register to FP double *)
(* 32-bit (single-precision) floating point *)
| Pfls     : freg -> ireg -> offset -> instruction (**r load float *)
| Pfss     : freg -> ireg -> offset -> instruction (**r store float *)
| Pfnegs   : freg -> freg -> instruction (**r negation *)
| Pfabss   : freg -> freg -> instruction (**r absolute value *)
| Pfadds   : freg -> freg -> freg -> instruction (**r addition *)
| Pfsubs   : freg -> freg -> freg -> instruction (**r subtraction *)
| Pfmuls   : freg -> freg -> freg -> instruction (**r multiplication *)
| Pfdivs   : freg -> freg -> freg -> instruction (**r division *)
| Pfmins   : freg -> freg -> freg -> instruction (**r minimum *)
| Pfmaxs   : freg -> freg -> freg -> instruction (**r maximum *)
| Pfeqs    : ireg -> freg -> freg -> instruction (**r compare equal *)
| Pflts    : ireg -> freg -> freg -> instruction (**r compare less-than *)
| Pfles    : ireg -> freg -> freg -> instruction (**r compare less-than/equal *)
| Pfsqrts  : freg -> freg -> instruction (**r square-root *)
| Pfmadds  : freg -> freg -> freg -> freg -> instruction (**r fused multiply-add *)
| Pfmsubs  : freg -> freg -> freg -> freg -> instruction (**r fused multiply-sub *)
| Pfnmadds : freg -> freg -> freg -> freg -> instruction (**r fused negated multiply-add *)
| Pfnmsubs : freg -> freg -> freg -> freg -> instruction (**r fused negated multiply-sub *)
| Pfcvtws  : ireg -> freg -> instruction (**r float32 -> int32 conversion *)
| Pfcvtwus : ireg -> freg -> instruction (**r float32 -> unsigned int32 conversion *)
| Pfcvtsw  : freg -> ireg0 -> instruction (**r int32 -> float32 conversion *)
| Pfcvtswu : freg -> ireg0 -> instruction (**r unsigned int32 -> float32 conversion *)
| Pfcvtls  : ireg -> freg -> instruction (**r float32 -> int64 conversion *)
| Pfcvtlus : ireg -> freg -> instruction (**r float32 -> unsigned int64 conversion *)
| Pfcvtsl  : freg -> ireg0 -> instruction (**r int64 -> float32 conversion *)
| Pfcvtslu : freg -> ireg0 -> instruction (**r unsigned int 64-> float32 conversion *)
| Ploadsi : freg -> float32 -> instruction. (**r load an immediate single *)

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pfmv d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (rs#s))) m).
Case Pfls d a ofs := (fun ge f rs m => exec_load ge Mfloat32 rs m d a ofs).
Case Pfss s a ofs := (fun ge f rs m => exec_store ge Mfloat32 rs m s a ofs).
Case Pfnegs d s := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.negfs rs#s))) m).
Case Pfabss d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.absfs rs#s))) m).
Case Pfadds d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m).
Case Pfsubs d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m).
Case Pfmuls d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m).
Case Pfdivs d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m).
Case Pfeqs d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m).
Case Pflts d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m).
Case Pfles d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m).
Case Pfcvtws d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m).
Case Pfcvtwus d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m).
Case Pfcvtsw d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m).
Case Pfcvtswu d s := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m).
Case Pfcvtls d s := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m).
Case Pfcvtlus d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m).
Case Pfcvtsl d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m).
Case Pfcvtslu d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m).
Case Ploadsi rd f := (fun ge _ rs m =>  Next (nextinstr (rs#X31 <- Vundef #rd <- (Vsingle f))) m).

(*not in the execution model *)
Case Pfmins a b c := (fun ge f rs m => Stuck).
Case Pfmaxs a b c := (fun ge f rs m => Stuck).
Case Pfsqrts a b := (fun ge f rs m => Stuck).
Case Pfmadds a b c d := (fun ge f rs m => Stuck).
Case Pfmsubs a b c d := (fun ge f rs m => Stuck).
Case Pfnmadds a b c d := (fun ge f rs m => Stuck).
Case Pfnmsubs a b c d := (fun ge f rs m => Stuck).
Case Pfmvxs a b := (fun ge f rs m => Stuck).
Case Pfmvsx a b := (fun ge f rs m => Stuck).
Case Pfmvxd a b := (fun ge f rs m => Stuck).
Case Pfmvdx a b := (fun ge f rs m => Stuck).

FEnd exec_instr.

FEnd F.

(* Standard extension for double-precision floating-point *)
Family D extends F.
FInductive instruction : Type :=
| Pfld     : freg -> ireg -> offset -> instruction (**r load 64-bit float *)
| Pfsd     : freg -> ireg -> offset -> instruction (**r store 64-bit float *)
| Pfnegd   : freg -> freg -> instruction (**r negation *)
| Pfabsd   : freg -> freg -> instruction (**r absolute value *)
| Pfaddd   : freg -> freg -> freg -> instruction (**r addition *)
| Pfsubd   : freg -> freg -> freg -> instruction (**r subtraction *)
| Pfmuld   : freg -> freg -> freg -> instruction (**r multiplication *)
| Pfdivd   : freg -> freg -> freg -> instruction (**r division *)
| Pfmind   : freg -> freg -> freg -> instruction (**r minimum *)
| Pfmaxd   : freg -> freg -> freg -> instruction (**r maximum *)
| Pfeqd    : ireg -> freg -> freg -> instruction (**r compare equal *)
| Pfltd    : ireg -> freg -> freg -> instruction (**r compare less-than *)
| Pfled    : ireg -> freg -> freg -> instruction (**r compare less-than/equal *)
| Pfsqrtd  : freg -> freg -> instruction (**r square-root *)
| Pfmaddd  : freg -> freg -> freg -> freg -> instruction (**r fused multiply-add *)
| Pfmsubd  : freg -> freg -> freg -> freg -> instruction (**r fused multiply-sub *)
| Pfnmaddd : freg -> freg -> freg -> freg -> instruction (**r fused negated multiply-add *)
| Pfnmsubd : freg -> freg -> freg -> freg -> instruction (**r fused negated multiply-sub *)
| Pfcvtwd  : ireg -> freg -> instruction (**r float -> int32 conversion *)
| Pfcvtwud : ireg -> freg -> instruction (**r float -> unsigned int32 conversion *)
| Pfcvtdw  : freg -> ireg0 -> instruction (**r int32 -> float conversion *)
| Pfcvtdwu : freg -> ireg0 -> instruction (**r unsigned int32 -> float conversion *)
| Pfcvtld  : ireg -> freg -> instruction (**r float -> int64 conversion *)
| Pfcvtlud : ireg -> freg -> instruction (**r float -> unsigned int64 conversion *)
| Pfcvtdl  : freg -> ireg0 -> instruction (**r int64 -> float conversion *)
| Pfcvtdlu : freg -> ireg0 -> instruction (**r unsigned int64 -> float conversion *)
| Pfcvtds : freg -> freg -> instruction (**r float32 -> float   *)
| Pfcvtsd : freg -> freg -> instruction (**r float   -> float32 *)
| Ploadfi : freg -> float -> instruction (**r load an immediate float *)
| Pfld_a  : freg -> ireg -> offset -> instruction (**r load any64 *)
| Pfsd_a  : freg -> ireg -> offset -> instruction. (**r store any64 *)

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pfld d a ofs := (fun ge f rs m =>  exec_load ge Mfloat64 rs m d a ofs).
Case Pfsd s a ofs := (fun ge f rs m => exec_store ge Mfloat64 rs m s a ofs).
Case Pfnegd d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.negf rs#s))) m).
Case Pfabsd d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.absf rs#s))) m).
Case Pfaddd d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m).
Case Pfsubd d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m).
Case Pfmuld d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m).
Case Pfdivd d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m).
Case Pfeqd d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m).
Case Pfltd d s1 s2 := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m).
Case Pfled d s1 s2 := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m).
Case Ploadfi rd f := (fun ge _ rs m => Next (nextinstr (rs#X31 <- Vundef #rd <- (Vfloat f))) m).
Case Pfcvtwd d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m).
Case Pfcvtwud d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m).
Case Pfcvtdw d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m).
Case Pfcvtdwu d s := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m).
Case Pfcvtld d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m).
Case Pfcvtlud d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.longuoffloat rs#s)))) m).
Case Pfcvtdl d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m).
Case Pfcvtdlu d s := (fun ge f rs m =>  Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m).
Case Pfcvtds d s := (fun ge f rs m =>   Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m).
Case Pfcvtsd d s := (fun ge f rs m => Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m).
Case Pfld_a d a ofs := (fun ge f rs m => exec_load ge Many64 rs m d a ofs).
Case Pfsd_a s a ofs := (fun ge f rs m => exec_store ge Many64 rs m s a ofs).

(* not modeled *)
Case Pfmind d s1 s2 := (fun ge f rs m => Stuck ).
Case Pfmaxd d s1 s2 := (fun ge f rs m => Stuck).
Case Pfsqrtd a b := (fun ge f rs m => Stuck).
Case Pfmaddd a b c d := (fun ge f rs m => Stuck).
Case Pfmsubd  a b c d := (fun ge f rs m => Stuck).
Case Pfnmaddd a b c d  := (fun ge f rs m => Stuck).
Case Pfnmsubd a b c d  := (fun ge f rs m => Stuck).

FEnd exec_instr.

FEnd D.

(* Standard extension for vector operations *)
Family V.
FEnd V.

FEnd RV.

Trait Base.

Family Asm extends RV.RV64I, RV.M.
FEnd Asm.

FEnd Base.

Trait Comp_Float extends Base.

(* extend with Asm *)
Family Asm extends RV.D.
FEnd Asm.

FEnd Comp_Float.
