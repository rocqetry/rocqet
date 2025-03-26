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

(* RISC-V *)
Family Asm extends RV.RV64I, RV.M, RV.D.
FEnd Asm.

Trait Base.

From Rocqet Require Import Registers.

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

Family Lfam.
FEnd Lfam.

Family Mach extends Lfam.
FDefinition label := positive.

FInductive instruction: Type :=
| Lop : Op.operation -> list mreg -> mreg -> instruction
| Lcond : Op.condition -> list mreg -> label -> instruction
| Llabel: label -> instruction
| Lgoto: label -> instruction
| Lreturn : instruction
| Lgetstack: ptrofs -> typ -> mreg -> instruction
| Lgetparam: ptrofs -> typ -> mreg -> instruction
| Lsetstack: mreg -> ptrofs -> typ -> instruction
(* Heap *)
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FDefinition code: Type := list instruction.

MetaData function binds fn_sig, fn_code, fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_code: code;
  fn_stacksize: Z;
  fn_link_ofs: ptrofs;
  fn_retaddr_ofs: ptrofs
}.
FEnd function.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => fn_sig f
  | AST.External ef => ef_sig ef
  end.

FDefinition genv := Genv.t fundef unit.

MetaData stackframe binds Stackframe.
Inductive stackframe: Type :=
  | Stackframe:
      forall (f: block)(* pointer to calling function *)
             (sp: val)(* stack pointer in calling function *)
             (retaddr: val)(* Asm return address in calling function *)
             (c: code),(* program point in calling function *)
      stackframe.
FEnd stackframe.

From Rocqet Require Import Mregisters.

MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State:
      forall (stack: list stackframe)(* call stack *)
             (f: block)(* pointer to current function *)
             (sp: val)(* stack pointer *)
             (c: code)(* current program point *)
             (rs: regset)(* register state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)(* call stack *)
             (f: block)(* pointer to function to call *)
             (rs: regset)(* register state *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)(* call stack *)
             (rs: regset)(* register state *)
             (m: mem),(* memory state *)
        state.
FEnd state.

FRecursion is_label about instruction motive (fun (_ : instruction) => label -> bool) by _rect.
Case Llabel lbl' := (fun lbl => if peq lbl lbl' then true else false).
Case _ := (fun lbl => false).
FEnd is_label.

MetaData find_label.
Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label i1 lbl then Some il else find_label lbl il
  end.
FEnd find_label.

FDefinition load_stack := fun (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) =>
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

FDefinition store_stack := fun (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) =>
   Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

(*From Rocqet Require Import Mregisters.
FDefinition reglist := fun (a: regset) (b: list mreg) => a ## b.*)

MetaData undef_regs.
Fixpoint undef_regs (rl: list mreg) (rs: Regmap.t val) {struct rl} :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite Regmap.gso. apply IHrl. intuition. intuition.
Qed.

Lemma undef_regs_same:
  forall r rl rs, In r rl -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct H. subst a. apply Regmap.gss.
  unfold Regmap.set. destruct (RegEq.eq r a); auto.
Qed.
FEnd undef_regs.

FDefinition parent_sp := fun (s: list stackframe) =>
  match s with
  | nil => Vnullptr
  | self__Mach.Stackframe f sp ra c :: s' => sp
  end.

FDefinition parent_ra := fun (s: list stackframe) =>
  match s with
  | nil => Vnullptr
  | self__Mach.Stackframe f sp ra c :: s' => ra
  end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Llabel:
    forall ge s f sp lbl b rs m,
    step ge (State s f sp (Llabel lbl :: b) rs m)
      E0 (State s f sp b rs m)
| exec_Lgoto:
    forall ge s fb f sp lbl b rs m c',
    Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
    find_label lbl (fn_code f) = Some c' ->
    step ge (State s fb sp (Lgoto lbl :: b) rs m)
      E0 (State s fb sp c' rs m)
| exec_Lop:
    forall ge s f sp op args res b rs m v rs',
    eval_operation ge sp op rs##args m = Some v ->
    rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
    step ge (State s f sp (Lop op args res :: b) rs m)
      E0 (State s f sp b rs' m)
| exec_Lcond_true:
    forall ge s f fb sp cond args lbl b rs m rs' c',
    eval_condition cond rs##args m = Some true ->
    Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
    find_label lbl (fn_code f) = Some c' ->
    rs' = undef_regs (destroyed_by_cond cond) rs ->
    step ge (State s fb sp (Lcond cond args lbl :: b) rs m)
      E0 (State s fb sp c' rs' m)
| exec_Lcond_false:
    forall ge s f sp cond args lbl c rs m rs',
    eval_condition cond rs##args m = Some false ->
    rs' = undef_regs (destroyed_by_cond cond) rs ->
    step ge (State s f sp (Lcond cond args lbl :: c) rs m)
      E0 (State s f sp c rs' m)
| exec_return:
      forall ge s f sp rs0 c rs m,
      step ge (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m)
| exec_Lgetstack:
      forall ge s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step ge (State s f sp (Lgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
| exec_Lsetstack:
      forall ge s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step ge (State s f sp (Lsetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
| exec_Lgetparam:
      forall ge s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      load_stack m sp Tptr (fn_link_ofs f) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step ge (State s fb sp (Lgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
| exec_function_internal:
      forall ge s fb rs m f m1 m2 m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      Mem.alloc m 0 (fn_stacksize f) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr (fn_link_ofs f) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tptr (fn_retaddr_ofs f) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step ge (Callstate s fb rs m)
        E0 (State s fb sp (fn_code f) rs' m3)
| exec_Lreturn:
      forall ge s fb stk soff c rs m f m',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      load_stack m (Vptr stk soff) Tptr (fn_link_ofs f) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr (fn_retaddr_ofs f) = Some (parent_ra s) ->
      Mem.free m stk 0 (fn_stacksize f) = Some m' ->
      step ge (State s fb (Vptr stk soff) (Lreturn :: c) rs m)
        E0 (Returnstate s rs m')
(* Heap *)
| exec_Lload:
      forall ge s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step ge (State s f sp (Lload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
| exec_Lstore:
      forall ge s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step ge (State s f sp (Lstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m').

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall fb m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(AST.prog_main) = Some fb ->
      initial_state p (Callstate nil fb (Regmap.init Vundef) m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = AST.One r ->
      rs r = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.
FEnd final_state.

FEnd Mach.

(* Mach -> Asm *)
Family Asmgen.
Family S extends Mach. FEnd S.

FDefinition ireg_of : mreg -> res ireg := fun r =>
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

FDefinition freg_of : mreg -> res freg := fun r =>
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

MetaData immed32 binds Imm32_single, Imm32_pair.
Inductive immed32 : Type :=
  | Imm32_single (imm: int)
  | Imm32_pair   (hi: int) (lo: int).
FEnd immed32.

FDefinition make_immed32 := fun (val: int) =>
  let lo := Int.sign_ext 12 val in
  if Int.eq val lo
  then Imm32_single val
  else Imm32_pair (Int.shru (Int.sub val lo) (Int.repr 12)) lo.

FDefinition load_hilo32 := fun (r: ireg) (hi lo: int) k =>
  if Int.eq lo Int.zero then Asm.Pluiw r hi :: k
  else Asm.Pluiw r hi :: Asm.Paddiw r r lo :: k.

FDefinition loadimm32 := fun (r: ireg) (n: int) (k: Asm.code) =>
  match make_immed32 n with
  | self__Asmgen.Imm32_single imm => Asm.Paddiw r X0 imm :: k
  | self__Asmgen.Imm32_pair hi lo => load_hilo32 r hi lo k
  end.

MetaData immed64 binds Imm64_single, Imm64_pair, Imm64_large.
Inductive immed64 : Type :=
  | Imm64_single (imm: int64)
  | Imm64_pair   (hi: int64) (lo: int64)
  | Imm64_large  (imm: int64).
FEnd immed64.

FDefinition make_immed64 := fun (val: int64) =>
  let lo := Int64.sign_ext 12 val in
  if Int64.eq val lo then Imm64_single lo else
  let hi := Int64.zero_ext 20 (Int64.shru (Int64.sub val lo) (Int64.repr 12)) in
  if Int64.eq val (Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo)
  then Imm64_pair hi lo
  else Imm64_large val.

FDefinition load_hilo64 := fun (r: ireg) (hi lo: int64) k =>
  if Int64.eq lo Int64.zero then Asm.Pluil r hi :: k
  else Asm.Pluil r hi :: Asm.Paddil r r lo :: k.

FDefinition loadimm64 := fun (r: ireg) (n: int64) (k: Asm.code) =>
  match make_immed64 n with
  | self__Asmgen.Imm64_single imm => Asm.Paddil r X0 imm :: k
  | self__Asmgen.Imm64_pair hi lo => load_hilo64 r hi lo k
  | self__Asmgen.Imm64_large imm  => Asm.Ploadli r imm :: k
  end.

FDefinition opimm32 :=
fun (op: ireg -> ireg0 -> ireg0 -> Asm.instruction)
    (opimm: ireg -> ireg0 -> int -> Asm.instruction)
    (rd rs: ireg) (n: int) (k: Asm.code) =>
  match make_immed32 n with
  | self__Asmgen.Imm32_single imm => opimm rd rs imm :: k
  | self__Asmgen.Imm32_pair hi lo => load_hilo32 X31 hi lo (op rd rs X31 :: k)
  end.

FDefinition opimm64 :=
  fun (op: ireg -> ireg0 -> ireg0 -> Asm.instruction)
      (opimm: ireg -> ireg0 -> int64 -> Asm.instruction)
      (rd rs: ireg) (n: int64) (k: Asm.code) =>
  match make_immed64 n with
  | self__Asmgen.Imm64_single imm => opimm rd rs imm :: k
  | self__Asmgen.Imm64_pair hi lo => load_hilo64 X31 hi lo (op rd rs X31 :: k)
  | self__Asmgen.Imm64_large imm  => Asm.Ploadli X31 imm :: op rd rs X31 :: k
  end.

FDefinition addimm32 := opimm32 Asm.Paddw Asm.Paddiw.
FDefinition xorimm32 := opimm32 Asm.Pxorw Asm.Pxoriw.
FDefinition sltimm32 := opimm32 Asm.Psltw Asm.Psltiw.
FDefinition addimm64 := opimm64 Asm.Paddl Asm.Paddil.
FDefinition sltuimm32 := opimm32 Asm.Psltuw Asm.Psltiuw.
FDefinition xorimm64 := opimm64 Asm.Pxorl Asm.Pxoril.

FDefinition addptrofs := fun (rd rs: ireg) (n: ptrofs) (k: Asm.code) =>
  if Ptrofs.eq_dec n Ptrofs.zero then
    Asm.Pmv rd rs :: k
  else
    if Archi.ptr64
    then addimm64 rd rs (Ptrofs.to_int64 n) k
    else addimm32 rd rs (Ptrofs.to_int n) k.

FDefinition transl_cond_int32s := fun (cmp: comparison) (rd: ireg) (r1 r2: ireg0) (k: Asm.code) =>
  match cmp with
  | Ceq => Asm.Pseqw rd r1 r2 :: k
  | Cne => Asm.Psnew rd r1 r2 :: k
  | Clt => Asm.Psltw rd r1 r2 :: k
  | Cle => Asm.Psltw rd r2 r1 :: Asm.Pxoriw rd rd Int.one :: k
  | Cgt => Asm.Psltw rd r2 r1 :: k
  | Cge => Asm.Psltw rd r1 r2 :: Asm.Pxoriw rd rd Int.one :: k
  end.

FDefinition transl_cond_int32u := fun (cmp: comparison) (rd: ireg) (r1 r2: ireg0) (k: Asm.code) =>
  match cmp with
  | Ceq => Asm.Pseqw rd r1 r2 :: k
  | Cne => Asm.Psnew rd r1 r2 :: k
  | Clt => Asm.Psltuw rd r1 r2 :: k
  | Cle => Asm.Psltuw rd r2 r1 :: Asm.Pxoriw rd rd Int.one :: k
  | Cgt => Asm.Psltuw rd r2 r1 :: k
  | Cge => Asm.Psltuw rd r1 r2 :: Asm.Pxoriw rd rd Int.one :: k
  end.

FDefinition transl_condimm_int32s := fun (cmp: comparison) (rd: ireg) (r1: ireg) (n: int) (k: Asm.code) =>
  if Int.eq n Int.zero then transl_cond_int32s cmp rd r1 X0 k else
  match cmp with
  | Ceq | Cne => xorimm32 rd r1 n (transl_cond_int32s cmp rd rd X0 k)
  | Clt => sltimm32 rd r1 n k
  | Cle => if Int.eq n (Int.repr Int.max_signed)
           then loadimm32 rd Int.one k
           else sltimm32 rd r1 (Int.add n Int.one) k
  | _   => loadimm32 X31 n (transl_cond_int32s cmp rd r1 X31 k)
  end.

FDefinition transl_condimm_int32u := fun (cmp: comparison) (rd: ireg) (r1: ireg) (n: int) (k: Asm.code) =>
  if Int.eq n Int.zero then transl_cond_int32u cmp rd r1 X0 k else
  match cmp with
  | Clt => sltuimm32 rd r1 n k
  | _   => loadimm32 X31 n (transl_cond_int32u cmp rd r1 X31 k)
  end.

FDefinition transl_cond_int64s := fun (cmp: comparison) (rd: ireg) (r1 r2: ireg0) (k: Asm.code) =>
  match cmp with
  | Ceq => Asm.Pseql rd r1 r2 :: k
  | Cne => Asm.Psnel rd r1 r2 :: k
  | Clt => Asm.Psltl rd r1 r2 :: k
  | Cle => Asm.Psltl rd r2 r1 :: Asm.Pxoriw rd rd Int.one :: k
  | Cgt => Asm.Psltl rd r2 r1 :: k
  | Cge => Asm.Psltl rd r1 r2 :: Asm.Pxoriw rd rd Int.one :: k
  end.

FDefinition transl_cond_int64u := fun (cmp: comparison) (rd: ireg) (r1 r2: ireg0) (k: Asm.code) =>
  match cmp with
  | Ceq => Asm.Pseql rd r1 r2 :: k
  | Cne => Asm.Psnel rd r1 r2 :: k
  | Clt => Asm.Psltul rd r1 r2 :: k
  | Cle => Asm.Psltul rd r2 r1 :: Asm.Pxoriw rd rd Int.one :: k
  | Cgt => Asm.Psltul rd r2 r1 :: k
  | Cge => Asm.Psltul rd r1 r2 :: Asm.Pxoriw rd rd Int.one :: k
  end.

FDefinition transl_cond_float := fun (cmp: comparison) (rd: ireg) (fs1 fs2: freg) =>
  match cmp with
  | Ceq => (Asm.Pfeqd rd fs1 fs2, true)
  | Cne => (Asm.Pfeqd rd fs1 fs2, false)
  | Clt => (Asm.Pfltd rd fs1 fs2, true)
  | Cle => (Asm.Pfled rd fs1 fs2, true)
  | Cgt => (Asm.Pfltd rd fs2 fs1, true)
  | Cge => (Asm.Pfled rd fs2 fs1, true)
  end.

FDefinition transl_cond_single := fun (cmp: comparison) (rd: ireg) (fs1 fs2: freg) =>
  match cmp with
  | Ceq => (Asm.Pfeqs rd fs1 fs2, true)
  | Cne => (Asm.Pfeqs rd fs1 fs2, false)
  | Clt => (Asm.Pflts rd fs1 fs2, true)
  | Cle => (Asm.Pfles rd fs1 fs2, true)
  | Cgt => (Asm.Pflts rd fs2 fs1, true)
  | Cge => (Asm.Pfles rd fs2 fs1, true)
  end.

FDefinition sltimm64 := opimm64 Asm.Psltl Asm.Psltil.
FDefinition transl_condimm_int64s := fun (cmp: comparison) (rd: ireg) (r1: ireg) (n: int64) (k: Asm.code) =>
  if Int64.eq n Int64.zero then transl_cond_int64s cmp rd r1 X0 k else
  match cmp with
  | Ceq | Cne => xorimm64 rd r1 n (transl_cond_int64s cmp rd rd X0 k)
  | Clt => sltimm64 rd r1 n k
  | Cle => if Int64.eq n (Int64.repr Int64.max_signed)
           then loadimm32 rd Int.one k
           else sltimm64 rd r1 (Int64.add n Int64.one) k
  | _   => loadimm64 X31 n (transl_cond_int64s cmp rd r1 X31 k)
  end.

FDefinition sltuimm64 := opimm64 Asm.Psltul Asm.Psltiul.
FDefinition transl_condimm_int64u := fun (cmp: comparison) (rd: ireg) (r1: ireg) (n: int64) (k: Asm.code) =>
  if Int64.eq n Int64.zero then transl_cond_int64u cmp rd r1 X0 k else
  match cmp with
  | Clt => sltuimm64 rd r1 n k
  | _   => loadimm64 X31 n (transl_cond_int64u cmp rd r1 X31 k)
  end.
Local Open Scope error_monad_scope.
FDefinition transl_cond_op
           := fun (cond: condition) (rd: ireg) (args: list mreg) (k: Asm.code) =>
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int32s c rd r1 r2 k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int32u c rd r1 r2 k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int32s c rd r1 n k)
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int32u c rd r1 n k)
  | Ccompl c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int64s c rd r1 r2 k)
  | Ccomplu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int64u c rd r1 r2 k)
  | Ccomplimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int64s c rd r1 n k)
  | Ccompluimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int64u c rd r1 n k)
  | Ccompf c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_float c rd r1 r2 in
      OK (insn :: if normal then k else Asm.Pxoriw rd rd Int.one :: k)
  | Cnotcompf c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_float c rd r1 r2 in
      OK (insn :: if normal then Asm.Pxoriw rd rd Int.one :: k else k)
  | Ccompfs c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_single c rd r1 r2 in
      OK (insn :: if normal then k else Asm.Pxoriw rd rd Int.one :: k)
  | Cnotcompfs c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_single c rd r1 r2 in
      OK (insn :: if normal then Asm.Pxoriw rd rd Int.one :: k else k)
  | _, _ =>
      Error(msg "Asmgen.transl_cond_op")
  end.

(*From Rocqet Require Import Prelude.*)

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

FDefinition andimm32 := opimm32 Asm.Pandw Asm.Pandiw.
FDefinition orimm32  := opimm32 Asm.Porw Asm.Poriw.
FDefinition andimm64 := opimm64 Asm.Pandl Asm.Pandil.
FDefinition orimm64  := opimm64 Asm.Porl  Asm.Poril.
FDefinition transl_op
            := fun (op: operation) (args: list mreg) (res: mreg) (k: Asm.code) =>
  match op, args with
  | Op.Omove, a1 :: nil =>
      match preg_of res, preg_of a1 with
      | IR r, IR a => OK (Asm.Pmv r a :: k)
      | FR r, FR a => OK (Asm.Pfmv r a :: k)
      |  _  ,  _   => Error(msg "Asmgen.Omove")
      end
  | Op.Ointconst n, nil =>
      do rd <- ireg_of res;
      OK (loadimm32 rd n k)
  | Op.Olongconst n, nil =>
      do rd <- ireg_of res;
      OK (loadimm64 rd n k)
  | Op.Ofloatconst f, nil =>
      do rd <- freg_of res;
      OK (if Float.eq_dec f Float.zero
          then Asm.Pfcvtdw rd X0 :: k
          else Asm.Ploadfi rd f :: k)
  | Op.Osingleconst f, nil =>
      do rd <- freg_of res;
      OK (if Float32.eq_dec f Float32.zero
          then Asm.Pfcvtsw rd X0 :: k
          else Asm.Ploadsi rd f :: k)
  | Op.Oaddrsymbol s ofs, nil =>
      do rd <- ireg_of res;
      OK (if Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)
          then Asm.Ploadsymbol rd s Ptrofs.zero :: addptrofs rd rd ofs k
          else Asm.Ploadsymbol rd s ofs :: k)
  | Op.Oaddrstack n, nil =>
      do rd <- ireg_of res;
      OK (addptrofs rd SP n k)

  | Op.Ocast8signed, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Pslliw rd rs (Int.repr 24) :: Asm.Psraiw rd rd (Int.repr 24) :: k)
  | Op.Ocast16signed, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Pslliw rd rs (Int.repr 16) :: Asm.Psraiw rd rd (Int.repr 16) :: k)
  | Op.Oadd, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Paddw rd rs1 rs2 :: k)
  | Op.Oaddimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (addimm32 rd rs n k)
  | Op.Oneg, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psubw rd X0 rs :: k)
  | Op.Osub, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psubw rd rs1 rs2 :: k)
  | Op.Omul, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pmulw rd rs1 rs2 :: k)
  | Op.Omulhs, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pmulhw rd rs1 rs2 :: k)
  | Op.Omulhu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pmulhuw rd rs1 rs2 :: k)
  | Op.Odiv, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pdivw rd rs1 rs2 :: k)
  | Op.Odivu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pdivuw rd rs1 rs2 :: k)
  | Op.Omod, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Premw rd rs1 rs2 :: k)
  | Op.Omodu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Premuw rd rs1 rs2 :: k)
  | Op.Oand, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pandw rd rs1 rs2 :: k)
  | Op.Oandimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (andimm32 rd rs n k)
  | Op.Oor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Porw rd rs1 rs2 :: k)
  | Op.Oorimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (orimm32 rd rs n k)
  | Op.Oxor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pxorw rd rs1 rs2 :: k)
  | Op.Oxorimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (xorimm32 rd rs n k)
  | Op.Oshl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psllw rd rs1 rs2 :: k)
  | Op.Oshlimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Pslliw rd rs n :: k)
  | Op.Oshr, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psraw rd rs1 rs2 :: k)
  | Op.Oshrimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psraiw rd rs n :: k)
  | Op.Oshru, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psrlw rd rs1 rs2 :: k)
  | Op.Oshruimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psrliw rd rs n :: k)
  | Op.Oshrximm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (if Int.eq n Int.zero then Asm.Pmv rd rs :: k else
          Asm.Psraiw X31 rs (Int.repr 31) ::
          Asm.Psrliw X31 X31 (Int.sub Int.iwordsize n) ::
          Asm.Paddw X31 rs X31 ::
          Asm.Psraiw rd X31 n :: k)

  (* [Omakelong], [Ohighlong]  should not occur *)
  | Op.Olowlong, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Pcvtl2w rd rs :: k)
  | Op.Ocast32signed, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      assertion (ireg_eq rd rs);
      OK (Asm.Pcvtw2l rd :: k)
  | Op.Ocast32unsigned, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      assertion (ireg_eq rd rs);
      OK (Asm.Pcvtw2l rd :: Asm.Psllil rd rd (Int.repr 32) :: Asm.Psrlil rd rd (Int.repr 32) :: k)
  | Op.Oaddl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Paddl rd rs1 rs2 :: k)
  | Op.Oaddlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (addimm64 rd rs n k)
  | Op.Onegl, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psubl rd X0 rs :: k)
  | Op.Osubl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psubl rd rs1 rs2 :: k)
  | Op.Omull, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pmull rd rs1 rs2 :: k)
  | Op.Omullhs, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pmulhl rd rs1 rs2 :: k)
  | Op.Omullhu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pmulhul rd rs1 rs2 :: k)
  | Op.Odivl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pdivl rd rs1 rs2 :: k)
  | Op.Odivlu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pdivul rd rs1 rs2 :: k)
  | Op.Omodl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Preml rd rs1 rs2 :: k)
  | Op.Omodlu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Premul rd rs1 rs2 :: k)
  | Op.Oandl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pandl rd rs1 rs2 :: k)
  | Op.Oandlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (andimm64 rd rs n k)
  | Op.Oorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Porl rd rs1 rs2 :: k)
  | Op.Oorlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (orimm64 rd rs n k)
  | Op.Oxorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pxorl rd rs1 rs2 :: k)
  | Op.Oxorlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (xorimm64 rd rs n k)
  | Op.Oshll, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Pslll rd rs1 rs2 :: k)
  | Op.Oshllimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psllil rd rs n :: k)
  | Op.Oshrl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psral rd rs1 rs2 :: k)
  | Op.Oshrlimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psrail rd rs n :: k)
  | Op.Oshrlu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Asm.Psrll rd rs1 rs2 :: k)
  | Op.Oshrluimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Asm.Psrlil rd rs n :: k)
  | Op.Oshrxlimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (if Int.eq n Int.zero then Asm.Pmv rd rs :: k else
          Asm.Psrail X31 rs (Int.repr 63) ::
          Asm.Psrlil X31 X31 (Int.sub Int64.iwordsize' n) ::
          Asm.Paddl X31 rs X31 ::
          Asm.Psrail rd X31 n :: k)

  | Op.Onegf, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Asm.Pfnegd rd rs :: k)
  | Op.Oabsf, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Asm.Pfabsd rd rs :: k)
  | Op.Oaddf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfaddd rd rs1 rs2 :: k)
  | Op.Osubf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfsubd rd rs1 rs2 :: k)
  | Op.Omulf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfmuld rd rs1 rs2 :: k)
  | Op.Odivf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfdivd rd rs1 rs2 :: k)

  | Op.Onegfs, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Asm.Pfnegs rd rs :: k)
  | Op.Oabsfs, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Asm.Pfabss rd rs :: k)
  | Op.Oaddfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfadds rd rs1 rs2 :: k)
  | Op.Osubfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfsubs rd rs1 rs2 :: k)
  | Op.Omulfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfmuls rd rs1 rs2 :: k)
  | Op.Odivfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Asm.Pfdivs rd rs1 rs2 :: k)

  | Op.Osingleoffloat, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtsd rd rs :: k)
  | Op.Ofloatofsingle, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtds rd rs :: k)

  | Op.Ointoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtwd rd rs :: k)
  | Op.Ointuoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtwud rd rs :: k)
  | Op.Ofloatofint, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtdw rd rs :: k)
  | Op.Ofloatofintu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtdwu rd rs :: k)
  | Op.Ointofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtws rd rs :: k)
  | Op.Ointuofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtwus rd rs :: k)
  | Op.Osingleofint, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtsw rd rs :: k)
  | Op.Osingleofintu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtswu rd rs :: k)

  | Op.Olongoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtld rd rs :: k)
  | Op.Olonguoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtlud rd rs :: k)
  | Op.Ofloatoflong, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtdl rd rs :: k)
  | Op.Ofloatoflongu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtdlu rd rs :: k)
  | Op.Olongofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtls rd rs :: k)
  | Op.Olonguofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Asm.Pfcvtlus rd rs :: k)
  | Op.Osingleoflong, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtsl rd rs :: k)
  | Op.Osingleoflongu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Asm.Pfcvtslu rd rs :: k)

  | Op.Ocmp cmp, _ =>
      do rd <- ireg_of res;
      transl_cond_op cmp rd args k

  | _, _ =>
      Error(msg "Asmgen.transl_op")
  end.

FDefinition transl_cbranch_int32s := fun (cmp: comparison) (r1 r2: ireg0) (lbl: Asm.label) =>
  match cmp with
  | Ceq => Asm.Pbeqw r1 r2 lbl
  | Cne => Asm.Pbnew r1 r2 lbl
  | Clt => Asm.Pbltw r1 r2 lbl
  | Cle => Asm.Pbgew r2 r1 lbl
  | Cgt => Asm.Pbltw r2 r1 lbl
  | Cge => Asm.Pbgew r1 r2 lbl
  end.

FDefinition transl_cbranch_int32u := fun (cmp: comparison) (r1 r2: ireg0) (lbl: Asm.label) =>
  match cmp with
  | Ceq => Asm.Pbeqw  r1 r2 lbl
  | Cne => Asm.Pbnew  r1 r2 lbl
  | Clt => Asm.Pbltuw r1 r2 lbl
  | Cle => Asm.Pbgeuw r2 r1 lbl
  | Cgt => Asm.Pbltuw r2 r1 lbl
  | Cge => Asm.Pbgeuw r1 r2 lbl
  end.

FDefinition transl_cbranch_int64s := fun (cmp: comparison) (r1 r2: ireg0) (lbl: Asm.label) =>
  match cmp with
  | Ceq => Asm.Pbeql r1 r2 lbl
  | Cne => Asm.Pbnel r1 r2 lbl
  | Clt => Asm.Pbltl r1 r2 lbl
  | Cle => Asm.Pbgel r2 r1 lbl
  | Cgt => Asm.Pbltl r2 r1 lbl
  | Cge => Asm.Pbgel r1 r2 lbl
  end.

FDefinition transl_cbranch_int64u := fun (cmp: comparison) (r1 r2: ireg0) (lbl: Asm.label) =>
  match cmp with
  | Ceq => Asm.Pbeql  r1 r2 lbl
  | Cne => Asm.Pbnel  r1 r2 lbl
  | Clt => Asm.Pbltul r1 r2 lbl
  | Cle => Asm.Pbgeul r2 r1 lbl
  | Cgt => Asm.Pbltul r2 r1 lbl
  | Cge => Asm.Pbgeul r1 r2 lbl
  end.

FDefinition transl_cbranch
           := fun (cond: condition) (args: list mreg) (lbl: Asm.label) (k: Asm.code) =>
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cbranch_int32s c r1 r2 lbl :: k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cbranch_int32u c r1 r2 lbl :: k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq n Int.zero then
            transl_cbranch_int32s c r1 X0 lbl :: k
          else
            loadimm32 X31 n (transl_cbranch_int32s c r1 X31 lbl :: k))
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq n Int.zero then
            transl_cbranch_int32u c r1 X0 lbl :: k
          else
            loadimm32 X31 n (transl_cbranch_int32u c r1 X31 lbl :: k))
  | Ccompl c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cbranch_int64s c r1 r2 lbl :: k)
  | Ccomplu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cbranch_int64u c r1 r2 lbl :: k)
  | Ccomplimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int64.eq n Int64.zero then
            transl_cbranch_int64s c r1 X0 lbl :: k
          else
            loadimm64 X31 n (transl_cbranch_int64s c r1 X31 lbl :: k))
  | Ccompluimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int64.eq n Int64.zero then
            transl_cbranch_int64u c r1 X0 lbl :: k
          else
            loadimm64 X31 n (transl_cbranch_int64u c r1 X31 lbl :: k))
  | Ccompf c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_float c X31 r1 r2 in
      OK (insn :: (if normal then Asm.Pbnew X31 X0 lbl else Asm.Pbeqw X31 X0 lbl) :: k)
  | Cnotcompf c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_float c X31 r1 r2 in
      OK (insn :: (if normal then Asm.Pbeqw X31 X0 lbl else Asm.Pbnew X31 X0 lbl) :: k)
  | Ccompfs c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_single c X31 r1 r2 in
      OK (insn :: (if normal then Asm.Pbnew X31 X0 lbl else Asm.Pbeqw X31 X0 lbl) :: k)
  | Cnotcompfs c, f1 :: f2 :: nil =>
      do r1 <- freg_of f1; do r2 <- freg_of f2;
      let (insn, normal) := transl_cond_single c X31 r1 r2 in
      OK (insn :: (if normal then Asm.Pbeqw X31 X0 lbl else Asm.Pbnew X31 X0 lbl) :: k)
  | _, _ =>
      Error(msg "Asmgen.transl_cond_branch")
  end.

FDefinition indexed_memory_access :=
  fun (mk_instr: ireg -> Asm.offset -> Asm.instruction)
      (base: ireg) (ofs: ptrofs) (k: Asm.code) =>
  if Archi.ptr64 then
    match make_immed64 (Ptrofs.to_int64 ofs) with
    | self__Asmgen.Imm64_single imm =>
        mk_instr base (Asm.Ofsimm (Ptrofs.of_int64 imm)) :: k
    | self__Asmgen.Imm64_pair hi lo =>
        Asm.Pluil X31 hi :: Asm.Paddl X31 base X31 :: mk_instr X31 (Asm.Ofsimm (Ptrofs.of_int64 lo)) :: k
    | self__Asmgen.Imm64_large imm =>
        Asm.Ploadli X31 imm :: Asm.Paddl X31 base X31 :: mk_instr X31 (Asm.Ofsimm Ptrofs.zero) :: k
    end
  else
    match make_immed32 (Ptrofs.to_int ofs) with
    | self__Asmgen.Imm32_single imm =>
        mk_instr base (Asm.Ofsimm (Ptrofs.of_int imm)) :: k
    | self__Asmgen.Imm32_pair hi lo =>
        Asm.Pluiw X31 hi :: Asm.Paddw X31 base X31 :: mk_instr X31 (Asm.Ofsimm (Ptrofs.of_int lo)) :: k
    end.

FDefinition loadind :=
  fun (base: ireg) (ofs: ptrofs) (ty: typ) (dst: mreg) (k: Asm.code) =>
  match ty, preg_of dst with
  | AST.Tint,    IR rd => OK (indexed_memory_access (Asm.Plw rd) base ofs k)
  | AST.Tlong,   IR rd => OK (indexed_memory_access (Asm.Pld rd) base ofs k)
  | AST.Tsingle, FR rd => OK (indexed_memory_access (Asm.Pfls rd) base ofs k)
  | AST.Tfloat,  FR rd => OK (indexed_memory_access (Asm.Pfld rd) base ofs k)
  | AST.Tany32,  IR rd => OK (indexed_memory_access (Asm.Plw_a rd) base ofs k)
  | AST.Tany64,  IR rd => OK (indexed_memory_access (Asm.Pld_a rd) base ofs k)
  | AST.Tany64,  FR rd => OK (indexed_memory_access (Asm.Pfld_a rd) base ofs k)
  | _, _           => Error (msg "Asmgen.loadind")
  end.

FDefinition storeind := fun (src: mreg) (base: ireg) (ofs: ptrofs) (ty: typ) (k: Asm.code) =>
  match ty, preg_of src with
  | AST.Tint,    IR rd => OK (indexed_memory_access (Asm.Psw rd) base ofs k)
  | AST.Tlong,   IR rd => OK (indexed_memory_access (Asm.Psd rd) base ofs k)
  | AST.Tsingle, FR rd => OK (indexed_memory_access (Asm.Pfss rd) base ofs k)
  | AST.Tfloat,  FR rd => OK (indexed_memory_access (Asm.Pfsd rd) base ofs k)
  | AST.Tany32,  IR rd => OK (indexed_memory_access (Asm.Psw_a rd) base ofs k)
  | AST.Tany64,  IR rd => OK (indexed_memory_access (Asm.Psd_a rd) base ofs k)
  | AST.Tany64,  FR rd => OK (indexed_memory_access (Asm.Pfsd_a rd) base ofs k)
  | _, _           => Error (msg "Asmgen.storeind")
  end.

FDefinition loadind_ptr := fun (base: ireg) (ofs: ptrofs) (dst: ireg) (k: Asm.code) =>
  indexed_memory_access (if Archi.ptr64 then Asm.Pld dst else Asm.Plw dst) base ofs k.

FDefinition storeind_ptr := fun (src: ireg) (base: ireg) (ofs: ptrofs) (k: Asm.code) =>
  indexed_memory_access (if Archi.ptr64 then Asm.Psd src else Asm.Psw src) base ofs k.

FDefinition make_epilogue := fun (f: S.function) (k: Asm.code) =>
  loadind_ptr SP (S.fn_retaddr_ofs f) RA
    (Asm.Pfreeframe (S.fn_stacksize f) (S.fn_link_ofs f) :: k).

(* Heap *)
From Rocqet Require Import Errors.
Open Scope error_monad_scope.
FDefinition transl_memory_access
     := fun (mk_instr: ireg -> Asm.offset -> Asm.instruction)
            (addr: addressing) (args: list mreg) (k: Asm.code) =>
  match addr, args with
  | Aindexed ofs, a1 :: nil =>
      do rs <- ireg_of a1;
      OK (indexed_memory_access mk_instr rs ofs k)
  | Aglobal id ofs, nil =>
    OK (Asm.Ploadsymbol_high X31 id ofs :: mk_instr X31 (Asm.Ofslow id ofs) :: k)
  | Ainstack ofs, nil =>
      OK (indexed_memory_access mk_instr SP ofs k)
  | _, _ =>
      Error(msg "Asmgen.transl_memory_access")
  end.

FDefinition transl_load := fun
  (chunk: memory_chunk) (addr: addressing)
  (args: list mreg) (dst: mreg) (k: Asm.code) =>
  match chunk with
  | Mint8signed =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plb r)  addr args k
  | Mint8unsigned =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plbu r) addr args k
  | Mint16signed =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plh r)  addr args k
  | Mint16unsigned =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plhu r) addr args k
  | Mint32 =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plw r)  addr args k
  | Mint64 =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Pld r)  addr args k
  | Mfloat32 =>
      do r <- freg_of dst;
      transl_memory_access (Asm.Pfls r) addr args k
  | Mfloat64 =>
      do r <- freg_of dst;
      transl_memory_access (Asm.Pfld r) addr args k
  | _ =>
      Error (msg "Asmgen.transl_load")
  end.

FDefinition transl_store := fun (chunk: memory_chunk) (addr: addressing)
           (args: list mreg) (src: mreg) (k: Asm.code) =>
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psb r)  addr args k
  | Mint16unsigned =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psh r)  addr args k
  | Mint32 =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psw r)  addr args k
  | Mint64 =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psd r)  addr args k
  | Mfloat32 =>
      do r <- freg_of src;
      transl_memory_access (Asm.Pfss r) addr args k
  | Mfloat64 =>
      do r <- freg_of src;
      transl_memory_access (Asm.Pfsd r) addr args k
  | _ =>
      Error (msg "Asmgen.transl_store")
  end.

FRecursion transl_instr about S.instruction motive (fun (_ : S.instruction) => S.function -> bool -> Asm.code -> res Asm.code) by _rect.
Case Lgetstack ofs ty dst := (fun f ep k => loadind SP ofs ty dst k).
Case Lsetstack src ofs ty := (fun f ep k =>  storeind src SP ofs ty k).
Case Lgetparam ofs ty dst :=
(fun f ep k =>
    do c <- loadind X30 ofs ty dst k;
      OK (if ep then c
                else loadind_ptr SP (S.fn_link_ofs f) X30 c)).
Case Lop op args res := (fun f ep k =>  transl_op op args res k).
Case Llabel lbl := (fun f ep k =>  OK (Asm.Plabel lbl :: k)).
Case Lgoto lbl := (fun f ep k => OK (Asm.Pj_l lbl :: k)).
Case Lcond cond args lbl := (fun f ep k => transl_cbranch cond args lbl k).
Case Lreturn := (fun f ep k => OK (make_epilogue f (Asm.Pj_r RA (S.fn_sig f) :: k))).
(* Heap *)
Case Lload chunk addr args dst :=
 (fun f ep k => transl_load chunk addr args dst k).
Case Lstore chunk addr args src :=
 (fun f ep k => transl_store chunk addr args src k).
FEnd transl_instr.

FRecursion it1_is_parent about S.instruction motive (fun (_ : S.instruction) => bool -> bool) by _rect.
Case Lgetstack ofs ty dst := (fun before => false).
Case Lsetstack src ofs ty := (fun before => before).
Case Lgetparam ofs ty dst := (fun before => negb (mreg_eq dst R30)).
Case Lop op args res := (fun before => before && negb (mreg_eq res R30)).
Case Llabel lbl := (fun before => false).
Case Lgoto lbl := (fun before => false).
Case Lcond cond args lbl := (fun before => false).
Case Lreturn := (fun before => false).
(* Heap *)
Case _ := (fun before => false).
FEnd it1_is_parent.

(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)
MetaData transl_code.
Fixpoint transl_code (f: S.function) (il: list S.instruction) (it1p: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (it1_is_parent i1 it1p);
      transl_instr i1 f it1p k
  end.
FEnd transl_code.

(** This is an equivalent definition in continuation-passing style
  that runs in constant stack space. *)
MetaData transl_code_rec.
Fixpoint transl_code_rec (f: S.function) (il: list S.instruction)
                         (it1p: bool) (k: Asm.code -> res Asm.code) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_code_rec f il' (it1_is_parent i1 it1p)
        (fun c1 => do c2 <- transl_instr i1 f it1p c1; k c2)
  end.
FEnd transl_code_rec.

FDefinition transl_code' :=
  fun (f: S.function) (il: list S.instruction) (it1p: bool) =>
  transl_code_rec f il it1p (fun c => OK c).

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

FDefinition transl_function := fun (f: S.function) =>
  do c <- transl_code' f (S.fn_code f) true;
  OK (Asm.mkfunction (S.fn_sig f)
        (Asm.Pallocframe (S.fn_stacksize f) (S.fn_link_ofs f) ::
         storeind_ptr RA SP (S.fn_retaddr_ofs f) (Asm.Pcfi_rel_offset (Ptrofs.to_int (S.fn_retaddr_ofs f)):: c))).

FDefinition transf_function : S.function -> res Asm.function := fun f =>
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z (Asm.fn_code tf))
  then Error (msg "code size exceeded")
  else OK tf.

FDefinition transf_fundef : S.fundef -> res Asm.fundef := fun f =>
  transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res Asm.program := fun p =>
  transform_partial_program transf_fundef p.


(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

MetaData code_tail.
Inductive code_tail: Z -> Asm.code -> Asm.code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. lia. lia.
Qed.

Import Asm.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. extlia.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by lia.
  eauto.
Qed.

Remark code_tail_bounds_1:
  forall fn ofs c,
  code_tail ofs fn c -> 0 <= ofs <= list_length_z fn.
Proof.
  induction 1; intros; simpl.
  generalize (list_length_z_pos c). lia.
  rewrite list_length_z_cons. lia.
Qed.

Remark code_tail_bounds_2:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl.
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). lia.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). lia.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Ptrofs.max_unsigned ->
  code_tail (Ptrofs.unsigned ofs) fn (i :: c) ->
  code_tail (Ptrofs.unsigned (Ptrofs.add ofs Ptrofs.one)) fn c.
Proof.
  intros. rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_one.
  rewrite Ptrofs.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds_2 _ _ _ _ H0). lia.
Qed.
FEnd code_tail.

(** [transl_code_at_pc pc fb f c ep tf tc] holds if the code pointer [pc] points
  within the Asm code generated by translating Mach function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

MetaData transl_code_at_pc.
Inductive transl_code_at_pc (ge: S.genv):
    val -> block -> S.function -> S.code -> bool -> Asm.function -> Asm.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(AST.Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_code f c ep = OK tc ->
    code_tail (Ptrofs.unsigned ofs) (Asm.fn_code tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc.
FEnd transl_code_at_pc.

MetaData match_stack.
(** * Properties of the Mach call stack *)
Section MATCH_STACK.
Import S.
Variable ge: genv.

Inductive match_stack: list stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f tf tc,
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      transl_code_at_pc ge ra fb f c false tf tc ->
      sp <> Vundef ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Lemma parent_sp_def: forall s, match_stack s -> parent_sp s <> Vundef.
Proof.
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  auto.
Qed.

Lemma parent_ra_def: forall s, match_stack s -> parent_ra s <> Vundef.
Proof.
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  inv H0. congruence.
Qed.

Lemma lessdef_parent_sp:
  forall s v,
  match_stack s -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

Lemma lessdef_parent_ra:
  forall s v,
  match_stack s -> Val.lessdef (parent_ra s) v -> v = parent_ra s.
Proof.
  intros. inv H0. auto. exploit parent_ra_def; eauto. tauto.
Qed.

End MATCH_STACK.
FEnd match_stack.

FDefinition match_prog := fun (p: S.program) (tp: Asm.program) =>
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Open Scope asm.
MetaData Proof0 binds agree.
Global Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = FR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma preg_of_data:
  forall r, data_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.
Global Hint Resolve preg_of_data: asmgen.

Lemma data_diff:
  forall r r',
  data_preg r = true -> data_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Global Hint Resolve data_diff: asmgen.

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence.
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
Qed.

Global Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.

Lemma undef_regs_other:
  forall r rl rs,
  (forall r', In r' rl -> r <> r') ->
  Asm.undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto.
  rewrite IHrl by auto. rewrite Pregmap.gso; auto.
Qed.

Fixpoint preg_notin (r: preg) (rl: list mreg) : Prop :=
  match rl with
  | nil => True
  | r1 :: nil => r <> preg_of r1
  | r1 :: rl => r <> preg_of r1 /\ preg_notin r rl
  end.

Remark preg_notin_charact:
  forall r rl,
  preg_notin r rl <-> (forall mr, In mr rl -> r <> preg_of mr).
Proof.
  induction rl; simpl; intros.
  tauto.
  destruct rl.
  simpl. split. intros. intuition congruence. auto.
  rewrite IHrl. split.
  intros [A B]. intros. destruct H. congruence. auto.
  auto.
Qed.

Lemma undef_regs_other_2:
  forall r rl rs,
  preg_notin r rl ->
  Asm.undef_regs (map preg_of rl) rs r = rs r.
Proof.
  intros. apply undef_regs_other. intros.
  exploit list_in_map_inv; eauto. intros [mr [A B]]. subst.
  rewrite preg_notin_charact in H. auto.
Qed.

(** * Agreement between Mach registers and processor registers *)
Record agree (ms: regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#SP = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r, agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall ms sp rs, agree ms sp rs ->
  forall l, Val.lessdef_list (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma sp_val:
  forall ms sp rs, agree ms sp rs -> sp = rs#SP.
Proof.
  intros. destruct H; auto.
Qed.

Lemma ireg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  freg_of r = OK r' ->
  Val.lessdef (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, data_preg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H0; auto. auto.
  intros. rewrite H0; auto. apply preg_of_data.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto. apply not_eq_sym. apply preg_of_not_SP.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence.
  rewrite H1. auto. apply preg_of_data.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Corollary agree_set_mreg_parallel:
  forall ms sp rs r v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Regmap.set r v ms) sp (Pregmap.set (preg_of r) v' rs).
Proof.
  intros. eapply agree_set_mreg; eauto. rewrite Pregmap.gss; auto. intros; apply Pregmap.gso; auto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  data_preg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (Asm.nextinstr rs).
Proof.
  intros. unfold Asm.nextinstr. apply agree_set_other. auto. auto.
Qed.

Lemma agree_undef_regs:
  forall ms sp rl rs rs',
  agree ms sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (S.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite <- agree_sp0. apply H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite S.undef_regs_same; auto.
  rewrite S.undef_regs_other; auto. rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_undef_regs2:
  forall ms sp rl rs rs',
  agree (S.undef_regs rl ms) sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (S.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite <- agree_sp0. apply H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite S.undef_regs_same; auto.
  rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_set_undef_mreg:
  forall ms sp rs r v rl rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Regmap.set r v (S.undef_regs rl ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  apply agree_undef_regs with rs; auto.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' (preg_of r)).
  congruence. auto.
  intros. rewrite Pregmap.gso; auto.
Qed.

Lemma agree_change_sp:
  forall ms sp rs sp',
  agree ms sp rs -> sp' <> Vundef ->
  agree ms sp' (rs#SP <- sp').
Proof.
  intros. inv H. split; auto.
  intros. rewrite Pregmap.gso; auto with asmgen.
Qed.
FEnd Proof0.

MetaData match_states.
Inductive match_states (ge: S.genv): S.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (AST.Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#X30 = S.parent_sp s),
      match_states ge (S.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (S.parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = S.parent_ra s),
      match_states ge (S.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (S.parent_sp s) rs)
        (ATPC: rs PC = S.parent_ra s),
      match_states ge (S.Returnstate s ms m)
                   (Asm.State rs m').
FEnd match_states.

MetaData exec_straight binds exec_straight_opt.
Section STRAIGHTLINE.
Import Asm.
Variable ge: Asm.genv.
Variable fn: Asm.function.

Inductive exec_straight: Asm.code -> Asm.regset -> mem ->
                         Asm.code -> Asm.regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_instr i1 ge fn rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
      exec_straight (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_instr i ge fn rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight (i :: c) rs1 m1 c' rs3 m3.

Lemma exec_straight_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_step with rs2 m2; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3,
  exec_instr i1 ge fn rs1 m1 = Next rs2 m2 ->
  exec_instr i2 ge fn rs2 m2 = Next rs3 m3 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  rs3#PC = Val.offset_ptr rs2#PC Ptrofs.one ->
  exec_straight (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_instr i1 ge fn rs1 m1 = Next rs2 m2 ->
  exec_instr i2 ge fn rs2 m2 = Next rs3 m3 ->
  exec_instr i3 ge fn rs3 m3 = Next rs4 m4 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  rs3#PC = Val.offset_ptr rs2#PC Ptrofs.one ->
  rs4#PC = Val.offset_ptr rs3#PC Ptrofs.one ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct Asm executions. *)

Lemma exec_straight_steps_1:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (AST.Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_code fn) c ->
  plus step ge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  eapply plus_left'.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  apply IHexec_straight with b (Ptrofs.add ofs Ptrofs.one).
  auto. rewrite H0. rewrite H3. reflexivity.
  auto.
  apply code_tail_next_int with i; auto.
  traceEq.
Qed.

Lemma exec_straight_steps_2:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (AST.Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_code fn) c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Ptrofs.unsigned ofs') (fn_code fn) c'.
Proof.
  induction 1; intros.
  exists (Ptrofs.add ofs Ptrofs.one). split.
  rewrite H0. rewrite H2. auto.
  apply code_tail_next_int with i1; auto.
  apply IHexec_straight with (Ptrofs.add ofs Ptrofs.one).
  auto. rewrite H0. rewrite H3. reflexivity. auto.
  apply code_tail_next_int with i; auto.
Qed.

Inductive exec_straight_opt: code -> regset -> mem -> code -> regset -> mem -> Prop :=
  | exec_straight_opt_refl: forall c rs m,
      exec_straight_opt c rs m c rs m
  | exec_straight_opt_intro: forall c1 rs1 m1 c2 rs2 m2,
      exec_straight c1 rs1 m1 c2 rs2 m2 ->
      exec_straight_opt c1 rs1 m1 c2 rs2 m2.

Lemma exec_straight_opt_left:
  forall c3 rs3 m3 c1 rs1 m1 c2 rs2 m2,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight_opt c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  destruct 2; intros. auto. eapply exec_straight_trans; eauto.
Qed.

Lemma exec_straight_opt_right:
  forall c3 rs3 m3 c1 rs1 m1 c2 rs2 m2,
  exec_straight_opt c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  destruct 1; intros. auto. eapply exec_straight_trans; eauto.
Qed.

Lemma exec_straight_opt_step:
  forall i c rs1 m1 rs2 m2 c' rs3 m3,
  exec_instr i ge fn rs1 m1 = Next rs2 m2 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  exec_straight_opt c rs2 m2 c' rs3 m3 ->
  exec_straight (i :: c) rs1 m1 c' rs3 m3.
Proof.
  intros. inv H1.
- apply exec_straight_one; auto.
- eapply exec_straight_step; eauto.
Qed.

Lemma exec_straight_opt_step_opt:
  forall i c rs1 m1 rs2 m2 c' rs3 m3,
  exec_instr i ge fn rs1 m1 = Next rs2 m2 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  exec_straight_opt c rs2 m2 c' rs3 m3 ->
  exec_straight_opt (i :: c) rs1 m1 c' rs3 m3.
Proof.
  intros. apply exec_straight_opt_intro. eapply exec_straight_opt_step; eauto.
Qed.
End STRAIGHTLINE.
FEnd exec_straight.

MetaData PRESERVATION0.
Section PRESERVATION0.

Variable prog: S.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (AST.Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (Asm.fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(Asm.fn_code))); inv EQ0.
  lia.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus Asm.step tge (Asm.State rs m) E0 (Asm.State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

End PRESERVATION0.
FEnd PRESERVATION0.

FLemma exec_straight_steps:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr i f ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent i ep = true -> rs2#X30 = S.parent_sp s)) ->
  exists st',
  plus Asm.step tge (Asm.State rs1 m1') E0 st' /\
  match_states ge (S.State s fb sp c ms2 m2) st'.
FProofLemma.
intros. inversion H5. subst. monadInv H10.
exploit H6; eauto. intros [rs2 [A [B C]]].
exists (Asm.State rs2 m2'); split.
eapply exec_straight_exec; eauto.
econstructor; eauto. eapply exec_straight_at; eauto.
Qed. CloseFLemma.

FDefinition measure := fun (s: S.state) =>
  match s with
  | self__Asmgen.S.State _ _ _ _ _ _ => 0%nat
  | self__Asmgen.S.Callstate _ _ _ _ => 0%nat
  | self__Asmgen.S.Returnstate _ _ _ => 1%nat
  end.

(* Asmgenproof0 *)
MetaData find_label.
Fixpoint find_label (lbl: Asm.label) (c: Asm.code) {struct c} : option Asm.code :=
  match c with
  | nil => None
  | instr :: c' =>
      if Asm.is_label instr lbl then Some c' else find_label lbl c'
  end.
FEnd find_label.

(* Asmgenproof0 *)
FDefinition nolabel := fun (i: Asm.instruction) =>
  (* __internal becuase Asm is not inside the compiler family *)
  match i with Asm.__internal_Plabel _ => False | _ => True end.

(* Asmgenproof0 *)
FLemma transl_code_rec_transl_code:
  forall f il ep k,
  transl_code_rec f il ep k = (do c <- transl_code f il ep; k c).
FProofLemma.
  induction il; simpl; intros.
  auto.
  rewrite IHil.
  destruct (transl_code f il (it1_is_parent a ep)); simpl; auto.
Qed. CloseFLemma.

(* Asmgenproof0 *)
FLemma transl_code'_transl_code:
  forall f il ep,
  transl_code' f il ep = transl_code f il ep.
FProofLemma.
  intros. unfold transl_code'. rewrite transl_code_rec_transl_code.
  destruct (transl_code f il ep); auto.
Qed. CloseFLemma.

(* Asmgenproof0 *)
FDefinition tail_nolabel : Asm.code -> Asm.code -> Prop := fun k c =>
  is_tail k c /\ forall lbl, find_label lbl c = find_label lbl k.

FLemma tail_nolabel_refl:
  forall c, tail_nolabel c c.
FProofLemma.
  intros; split. apply is_tail_refl. auto.
Qed. CloseFLemma.

FLemma tail_nolabel_trans:
  forall c1 c2 c3, tail_nolabel c2 c3 -> tail_nolabel c1 c2 -> tail_nolabel c1 c3.
FProofLemma.
  intros. destruct H; destruct H0; split.
  eapply is_tail_trans; eauto.
  intros. rewrite H1; auto.
Qed. CloseFLemma.

MetaData _nolabel_hint.
Global Hint Extern 1 (nolabel _) => exact I : labels.
FEnd _nolabel_hint.

FLemma tail_nolabel_cons:
  forall i c k,
  nolabel i -> tail_nolabel k c -> tail_nolabel k (i :: c).
FProofLemma.
  intros. destruct H0. split.
  constructor; auto.
  intros. simpl. rewrite <- H1. destruct i; reflexivity || contradiction.
Qed. CloseFLemma.

MetaData _tail_nolabel_refl.
Global Hint Resolve tail_nolabel_refl: labels.
FEnd _tail_nolabel_refl.

MetaData TailNoLabel.
Ltac TailNoLabel :=
  eauto with labels;
  match goal with
  | [ |- tail_nolabel _ (_ :: _) ] => apply tail_nolabel_cons; [auto; exact I | TailNoLabel]
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: assertion_failed = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; TailNoLabel
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H;  TailNoLabel
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; TailNoLabel
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; TailNoLabel
  | _ => idtac
  end.
FEnd TailNoLabel.

(* Asmgenproof0 *)
FLemma tail_nolabel_find_label:
  forall lbl k c, tail_nolabel k c -> find_label lbl c = find_label lbl k.
FProofLemma.
  intros. destruct H. auto.
Qed. CloseFLemma.

(* Asmgenproof0 *)
FLemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  Asm.label_pos lbl pos c = Some pos'
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
FProofLemma.
  induction c.
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (Asm.is_label a lbl).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by lia. constructor. constructor.
  rewrite list_length_z_cons. generalize (list_length_z_pos c). lia.
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by lia.
  constructor. auto.
  rewrite list_length_z_cons. lia.
Qed. CloseFLemma.

(* FIND_LABEL: Asmgenproof *)
FLemma indexed_memory_access_label:
  forall (mk_instr: ireg -> Asm.offset -> Asm.instruction) base ofs k,
  (forall r o, nolabel (mk_instr r o)) ->
  tail_nolabel k (indexed_memory_access mk_instr base ofs k).
FProofLemma.
  unfold indexed_memory_access; intros.
  destruct Archi.ptr64.
  destruct (make_immed64 (Ptrofs.to_int64 ofs)); TailNoLabel.
  destruct (make_immed32 (Ptrofs.to_int ofs)); TailNoLabel.
Qed. CloseFLemma.

FLemma storeind_ptr_label:
  forall src base ofs k, tail_nolabel k (storeind_ptr src base ofs k).
FProofLemma.
  intros. apply indexed_memory_access_label. intros; destruct Archi.ptr64; exact I.
Qed. CloseFLemma.

MetaData _label_lemmas.
Remark loadimm32_label:
  forall r n k, tail_nolabel k (loadimm32 r n k).
Proof.
  intros; unfold loadimm32. destruct (make_immed32 n); TailNoLabel.
  unfold load_hilo32. destruct (Int.eq lo Int.zero); TailNoLabel.
Qed.
Hint Resolve loadimm32_label: labels.

Remark opimm32_label:
  forall op opimm r1 r2 n k,
  (forall r1 r2 r3, nolabel (op r1 r2 r3)) ->
  (forall r1 r2 n, nolabel (opimm r1 r2 n)) ->
  tail_nolabel k (opimm32 op opimm r1 r2 n k).
Proof.
  intros; unfold opimm32. destruct (make_immed32 n); TailNoLabel.
  unfold load_hilo32. destruct (Int.eq lo Int.zero); TailNoLabel.
Qed.
Hint Resolve opimm32_label: labels.

Remark loadimm64_label:
  forall r n k, tail_nolabel k (loadimm64 r n k).
Proof.
  intros; unfold loadimm64. destruct (make_immed64 n); TailNoLabel.
  unfold load_hilo64. destruct (Int64.eq lo Int64.zero); TailNoLabel.
Qed.
Hint Resolve loadimm64_label: labels.

Remark opimm64_label:
  forall op opimm r1 r2 n k,
  (forall r1 r2 r3, nolabel (op r1 r2 r3)) ->
  (forall r1 r2 n, nolabel (opimm r1 r2 n)) ->
  tail_nolabel k (opimm64 op opimm r1 r2 n k).
Proof.
  intros; unfold opimm64. destruct (make_immed64 n); TailNoLabel.
  unfold load_hilo64. destruct (Int64.eq lo Int64.zero); TailNoLabel.
Qed.
Hint Resolve opimm64_label: labels.

Remark addptrofs_label:
  forall r1 r2 n k, tail_nolabel k (addptrofs r1 r2 n k).
Proof.
  unfold addptrofs; intros. destruct (Ptrofs.eq_dec n Ptrofs.zero). TailNoLabel.
  destruct Archi.ptr64. apply opimm64_label; TailNoLabel. apply opimm32_label; TailNoLabel.
Qed.
Hint Resolve addptrofs_label: labels.

Remark transl_cond_float_nolabel:
  forall c r1 r2 r3 insn normal,
  transl_cond_float c r1 r2 r3 = (insn, normal) -> nolabel insn.
Proof.
  unfold transl_cond_float; intros. destruct c; inv H; exact I.
Qed.

Remark transl_cond_single_nolabel:
  forall c r1 r2 r3 insn normal,
  transl_cond_single c r1 r2 r3 = (insn, normal) -> nolabel insn.
Proof.
  unfold transl_cond_single; intros. destruct c; inv H; exact I.
Qed.

Remark transl_cbranch_label:
  forall cond args lbl k c,
  transl_cbranch cond args lbl k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cbranch in H; destruct cond; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct (Int.eq n Int.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int32s c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (Int.eq n Int.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int32u c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct (Int64.eq n Int64.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int64s c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (Int64.eq n Int64.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int64u c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto.
  destruct normal; TailNoLabel.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto.
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto.
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto.
  destruct normal; TailNoLabel.
Qed.

Remark transl_cond_op_label:
  forall cond args r k c,
  transl_cond_op cond r args k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cond_op in H; destruct cond; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- unfold transl_condimm_int32s.
  destruct (Int.eq n Int.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl.
* eapply tail_nolabel_trans; [apply opimm32_label; intros; exact I | TailNoLabel].
* eapply tail_nolabel_trans; [apply opimm32_label; intros; exact I | TailNoLabel].
* apply opimm32_label; intros; exact I.
* destruct (Int.eq n (Int.repr Int.max_signed)). apply loadimm32_label. apply opimm32_label; intros; exact I.
* eapply tail_nolabel_trans. apply loadimm32_label. TailNoLabel.
* eapply tail_nolabel_trans. apply loadimm32_label. TailNoLabel.
- unfold transl_condimm_int32u.
  destruct (Int.eq n Int.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl;
  try (eapply tail_nolabel_trans; [apply loadimm32_label | TailNoLabel]).
  apply opimm32_label; intros; exact I.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- unfold transl_condimm_int64s.
  destruct (Int64.eq n Int64.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl.
* eapply tail_nolabel_trans; [apply opimm64_label; intros; exact I | TailNoLabel].
* eapply tail_nolabel_trans; [apply opimm64_label; intros; exact I | TailNoLabel].
* apply opimm64_label; intros; exact I.
* destruct (Int64.eq n (Int64.repr Int64.max_signed)). apply loadimm32_label. apply opimm64_label; intros; exact I.
* eapply tail_nolabel_trans. apply loadimm64_label. TailNoLabel.
* eapply tail_nolabel_trans. apply loadimm64_label. TailNoLabel.
- unfold transl_condimm_int64u.
  destruct (Int64.eq n Int64.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl;
  try (eapply tail_nolabel_trans; [apply loadimm64_label | TailNoLabel]).
  apply opimm64_label; intros; exact I.
- destruct (transl_cond_float c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto.
  destruct normal; TailNoLabel.
- destruct (transl_cond_float c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto.
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto.
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto.
  destruct normal; TailNoLabel.
Qed.
FEnd _label_lemmas.

FLemma transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c -> tail_nolabel k c.
FProofLemma.
Opaque Int.eq.
  unfold transl_op; intros; destruct op; TailNoLabel.
- destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
- destruct (Float.eq_dec n Float.zero); TailNoLabel.
- destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
- destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)).
+ eapply tail_nolabel_trans; [|apply addptrofs_label]. TailNoLabel.
+ TailNoLabel.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- destruct (Int.eq n Int.zero); TailNoLabel.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- destruct (Int.eq n Int.zero); TailNoLabel.
- eapply transl_cond_op_label; eauto.
Qed. CloseFLemma.

(* match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.*)
FRecursion transl_instr_label_sig about S.instruction
  motive (fun (_ : S.instruction) => Asm.code -> list Asm.instruction -> Prop) by _rect.
Case Llabel lbl := (fun c k => c = Asm.Plabel lbl :: k).
Case _ := (fun c k => tail_nolabel k c).
FEnd transl_instr_label_sig.

FLemma loadind_ptr_label:
  forall base ofs dst k, tail_nolabel k (loadind_ptr base ofs dst k).
FProofLemma.
  intros. apply indexed_memory_access_label. intros; destruct Archi.ptr64; exact I.
Qed. CloseFLemma.

FLemma make_epilogue_label:
  forall f k, tail_nolabel k (make_epilogue f k).
FProofLemma.
  unfold make_epilogue; intros. eapply tail_nolabel_trans. apply loadind_ptr_label. TailNoLabel.
Qed. CloseFLemma.

FLemma loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c -> tail_nolabel k c.
FProofLemma.
  unfold loadind; intros.
  destruct ty, (preg_of dst); inv H; apply indexed_memory_access_label; intros; exact I.
Qed. CloseFLemma.

FLemma storeind_label:
  forall src base ofs ty k c,
  storeind src base ofs ty k = OK c -> tail_nolabel k c.
FProofLemma.
  unfold storeind; intros.
  destruct ty, (preg_of src); inv H; apply indexed_memory_access_label; intros; exact I.
Qed. CloseFLemma.

(* Heap *)
FLemma transl_memory_access_label:
  forall (mk_instr: ireg -> Asm.offset -> Asm.instruction) addr args k c,
  (forall r o, nolabel (mk_instr r o)) ->
  transl_memory_access mk_instr addr args k = OK c ->
  tail_nolabel k c.
FProofLemma.
unfold transl_memory_access; intros; destruct addr; TailNoLabel. (*monadInv H0.*) apply indexed_memory_access_label; auto. apply indexed_memory_access_label; auto.
Qed. CloseFLemma.

FInduction transl_instr_label about S.instruction motive
  (fun (i: S.instruction) => forall f ep k c,
       transl_instr i f ep k = OK c -> transl_instr_label_sig i c k).
FProof.
all: fsimpl; intros; TailNoLabel; fsimpl; fsimpl in H.
+ eapply transl_op_label; eauto.
+ eapply transl_cbranch_label; eauto.
+ monadInv H; reflexivity.
+ monadInv H. TailNoLabel.
+ eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel].
+ eapply loadind_label; eauto.
+ destruct ep. monadInv H.  eapply loadind_label; eauto. monadInv H.
  eapply tail_nolabel_trans. apply loadind_ptr_label. eapply loadind_label; eauto.
+ eapply storeind_label; eauto.
(* Heap *)
+ destruct m; monadInv H;  eapply transl_memory_access_label; eauto; intros; exact I.
+ destruct m; monadInv H;  eapply transl_memory_access_label; eauto; intros; exact I.
Qed. FEnd transl_instr_label.

FInduction transl_instr_label' about S.instruction
  motive (fun (i : S.instruction) =>
    forall lbl f ep k c,
      transl_instr i f ep k = OK c ->
      find_label lbl c = if S.is_label i lbl then Some k else find_label lbl k).
FProof.
all: intros; exploit transl_instr_label; eauto; do 2 fsimpl; try (intros [A B]; apply B).
+ intros. subst c. simpl. unfold Asm.is_labelPlabel. auto.
Qed. FEnd transl_instr_label'.

FInduction is_mach_label_correct about S.instruction
  motive (fun (instr : S.instruction) => forall lbl,
  if S.is_label instr lbl then instr = S.Llabel lbl else instr <> S.Llabel lbl).
FProof.
all: intros; fsimpl.
+ fdiscriminate.
+ fdiscriminate. + destruct (peq lbl l); subst. auto. fdiscriminate. + fdiscriminate. + fdiscriminate.
+ fdiscriminate. + fdiscriminate. + fdiscriminate.
(* Heap *)
+ fdiscriminate. + fdiscriminate.
Qed. FEnd is_mach_label_correct.

FLemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match S.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
FProofLemma.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' _ lbl _ _ _ _ EQ0).
  generalize (is_mach_label_correct a lbl).
  destruct (S.is_label a lbl); intros.
  subst a. simpl in EQ. exists x; auto.
  fsimpl in EQ. fsimpl in EQ0. auto. eapply IHc; eauto.
Qed. CloseFLemma.

FLemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match S.find_label lbl (S.fn_code f) with
  | None => find_label lbl (Asm.fn_code tf) = None
  | Some c => exists tc, find_label lbl (Asm.fn_code tf) = Some tc /\ transl_code f c false = OK tc
  end.
FProofLemma.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (Asm.fn_code x))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0. unfold Asm.fn_code.
  simpl. erewrite tail_nolabel_find_label by (apply storeind_ptr_label). simpl.
  eapply transl_code_label; eauto.
Qed. CloseFLemma.

FLemma find_label_goto_label:
  forall ge f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  S.find_label lbl (S.fn_code f) = Some c' ->
  exists tc', exists rs',
    Asm.goto_label tf lbl rs m = Asm.Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
FProofLemma.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold Asm.goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. lia.
  generalize (transf_function_no_overflow _ _ H0). lia.
  intros. apply Pregmap.gso; auto.
Qed. CloseFLemma.

MetaData ArgsInv.
Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
  end).
FEnd ArgsInv.

MetaData Simpl.
Lemma nextinstr_pc:
  forall rs, (Asm.nextinstr rs)#PC = Val.offset_ptr rs#PC Ptrofs.one.
Proof.
  intros. apply Pregmap.gss.
Qed.

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (Asm.nextinstr rs)#r = rs#r.
Proof.
  intros. unfold Asm.nextinstr. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextinstr_inv1:
  forall r rs, data_preg r = true -> (Asm.nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

Lemma ireg_of_not_X31:
  forall m r, ireg_of m = OK r -> IR r <> IR X31.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.

Lemma ireg_of_not_X31':
  forall m r, ireg_of m = OK r -> r <> X31.
Proof.
  intros. apply ireg_of_not_X31 in H. congruence.
Qed.

Global Hint Resolve ireg_of_not_X31 ireg_of_not_X31': asmgen.

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.
FEnd Simpl.

(** * Correctness of RISC-V constructor functions *)
MetaData CONSTRUCTORS.

(** Decomposition of integer constants. *)

Lemma make_immed32_sound:
  forall n,
  match make_immed32 n with
  | Imm32_single imm => n = imm
  | Imm32_pair hi lo => n = Int.add (Int.shl hi (Int.repr 12)) lo
  end.
Proof.
  intros; unfold make_immed32. set (lo := Int.sign_ext 12 n).
  predSpec Int.eq Int.eq_spec n lo.
- auto.
- set (m := Int.sub n lo).
  assert (A: eqmod (two_p 12) (Int.unsigned lo) (Int.unsigned n)) by (apply Int.eqmod_sign_ext'; compute; auto).
  assert (B: eqmod (two_p 12) (Int.unsigned n - Int.unsigned  lo) 0).
  { replace 0 with (Int.unsigned n - Int.unsigned n) by lia.
    auto using eqmod_sub, eqmod_refl. }
  assert (C: eqmod (two_p 12) (Int.unsigned m) 0).
  { apply eqmod_trans with (Int.unsigned n - Int.unsigned lo); auto.
    apply eqmod_divides with Int.modulus. apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
    exists (two_p (32-12)); auto. }
  assert (D: Int.modu m (Int.repr 4096) = Int.zero).
  { apply eqmod_mod_eq in C. unfold Int.modu.
    change (Int.unsigned (Int.repr 4096)) with (two_p 12). rewrite C.
    reflexivity.
    apply two_p_gt_ZERO; lia. }
  rewrite <- (Int.divu_pow2 m (Int.repr 4096) (Int.repr 12)) by auto.
  rewrite Int.shl_mul_two_p.
  change (two_p (Int.unsigned (Int.repr 12))) with 4096.
  replace (Int.mul (Int.divu m (Int.repr 4096)) (Int.repr 4096)) with m.
  unfold m. rewrite Int.sub_add_opp. rewrite Int.add_assoc. rewrite <- (Int.add_commut lo).
  rewrite Int.add_neg_zero. rewrite Int.add_zero. auto.
  rewrite (Int.modu_divu_Euclid m (Int.repr 4096)) at 1 by (vm_compute; congruence).
  rewrite D. apply Int.add_zero.
Qed.

Lemma make_immed64_sound:
  forall n,
  match make_immed64 n with
  | Imm64_single imm => n = imm
  | Imm64_pair hi lo => n = Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo
  | Imm64_large imm => n = imm
  end.
Proof.
  intros; unfold make_immed64. set (lo := Int64.sign_ext 12 n).
  predSpec Int64.eq Int64.eq_spec n lo.
- auto.
- set (m := Int64.sub n lo).
  set (p := Int64.zero_ext 20 (Int64.shru m (Int64.repr 12))).
  predSpec Int64.eq Int64.eq_spec n (Int64.add (Int64.sign_ext 32 (Int64.shl p (Int64.repr 12))) lo).
  auto.
  auto.
Qed.

Section CONSTRUCTORS.
Import Asm.
Variable ge: genv.
Variable fn: function.

(** 32-bit integer constants and arithmetic *)

Lemma load_hilo32_correct:
  forall rd hi lo k rs m,
  exists rs',
     exec_straight ge fn (load_hilo32 rd hi lo k) rs m k rs' m
  /\ rs'#rd = Vint (Int.add (Int.shl hi (Int.repr 12)) lo)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold load_hilo32; intros.
  predSpec Int.eq Int.eq_spec lo Int.zero.
- subst lo. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split. rewrite Int.add_zero. Simpl.
  intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  simpl. split. Simpl.
  intros; Simpl.
Qed.

Lemma loadimm32_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm32 rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm32; intros. generalize (make_immed32_sound n); intros E.
  destruct (make_immed32 n).
- subst imm. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split. simpl. rewrite Int.add_zero_l; Simpl.
  intros; Simpl.
- rewrite E. apply load_hilo32_correct.
Qed.

Lemma opimm32_correct:
  forall (op: ireg -> ireg0 -> ireg0 -> instruction)
         (opi: ireg -> ireg0 -> int -> instruction)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_instr (op d s1 s2) ge fn rs m = Next (nextinstr (rs#d <- (sem rs##s1 rs##s2))) m) ->
  (forall d s n rs,
   exec_instr (opi d s n) ge fn rs m = Next (nextinstr (rs#d <- (sem rs##s (Vint n)))) m) ->
  forall rd r1 n k rs,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (opimm32 op opi rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs##r1 (Vint n)
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold opimm32. generalize (make_immed32_sound n); intros E.
  destruct (make_immed32 n).
- subst imm. econstructor; split.
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
- destruct (load_hilo32_correct X31 hi lo (op rd r1 X31 :: k) rs m)
  as (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  rewrite H; eauto. auto.
  split. Simpl. simpl. rewrite B, C, E. auto. congruence. congruence.
  intros; Simpl.
Qed.

(** 64-bit integer constants and arithmetic *)

Lemma load_hilo64_correct:
  forall rd hi lo k rs m,
  exists rs',
     exec_straight ge fn (load_hilo64 rd hi lo k) rs m k rs' m
  /\ rs'#rd = Vlong (Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold load_hilo64; intros.
  predSpec Int64.eq Int64.eq_spec lo Int64.zero.
- subst lo. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split. rewrite Int64.add_zero. Simpl.
  intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  simpl. split. Simpl.
  intros; Simpl.
Qed.

Lemma loadimm64_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm64 rd n k) rs m k rs' m
  /\ rs'#rd = Vlong n
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  unfold loadimm64; intros. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n).
- subst imm. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split. simpl. rewrite Int64.add_zero_l; Simpl.
  intros; Simpl.
- exploit load_hilo64_correct; eauto. intros (rs' & A & B & C).
  rewrite E. exists rs'; eauto.
- subst imm. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split. Simpl.
  intros; Simpl.
Qed.

Lemma opimm64_correct:
  forall (op: ireg -> ireg0 -> ireg0 -> instruction)
         (opi: ireg -> ireg0 -> int64 -> instruction)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_instr (op d s1 s2) ge fn rs m = Next (nextinstr (rs#d <- (sem rs###s1 rs###s2))) m) ->
  (forall d s n rs,
   exec_instr (opi d s n) ge fn rs m = Next (nextinstr (rs#d <- (sem rs###s (Vlong n)))) m) ->
  forall rd r1 n k rs,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (opimm64 op opi rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs##r1 (Vlong n)
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold opimm64. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n).
- subst imm. econstructor; split.
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
- destruct (load_hilo64_correct X31 hi lo (op rd r1 X31 :: k) rs m)
  as (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  rewrite H; eauto. auto.
  split. Simpl. simpl. rewrite B, C, E. auto. congruence. congruence.
  intros; Simpl.
- subst imm. econstructor; split.
  eapply exec_straight_two. reflexivity. rewrite H. simpl; eauto. auto. auto.
  split. Simpl. intros; Simpl.
Qed.

(** Add offset to pointer *)

Lemma addptrofs_correct:
  forall rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  unfold addptrofs; intros.
  destruct (Ptrofs.eq_dec n Ptrofs.zero).
- subst n. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split. Simpl. destruct (rs r1); simpl; auto. rewrite Ptrofs.add_zero; auto.
  intros; Simpl.
- destruct Archi.ptr64 eqn:SF.
+ unfold addimm64.
  exploit (opimm64_correct Paddl Paddil Val.addl); eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto.
  rewrite B. simpl. destruct (rs r1); simpl; auto. rewrite SF.
  rewrite Ptrofs.of_int64_to_int64 by auto. auto.
+ unfold addimm32.
  exploit (opimm32_correct Paddw Paddiw Val.add); eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto.
  rewrite B. simpl. destruct (rs r1); simpl; auto. rewrite SF.
  rewrite Ptrofs.of_int_to_int by auto. auto.
Qed.

Lemma addptrofs_correct_2:
  forall rd r1 n k (rs: regset) m b ofs,
  r1 <> X31 -> rs#r1 = Vptr b ofs ->
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ rs'#rd = Vptr b (Ptrofs.add ofs n)
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. exploit (addptrofs_correct rd r1 n); eauto. intros (rs' & A & B & C).
  exists rs'; intuition eauto.
  rewrite H0 in B. inv B. auto.
Qed.

(** Translation of conditional branches *)

Lemma transl_cbranch_int32s_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmp_bool cmp rs##r1 rs##r2 = Some b ->
  exec_instr (transl_cbranch_int32s cmp r1 r2 lbl) ge fn rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; unfold exec_instrPbeqw, exec_instrPbnew, exec_instrPbltw, exec_instrPbgew; rewrite ? H.
- destruct rs##r1; simpl in H; try discriminate. destruct rs##r2; inv H.
  simpl; auto.
- destruct rs##r1; simpl in H; try discriminate. destruct rs##r2; inv H.
  simpl; auto.
- auto.
- rewrite <- Val.swap_cmp_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmp_bool. simpl. rewrite H; auto.
- auto.
Qed.

Lemma transl_cbranch_int32u_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmpu_bool (Mem.valid_pointer m) cmp rs##r1 rs##r2 = Some b ->
  exec_instr (transl_cbranch_int32u cmp r1 r2 lbl) ge fn rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; unfold exec_instrPbeqw, exec_instrPbnew, exec_instrPbltuw, exec_instrPbgeuw; rewrite ? H; auto.
- rewrite <- Val.swap_cmpu_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmpu_bool. simpl. rewrite H; auto.
Qed.

Lemma transl_cbranch_int64s_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmpl_bool cmp rs###r1 rs###r2 = Some b ->
  exec_instr (transl_cbranch_int64s cmp r1 r2 lbl) ge fn rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; unfold exec_instrPbeql, exec_instrPbnel, exec_instrPbltl, exec_instrPbgel; rewrite ? H.
- destruct rs###r1; simpl in H; try discriminate. destruct rs###r2; inv H.
  simpl; auto.
- destruct rs###r1; simpl in H; try discriminate. destruct rs###r2; inv H.
  simpl; auto.
- auto.
- rewrite <- Val.swap_cmpl_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmpl_bool. simpl. rewrite H; auto.
- auto.
Qed.

Lemma transl_cbranch_int64u_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmplu_bool (Mem.valid_pointer m) cmp rs###r1 rs###r2 = Some b ->
  exec_instr (transl_cbranch_int64u cmp r1 r2 lbl) ge fn rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; unfold exec_instrPbeql, exec_instrPbnel, exec_instrPbltul, exec_instrPbgeul; rewrite ? H; auto.
- rewrite <- Val.swap_cmplu_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmplu_bool. simpl. rewrite H; auto.
Qed.

Lemma transl_cond_float_correct:
  forall (rs: regset) m cmp rd r1 r2 insn normal v,
  transl_cond_float cmp rd r1 r2 = (insn, normal) ->
  v = (if normal then Val.cmpf cmp rs#r1 rs#r2 else Val.notbool (Val.cmpf cmp rs#r1 rs#r2)) ->
  exec_instr insn ge fn rs m = Next (nextinstr (rs#rd <- v)) m.
Proof.
  intros. destruct cmp; simpl in H; inv H; auto.
- rewrite Val.negate_cmpf_eq. auto.
- simpl. unfold exec_instrPfltd. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpf, Val.cmpf_bool.
  rewrite <- Float.cmp_swap. auto.
- simpl. unfold exec_instrPfled. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpf, Val.cmpf_bool.
  rewrite <- Float.cmp_swap. auto.
Qed.

Lemma transl_cond_single_correct:
  forall (rs: regset) m cmp rd r1 r2 insn normal v,
  transl_cond_single cmp rd r1 r2 = (insn, normal) ->
  v = (if normal then Val.cmpfs cmp rs#r1 rs#r2 else Val.notbool (Val.cmpfs cmp rs#r1 rs#r2)) ->
  exec_instr insn ge fn rs m = Next (nextinstr (rs#rd <- v)) m.
Proof.
  intros. destruct cmp; simpl in H; inv H; auto.
- simpl. unfold exec_instrPfeqs. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpfs, Val.cmpfs_bool.
  rewrite Float32.cmp_ne_eq. destruct (Float32.cmp Ceq f0 f); auto.
- simpl. unfold exec_instrPflts. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpfs, Val.cmpfs_bool.
  rewrite <- Float32.cmp_swap. auto.
- simpl. unfold exec_instrPfles. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpfs, Val.cmpfs_bool.
  rewrite <- Float32.cmp_swap. auto.
Qed.

Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr insn ge fn rs' m' = eval_branch fn lbl rs' m' (Some b)
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)).
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_lessdef with (map ms args) m; auto. eapply preg_vals; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
- exists rs, (transl_cbranch_int32s c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32s_correct; auto.
- exists rs, (transl_cbranch_int32u c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32u_correct; auto.
- predSpec Int.eq Int.eq_spec n Int.zero.
+ subst n. exists rs, (transl_cbranch_int32s c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32s_correct; auto.
+ exploit (loadimm32_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int32s c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int32s_correct; auto.
  simpl; rewrite B, C; try congruence; eauto with asmgen.
- predSpec Int.eq Int.eq_spec n Int.zero.
+ subst n. exists rs, (transl_cbranch_int32u c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32u_correct; auto.
+ exploit (loadimm32_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int32u c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int32u_correct; auto.
  simpl; rewrite B, C; try congruence; eauto with asmgen.
- exists rs, (transl_cbranch_int64s c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64s_correct; auto.
- exists rs, (transl_cbranch_int64u c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64u_correct; auto.
- predSpec Int64.eq Int64.eq_spec n Int64.zero.
+ subst n. exists rs, (transl_cbranch_int64s c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64s_correct; auto.
+ exploit (loadimm64_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int64s c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int64s_correct; auto.
  simpl; rewrite B, C; try congruence; eauto with asmgen.
- predSpec Int64.eq Int64.eq_spec n Int64.zero.
+ subst n. exists rs, (transl_cbranch_int64u c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64u_correct; auto.
+ exploit (loadimm64_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int64u c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int64u_correct; auto.
  simpl; rewrite B, C; try congruence; eauto with asmgen.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  set (v := if normal then Val.cmpf c0 rs#x rs#x0 else Val.notbool (Val.cmpf c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (eqb normal b)).
  { unfold v, Val.cmpf. rewrite EVAL'. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  assert (EVAL'': Val.cmpf_bool c0 (rs x) (rs x0) = Some (negb b)).
  { destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; inv EVAL'; auto. }
  set (v := if normal then Val.cmpf c0 rs#x rs#x0 else Val.notbool (Val.cmpf c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (xorb normal b)).
  { unfold v, Val.cmpf. rewrite EVAL''. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  set (v := if normal then Val.cmpfs c0 rs#x rs#x0 else Val.notbool (Val.cmpfs c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (eqb normal b)).
  { unfold v, Val.cmpfs. rewrite EVAL'. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  assert (EVAL'': Val.cmpfs_bool c0 (rs x) (rs x0) = Some (negb b)).
  { destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; inv EVAL'; auto. }
  set (v := if normal then Val.cmpfs c0 rs#x rs#x0 else Val.notbool (Val.cmpfs c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (xorb normal b)).
  { unfold v, Val.cmpfs. rewrite EVAL''. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
Qed.

Lemma transl_cbranch_correct_true:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr insn ge fn rs' m' = goto_label fn lbl rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed.

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1; eauto. simpl.
  intros (rs' & insn & A & B & C).
  exists (nextinstr rs').
  split. eapply exec_straight_opt_right; eauto. apply exec_straight_one; auto.
  intros; Simpl.
Qed.

(** Translation of condition operators *)

Lemma transl_cond_int32s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32s cmp rd r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs##r1 rs##r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. destruct (rs##r1); auto. destruct (rs##r2); auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. destruct (rs##r1); auto. destruct (rs##r2); auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmp. rewrite <- Val.swap_cmp_bool.
  simpl. rewrite (Val.negate_cmp_bool Clt).
  destruct (Val.cmp_bool Clt rs##r2 rs##r1) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. unfold Val.cmp. rewrite <- Val.swap_cmp_bool. auto.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmp. rewrite (Val.negate_cmp_bool Clt).
  destruct (Val.cmp_bool Clt rs##r1 rs##r2) as [[]|]; auto.
Qed.

Lemma transl_cond_int32u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32u cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.cmpu (Mem.valid_pointer m) cmp rs##r1 rs##r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmpu. rewrite <- Val.swap_cmpu_bool.
  simpl. rewrite (Val.negate_cmpu_bool (Mem.valid_pointer m) Cle).
  destruct (Val.cmpu_bool (Mem.valid_pointer m) Cle rs##r1 rs##r2) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. unfold Val.cmpu. rewrite <- Val.swap_cmpu_bool. auto.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmpu. rewrite (Val.negate_cmpu_bool (Mem.valid_pointer m) Clt).
  destruct (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##r1 rs##r2) as [[]|]; auto.
Qed.

Lemma transl_cond_int64s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int64s cmp rd r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs###r1 rs###r2)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. destruct (rs###r1); auto. destruct (rs###r2); auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. destruct (rs###r1); auto. destruct (rs###r2); auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmpl. rewrite <- Val.swap_cmpl_bool.
  simpl. rewrite (Val.negate_cmpl_bool Clt).
  destruct (Val.cmpl_bool Clt rs###r2 rs###r1) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. unfold Val.cmpl. rewrite <- Val.swap_cmpl_bool. auto.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmpl. rewrite (Val.negate_cmpl_bool Clt).
  destruct (Val.cmpl_bool Clt rs###r1 rs###r2) as [[]|]; auto.
Qed.

Lemma transl_cond_int64u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int64u cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs###r1 rs###r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmplu. rewrite <- Val.swap_cmplu_bool.
  simpl. rewrite (Val.negate_cmplu_bool (Mem.valid_pointer m) Cle).
  destruct (Val.cmplu_bool (Mem.valid_pointer m) Cle rs###r1 rs###r2) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [reflexivity|auto].
  split; intros; Simpl. unfold Val.cmplu. rewrite <- Val.swap_cmplu_bool. auto.
- econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold Val.cmplu. rewrite (Val.negate_cmplu_bool (Mem.valid_pointer m) Clt).
  destruct (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###r1 rs###r2) as [[]|]; auto.
Qed.

Lemma transl_condimm_int32s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32s cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int32s.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. exploit transl_cond_int32s_correct. intros (rs' & A & B & C).
  exists rs'; eauto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm32 X31 n (transl_cond_int32s cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.cmp cmp rs#r1 (Vint n)) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int32s_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split.
    eapply exec_straight_trans. eexact A1. eexact A2.
    split. simpl in B2. rewrite B1, C1 in B2 by congruence. auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ unfold xorimm32.
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int32s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split.
  eapply exec_straight_trans. eexact A1. eexact A2.
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmp in B2; simpl in B2; rewrite Int.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ unfold xorimm32.
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int32s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split.
  eapply exec_straight_trans. eexact A1. eexact A2.
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmp in B2; simpl in B2; rewrite Int.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ exploit (opimm32_correct Psltw Psltiw (Val.cmp Clt)); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ predSpec Int.eq Int.eq_spec n (Int.repr Int.max_signed).
* subst n. exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto.
  unfold Val.cmp; destruct (rs#r1); simpl; auto. rewrite B1.
  unfold Int.lt. rewrite zlt_false. auto.
  change (Int.signed (Int.repr Int.max_signed)) with Int.max_signed.
  generalize (Int.signed_range i); lia.
* exploit (opimm32_correct Psltw Psltiw (Val.cmp Clt)); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto.
  rewrite B1. unfold Val.cmp; simpl; destruct (rs#r1); simpl; auto.
  unfold Int.lt. replace (Int.signed (Int.add n Int.one)) with (Int.signed n + 1).
  destruct (zlt (Int.signed n) (Int.signed i)).
  rewrite zlt_false by lia. auto.
  rewrite zlt_true by lia. auto.
  rewrite Int.add_signed. symmetry; apply Int.signed_repr.
  assert (Int.signed n <> Int.max_signed).
  { red; intros E. elim H1. rewrite <- (Int.repr_signed n). rewrite E. auto. }
  generalize (Int.signed_range n); lia.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_condimm_int32u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32u cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int32u.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. exploit transl_cond_int32u_correct. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto. rewrite B; auto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm32 X31 n (transl_cond_int32u cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (Vint n)) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int32u_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split.
    eapply exec_straight_trans. eexact A1. eexact A2.
    split. simpl in B2. rewrite B1, C1 in B2 by congruence. rewrite B2; auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ apply DFL.
+ apply DFL.
+ exploit (opimm32_correct Psltuw Psltiuw (Val.cmpu (Mem.valid_pointer m) Clt) m); eauto.
  intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ apply DFL.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_condimm_int64s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int64s cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int64s.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
- subst n. exploit transl_cond_int64s_correct. intros (rs' & A & B & C).
  exists rs'; eauto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm64 X31 n (transl_cond_int64s cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 (Vlong n))) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm64_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int64s_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split.
    eapply exec_straight_trans. eexact A1. eexact A2.
    split. simpl in B2. rewrite B1, C1 in B2 by congruence. auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ unfold xorimm64.
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int64s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split.
  eapply exec_straight_trans. eexact A1. eexact A2.
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmpl in B2; simpl in B2; rewrite Int64.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ unfold xorimm64.
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int64s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split.
  eapply exec_straight_trans. eexact A1. eexact A2.
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmpl in B2; simpl in B2; rewrite Int64.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ exploit (opimm64_correct Psltl Psltil (fun v1 v2 => Val.maketotal (Val.cmpl Clt v1 v2))); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ predSpec Int64.eq Int64.eq_spec n (Int64.repr Int64.max_signed).
* subst n. exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto.
  unfold Val.cmpl; destruct (rs#r1); simpl; auto. rewrite B1.
  unfold Int64.lt. rewrite zlt_false. auto.
  change (Int64.signed (Int64.repr Int64.max_signed)) with Int64.max_signed.
  generalize (Int64.signed_range i); lia.
* exploit (opimm64_correct Psltl Psltil (fun v1 v2 => Val.maketotal (Val.cmpl Clt v1 v2))); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto.
  rewrite B1. unfold Val.cmpl; simpl; destruct (rs#r1); simpl; auto.
  unfold Int64.lt. replace (Int64.signed (Int64.add n Int64.one)) with (Int64.signed n + 1).
  destruct (zlt (Int64.signed n) (Int64.signed i)).
  rewrite zlt_false by lia. auto.
  rewrite zlt_true by lia. auto.
  rewrite Int64.add_signed. symmetry; apply Int64.signed_repr.
  assert (Int64.signed n <> Int64.max_signed).
  { red; intros E. elim H1. rewrite <- (Int64.repr_signed n). rewrite E. auto. }
  generalize (Int64.signed_range n); lia.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_condimm_int64u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int64u cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int64u.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
- subst n. exploit transl_cond_int64u_correct. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto. rewrite B; auto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm64 X31 n (transl_cond_int64u cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs#r1 (Vlong n))) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm64_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int64u_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split.
    eapply exec_straight_trans. eexact A1. eexact A2.
    split. simpl in B2. rewrite B1, C1 in B2 by congruence. rewrite B2; auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ apply DFL.
+ apply DFL.
+ exploit (opimm64_correct Psltul Psltiul (fun v1 v2 => Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt v1 v2)) m); eauto.
  intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ apply DFL.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
+ (* cmp *)
  exploit transl_cond_int32s_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpu *)
  exploit transl_cond_int32u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B; auto.
+ (* cmpimm *)
  apply transl_condimm_int32s_correct; eauto with asmgen.
+ (* cmpuimm *)
  apply transl_condimm_int32u_correct; eauto with asmgen.
+ (* cmpl *)
  exploit transl_cond_int64s_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmplu *)
  exploit transl_cond_int64u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B, MKTOT; eauto.
+ (* cmplimm *)
  exploit transl_condimm_int64s_correct; eauto. instantiate (1 := x); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpluimm *)
  exploit transl_condimm_int64u_correct; eauto. instantiate (1 := x); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpf *)
  destruct (transl_cond_float c0 rd x x0) as [insn normal] eqn:TR.
  fold (Val.cmpf c0 (rs x) (rs x0)).
  set (v := Val.cmpf c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split; intros; Simpl.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_float_correct with (v := Val.notbool v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold v, Val.cmpf. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; auto.
+ (* notcmpf *)
  destruct (transl_cond_float c0 rd x x0) as [insn normal] eqn:TR.
  rewrite Val.notbool_negb_3. fold (Val.cmpf c0 (rs x) (rs x0)).
  set (v := Val.cmpf c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_float_correct with (v := v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold v, Val.cmpf. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; auto.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_float_correct with (v := Val.notbool v); eauto. auto.
  split; intros; Simpl.
+ (* cmpfs *)
  destruct (transl_cond_single c0 rd x x0) as [insn normal] eqn:TR.
  fold (Val.cmpfs c0 (rs x) (rs x0)).
  set (v := Val.cmpfs c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split; intros; Simpl.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_single_correct with (v := Val.notbool v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold v, Val.cmpfs. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; auto.
+ (* notcmpfs *)
  destruct (transl_cond_single c0 rd x x0) as [insn normal] eqn:TR.
  rewrite Val.notbool_negb_3. fold (Val.cmpfs c0 (rs x) (rs x0)).
  set (v := Val.cmpfs c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_single_correct with (v := v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold v, Val.cmpfs. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; auto.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_single_correct with (v := Val.notbool v); eauto. auto.
  split; intros; Simpl.
Qed.

(** Some arithmetic properties. *)

Remark cast32unsigned_from_cast32signed:
  forall i, Int64.repr (Int.unsigned i) = Int64.zero_ext 32 (Int64.repr (Int.signed i)).
Proof.
  intros. apply Int64.same_bits_eq; intros.
  rewrite Int64.bits_zero_ext, !Int64.testbit_repr by tauto.
  rewrite Int.bits_signed by tauto. fold (Int.testbit i i0).
  change Int.zwordsize with 32.
  destruct (zlt i0 32). auto. apply Int.bits_above. auto.
Qed.

(* Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [reflexivity | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.
- (* move *)
  destruct (preg_of res), (preg_of m0); inv TR; TranslOpSimpl.
- (* intconst *)
  exploit loadimm32_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* longconst *)
  exploit loadimm64_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* floatconst *)
  destruct (Float.eq_dec n Float.zero).
+ subst n. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl.
+ econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl.
- (* singleconst *)
  destruct (Float32.eq_dec n Float32.zero).
+ subst n. econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl.
+ econstructor; split.
  apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl.
- (* addrsymbol *)
  destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)).
+ set (rs1 := nextinstr (rs#x <- (Genv.symbol_address ge id Ptrofs.zero))).
  exploit (addptrofs_correct x x ofs k rs1 m); eauto with asmgen.
  intros (rs2 & A & B & C).
  exists rs2; split.
  apply exec_straight_step with rs1 m; auto.
  split. replace ofs with (Ptrofs.add Ptrofs.zero ofs) by (apply Ptrofs.add_zero_l).
  rewrite Genv.shift_symbol_address.
  replace (rs1 x) with (Genv.symbol_address ge id Ptrofs.zero) in B by (unfold rs1; Simpl).
  exact B.
  intros. rewrite C by eauto with asmgen. unfold rs1; Simpl.
+ TranslOpSimpl.
- (* stackoffset *)
  exploit addptrofs_correct. instantiate (1 := X2); congruence. intros (rs' & A & B & C).
  exists rs'; split; eauto. auto with asmgen.
- (* cast8signed *)
  econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl.
  assert (A: Int.ltu (Int.repr 24) Int.iwordsize = true) by auto.
  destruct (rs x0); auto; simpl. rewrite A; simpl. rewrite A.
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. compute; intuition congruence.
- (* cast16signed *)
  econstructor; split.
  eapply exec_straight_two. reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl.
  assert (A: Int.ltu (Int.repr 16) Int.iwordsize = true) by auto.
  destruct (rs x0); auto; simpl. rewrite A; simpl. rewrite A.
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. compute; intuition congruence.
- (* addimm *)
  exploit (opimm32_correct Paddw Paddiw Val.add); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* andimm *)
  exploit (opimm32_correct Pandw Pandiw Val.and); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* orimm *)
  exploit (opimm32_correct Porw Poriw Val.or); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* xorimm *)
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* shrximm *)
  clear H. exploit Val.shrx_shr_2; eauto. intros E; subst v; clear EV.
  destruct (Int.eq n Int.zero).
+ econstructor; split. apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl.
+ change (Int.repr 32) with Int.iwordsize. set (n' := Int.sub Int.iwordsize n).
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_step. simpl; reflexivity. auto.
  apply exec_straight_one. simpl; reflexivity. auto.
  split; intros; Simpl.
- (* longofintu *)
  econstructor; split.
  eapply exec_straight_three. reflexivity. reflexivity. reflexivity. auto. auto. auto.
  split; intros; Simpl; simpl; Simpl. destruct (rs x0); auto. simpl.
  assert (A: Int.ltu (Int.repr 32) Int64.iwordsize' = true) by auto.
  rewrite A; simpl. rewrite A. apply Val.lessdef_same. f_equal.
  rewrite cast32unsigned_from_cast32signed. apply Int64.zero_ext_shru_shl. compute; auto.
- (* addlimm *)
  exploit (opimm64_correct Paddl Paddil Val.addl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* andimm *)
  exploit (opimm64_correct Pandl Pandil Val.andl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* orimm *)
  exploit (opimm64_correct Porl Poril Val.orl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* xorimm *)
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* shrxlimm *)
  clear H. exploit Val.shrxl_shrl_2; eauto. intros E; subst v; clear EV.
  destruct (Int.eq n Int.zero).
+ econstructor; split. apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl.
+ change (Int.repr 64) with Int64.iwordsize'. set (n' := Int.sub Int64.iwordsize' n).
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_step. simpl; reflexivity. auto.
  apply exec_straight_one. simpl; reflexivity. auto.
  split; intros; Simpl.
- (* cond *)
  exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. eauto with asmgen.
Qed.

(** Memory accesses *)

Lemma indexed_memory_access_correct:
  forall mk_instr base ofs k rs m,
  base <> X31 ->
  exists base' ofs' rs',
     exec_straight_opt ge fn (indexed_memory_access mk_instr base ofs k) rs m
                       (mk_instr base' ofs' :: k) rs' m
  /\ Val.offset_ptr rs'#base' (eval_offset ge ofs') = Val.offset_ptr rs#base ofs
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  unfold indexed_memory_access; intros.
  destruct Archi.ptr64 eqn:SF.
- generalize (make_immed64_sound (Ptrofs.to_int64 ofs)); intros EQ.
  destruct (make_immed64 (Ptrofs.to_int64 ofs)).
+ econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
+ econstructor; econstructor; econstructor; split.
  constructor. eapply exec_straight_two.
  reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal.
  rewrite <- (Ptrofs.of_int64_to_int64 SF ofs). rewrite EQ.
  symmetry; auto with ptrofs.
+ econstructor; econstructor; econstructor; split.
  constructor. eapply exec_straight_two.
  reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. unfold eval_offset. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_zero. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
- generalize (make_immed32_sound (Ptrofs.to_int ofs)); intros EQ.
  destruct (make_immed32 (Ptrofs.to_int ofs)).
+ econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int_to_int by auto. auto.
+ econstructor; econstructor; econstructor; split.
  constructor. eapply exec_straight_two.
  reflexivity. reflexivity. auto. auto.
  split; intros; Simpl; simpl; Simpl. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal.
  rewrite <- (Ptrofs.of_int_to_int SF ofs). rewrite EQ.
  symmetry; auto with ptrofs.
Qed.

Lemma indexed_load_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) rd m,
  (forall base ofs rs,
     exec_instr (mk_instr base ofs) ge fn rs m = exec_load ge chunk rs m rd base ofs) ->
  forall (base: ireg) ofs k (rs: regset) v,
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> X31 -> rd <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base ofs k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, r <> PC -> r <> X31 -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until v; intros LOAD NOT31 NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_load. rewrite B, LOAD. eauto. Simpl.
  split; intros; Simpl.
Qed.

Lemma indexed_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) r1 m,
  (forall base ofs rs,
     exec_instr (mk_instr base ofs) ge fn rs m = exec_store ge chunk rs m r1 base ofs) ->
  forall (base: ireg) ofs k (rs: regset) m',
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs#r1) = Some m' ->
  base <> X31 -> r1 <> X31 -> r1 <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until m'; intros STORE NOT31 NOT31' NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_store. rewrite B, C, STORE by auto. eauto. auto.
  intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> X31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> X31 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR LOAD NOT31.
  assert (A: exists mk_instr,
                c = indexed_memory_access mk_instr base ofs k
             /\ forall base' ofs' rs',
                   exec_instr (mk_instr base' ofs') ge fn rs' m =
                   exec_load ge (chunk_of_type ty) rs' m (preg_of dst) base' ofs').
  { unfold loadind in TR. destruct ty, (preg_of dst); inv TR; econstructor; split; eauto. }
  destruct A as (mk_instr & B & C). subst c.
  eapply indexed_load_access_correct; eauto with asmgen.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  base <> X31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR STORE NOT31.
  assert (A: exists mk_instr,
                c = indexed_memory_access mk_instr base ofs k
             /\ forall base' ofs' rs',
                   exec_instr (mk_instr base' ofs') ge fn rs' m =
                   exec_store ge (chunk_of_type ty) rs' m (preg_of src) base' ofs').
  { unfold storeind in TR. destruct ty, (preg_of src); inv TR; econstructor; split; eauto. }
  destruct A as (mk_instr & B & C). subst c.
  eapply indexed_store_access_correct; eauto with asmgen.
Qed.

Lemma loadind_ptr_correct:
  forall (base: ireg) ofs (dst: ireg) k (rs: regset) m v,
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> X31 ->
  exists rs',
     exec_straight ge fn (loadind_ptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> X31 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_load_access_correct; eauto with asmgen.
  intros. unfold Mptr. destruct Archi.ptr64; auto.
Qed.

Lemma storeind_ptr_correct:
  forall (base: ireg) ofs (src: ireg) k (rs: regset) m m',
  Mem.storev Mptr m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  base <> X31 -> src <> X31 ->
  exists rs',
     exec_straight ge fn (storeind_ptr src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_store_access_correct with (r1 := src); eauto with asmgen.
  intros. unfold Mptr. destruct Archi.ptr64; auto.
Qed.

Lemma transl_memory_access_correct:
  forall mk_instr addr args k c (rs: regset) m v,
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  exists base ofs rs',
     exec_straight_opt ge fn c rs m (mk_instr base ofs :: k) rs' m
  /\ Val.offset_ptr rs'#base (eval_offset ge ofs) = v
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV.
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
- (* indexed *)
  inv EV. apply indexed_memory_access_correct; eauto with asmgen.
- (* global *)
  simpl in EV. inv EV. inv TR.  econstructor; econstructor; econstructor; split.
  constructor. apply exec_straight_one. reflexivity. auto.
  split; intros; Simpl. unfold eval_offset. apply low_high_half.
- (* stack *)
  inv TR. inv EV. apply indexed_memory_access_correct; eauto with asmgen.
Qed.

Lemma transl_load_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) addr args k c rd (rs: regset) m v v',
  (forall base ofs rs,
     exec_instr (mk_instr base ofs) ge fn rs m = exec_load ge chunk rs m rd base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> X31 -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros INSTR TR EV LOAD NOTPC.
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one.
  rewrite INSTR. unfold exec_load. rewrite B, LOAD. reflexivity. Simpl.
  split; intros; Simpl.
Qed.

Lemma transl_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) addr args k c r1 (rs: regset) m v m',
  (forall base ofs rs,
     exec_instr (mk_instr base ofs) ge fn rs m = exec_store ge chunk rs m r1 base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> PC -> r1 <> X31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros INSTR TR EV STORE NOTPC NOT31.
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one.
  rewrite INSTR. unfold exec_store. rewrite B, C, STORE by auto. reflexivity. auto.
  intros; Simpl.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> X31 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD.
  assert (A: exists mk_instr,
      transl_memory_access mk_instr addr args k = OK c
   /\ forall base ofs rs,
        exec_instr (mk_instr base ofs) ge fn rs m = exec_load ge chunk rs m (preg_of dst) base ofs).
  { unfold transl_load in TR; destruct chunk; ArgsInv; econstructor; (split; [eassumption|auto]). }
  destruct A as (mk_instr & B & C).
  eapply transl_load_access_correct; eauto with asmgen.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR EV STORE.
  assert (A: exists mk_instr,
      transl_memory_access mk_instr addr args k = OK c
   /\ (forall base ofs rs,
        exec_instr (mk_instr base ofs) ge fn rs m = exec_store ge chunk rs m (preg_of src) base ofs)).
  { unfold transl_store in TR; destruct chunk; ArgsInv;
    (econstructor; split; [eassumption | intros; simpl; reflexivity]).
  }
  destruct A as (mk_instr & B & C).
  eapply transl_store_access_correct; eauto with asmgen.
Qed.

(** Function epilogues *)

Lemma make_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  S.load_stack m (Vptr stk soff) Tptr (S.fn_link_ofs f) = Some (S.parent_sp cs) ->
  S.load_stack m (Vptr stk soff) Tptr (S.fn_retaddr_ofs f) = Some (S.parent_ra cs) ->
  Mem.free m stk 0 (S.fn_stacksize f) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (make_epilogue f k) rs tm k rs' tm'
  /\ agree ms (S.parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#RA = S.parent_ra cs
  /\ rs'#SP = S.parent_sp cs
  /\ (forall r, r <> PC -> r <> RA -> r <> SP -> r <> X31 -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue.
  rewrite chunk_of_Tptr in *.
  exploit (loadind_ptr_correct SP (S.fn_retaddr_ofs f) RA (Pfreeframe (S.fn_stacksize f) (S.fn_link_ofs f) :: k) rs tm).
    rewrite <- (sp_val _ _ _ AG). simpl. eexact LRA'. congruence.
  intros (rs1 & A1 & B1 & C1).
  econstructor; econstructor; split.
  eapply exec_straight_trans. eexact A1. apply exec_straight_one. simpl. unfold exec_instrPfreeframe.
    rewrite (C1 X2) by auto with asmgen. rewrite <- (sp_val _ _ _ AG). simpl; rewrite LP'.
    rewrite FREE'. eauto. auto.
  split. apply agree_nextinstr. apply agree_set_other; auto with asmgen.
    apply agree_change_sp with (Vptr stk soff).
    apply agree_exten with rs; auto. intros; apply C1; auto with asmgen.
    eapply parent_sp_def; eauto.
  split. auto.
  split. Simpl.
  split. Simpl.
  intros. Simpl.
Qed.

End CONSTRUCTORS.
FEnd CONSTRUCTORS.

FLemma preg_of_not_X30: forall r, negb (mreg_eq r R30) = true -> IR X30 <> preg_of r.
FProofLemma.
  intros. change (IR X30) with (preg_of R30). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed. CloseFLemma.

FLemma exec_straight_opt_steps_goto:
  forall prog tprog ge tge,
    match_prog prog tprog ->
    ge = Genv.globalenv prog ->
    tge = Genv.globalenv tprog ->
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
  S.find_label lbl (S.fn_code f) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent i ep = false ->
  (forall k c (TR: transl_instr i f ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ Asm.exec_instr jmp tge tf rs2 m2' = Asm.goto_label tf lbl rs2 m2') ->
  exists st',
  plus Asm.step tge (Asm.State rs1 m1') E0 st' /\
  match_states ge (S.State s fb sp c' ms2 m2) st'.
FProofLemma.
  intros. inversion H6. subst. monadInv H12.
  exploit H8; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl prog tprog H _ _ _ H10 H11); intro FN.
  generalize (transf_function_no_overflow _ _ H11); intro NOOV.
  inv A.
- exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (Asm.State rs3 m2'); split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
- exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (Asm.State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed. CloseFLemma.

From Rocqet Require Import Mregisters.
FInduction step_simulation about S.step
  motive (fun ge S1 t S2 (_ : S.step ge S1 t S2) =>
    forall tge prog tprog (TRANSF: match_prog prog tprog),
    ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
    forall S1' (MS: match_states ge S1 S1'),
    (exists S2', plus Asm.step tge S1' t S2' /\ match_states ge S2 S2')
    \/ (measure S2 < measure S1 /\ t = E0 /\ match_states ge S2 S1')%nat).
FProof.
all: intros; inv MS.
(* Llabel *)
+ left; eapply exec_straight_steps; eauto.
  intros. fsimpl in TR. monadInv TR. econstructor; split. apply exec_straight_one. reflexivity. unfold Asm.exec_instrPlabel. auto. auto.
  split. apply agree_nextinstr; auto. fsimpl; congruence.

(* Lgoto *)
+ intros. assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e; congruence). subst f0.
  inv AT. monadInv H2.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (Asm.State rs' m'); split.
  fsimpl in EQ0. fsimpl in EQ. monadInv EQ0.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

(* Lop *)
+ assert (eval_operation (Genv.globalenv tprog) sp op (map rs args) m = Some v).
    rewrite <- e. apply eval_operation_preserved. apply (symbols_preserved prog tprog TRANSF).
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. fsimpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split. auto.
  apply agree_set_undef_mreg with rs0; auto.
  apply Val.lessdef_trans with v'; auto.
  simpl; intros. fsimpl in H0. destruct (andb_prop _ _ H0); clear H1.
  rewrite R; auto. simple apply DXP. rewrite H2 in H0. destruct H0. rewrite andb_true_r. reflexivity. apply preg_of_not_X30; auto.
Local Transparent destroyed_by_op.
destruct op; simpl; auto; congruence.

(* Lcond true *)
+ assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e0; congruence). subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_opt_steps_goto; eauto. fsimpl; reflexivity.
  intros. fsimpl in TR.
  exploit transl_cbranch_correct_true; eauto. intros (rs' & jmp & A & B & C).
  exists jmp; exists k; exists rs'.
  split. eexact A.
  split. apply agree_exten with rs0; auto with asmgen.
  exact B.

(* Lcond false *)
+  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit transl_cbranch_correct_false; eauto. fsimpl in TR. apply TR. intros (rs' & A & B).
  exists rs'.
  split. eexact A.
  split. apply agree_exten with rs0; auto with asmgen. fsimpl.
  simpl. congruence.

(* return *)
+ inv STACKS. simpl in *.
  right. split. lia. split. auto.
  rewrite <- ATPC in H5.
  econstructor; eauto. congruence.

(* Lgetstack *)
+ unfold S.load_stack in e.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. fsimpl in TR.
  exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto with asmgen. congruence.
  fsimpl; congruence.

(* Lsetstack *)
+ unfold S.store_stack in e.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. fsimpl in TR.
  exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  fsimpl; intros. rewrite Q; auto with asmgen.

(* Lgetparam *)
+ assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e; congruence). subst f0.
  unfold S.load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact e0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact e1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros. fsimpl in TR; monadInv TR.
  destruct ep.
(* X30 contains parent *)
-  exploit loadind_correct. eexact EQ.
  instantiate (2 := rs0). rewrite DXP; eauto. congruence.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
  simpl; intros. rewrite R; auto with asmgen.
  apply preg_of_not_X30; auto. fsimpl in H. auto.
(* GPR11 does not contain parent *)
-  rewrite chunk_of_Tptr in A.
  exploit loadind_ptr_correct. eexact A. congruence. intros [rs1 [P [Q R]]].
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto. congruence.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
  Open Scope asm.
  instantiate (1 := rs1#X30 <- (rs2#X30)). intros.
  rewrite Pregmap.gso; auto with asmgen.
  congruence.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' X30). congruence. auto with asmgen.
  fsimpl; intros. rewrite U; auto with asmgen.
  apply preg_of_not_X30; auto.

(* internal function *)
+ exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (Asm.fn_code x0))); inversion EQ1. clear EQ1. subst x0.
  unfold S.store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact e1. eauto. eauto.
  intros [m2' [F G]].
  simpl chunk_of_type in F.
  exploit Mem.storev_extends. eexact G. eexact e2. eauto. eauto.
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  set (x1 := Asm.Pcfi_rel_offset (Ptrofs.to_int (S.fn_retaddr_ofs f)) :: x0) in *.
  set (tfbody := Asm.Pallocframe (S.fn_stacksize f) (S.fn_link_ofs f) ::
                 storeind_ptr RA SP (S.fn_retaddr_ofs f) x1) in *.
  set (tf := {| Asm.fn_sig := S.fn_sig f; Asm.fn_code := tfbody |}) in *.
  set (sp := Vptr stk Ptrofs.zero).
  set (rs2 := Asm.nextinstr (rs0#X30 <- (S.parent_sp s) #SP <- sp #X31 <- Vundef)).
  exploit (storeind_ptr_correct (Genv.globalenv tprog) tf SP (S.fn_retaddr_ofs f) RA x1 rs2 m2').
    rewrite chunk_of_Tptr in P. change (rs2 X1) with (rs0 X1). rewrite ATLR.
    change (rs2 X2) with sp. eexact P.
    congruence. congruence.
  intros (rs3 & U & V).
  set (rs4 := Asm.nextinstr rs3).
  assert (EXEC_PROLOGUE:
            exec_straight (Genv.globalenv tprog) tf
              (Asm.fn_code tf) rs0 m'
              x0 rs4 m3').
  { change (Asm.fn_code tf) with tfbody; unfold tfbody.
    apply exec_straight_step with rs2 m2'.
    unfold Asm.exec_instr. simpl. unfold Asm.exec_instrPallocframe. rewrite C. fold sp.
    rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. subst sp. rewrite F. reflexivity.
    reflexivity.
    eapply exec_straight_trans with (rs2 := rs3) (m2 := m3').
    eexact U. eapply exec_straight_one; eauto.
  }
  exploit exec_straight_steps_2; eauto using functions_transl. lia. constructor.
  intros (ofs' & X & Y).
  left; exists (Asm.State rs4 m3'); split.
  eapply exec_straight_steps_1; eauto. lia. constructor.
  econstructor; eauto.
  rewrite X; econstructor; eauto.
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2.
  apply agree_nextinstr. apply agree_set_other; auto with asmgen.
  apply agree_change_sp with (S.parent_sp s).
  apply agree_undef_regs with rs0. auto.
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.
  intros. unfold rs4; Simpl. unfold rs4; intros.
  unfold rs4 in * ; intros.
  rewrite nextinstr_inv; try apply V; eauto with asmgen.

(* Lreturn *)
+ assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e; congruence). subst f0.
  inversion AT; subst. simpl in H2; monadInv H2.
  assert (NOOV: list_length_z (Asm.fn_code tf) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl. fsimpl in EQ0. monadInv EQ0. eauto.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto. fsimpl in EQ0. monadInv EQ0. eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. unfold Asm.exec_instrPj_r. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.

(* heap *)

  (* Lload *)
+ assert (eval_addressing (Genv.globalenv tprog) sp addr (map rs args) = Some a).
    rewrite <- e. apply eval_addressing_preserved. apply (symbols_preserved prog tprog TRANSF).
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. fsimpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen. fsimpl.
  simpl; congruence.

  (* Lstore *)
+ assert (eval_addressing (Genv.globalenv tprog) sp addr (map rs args) = Some a).
    rewrite <- e. apply eval_addressing_preserved. apply (symbols_preserved prog tprog TRANSF).
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. fsimpl in TR. exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  fsimpl; congruence.
Qed. FEnd step_simulation.

FLemma transf_initial_states:
  forall prog tprog, match_prog prog tprog ->
  forall st1, S.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states (Genv.globalenv prog) st1 st2.
FProofLemma.
  intros. inversion H0. unfold ge in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial H); eauto.
  (*replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).*)
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. unfold Vnullptr; destruct Archi.ptr64; congruence.
  intros. rewrite Regmap.gi. auto.
  unfold Genv.symbol_address.
  rewrite (match_program_main H).
  rewrite symbols_preserved with (prog:=prog) (tprog:=tprog) by auto.
  unfold ge; rewrite H2. auto.
Qed. CloseFLemma.

FLemma transf_final_states:
  forall ge st1 st2 r,
  match_states ge st1 st2 -> S.final_state st1 r -> Asm.final_state st2 r.
FProofLemma.
  intros. inv H0. inv H. constructor. assumption.
  compute in H1. inv H1.
  generalize (preg_val _ _ _ R10 AG). rewrite H2. intros LD; inv LD. auto.
Qed. CloseFLemma.

FEnd Asmgen.

FEnd Base.

Trait Comp_Loops extends Base.

(* TODO: make Lfam base even in the base compiler *)
Family Lfam.
FEnd Lfam.

Family Mach extends Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ljumptable:
      forall ge s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      find_label lbl (fn_code f) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step ge (State s fb sp (Ljumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m).
FEnd Mach.

Family Asmgen.
Family S extends Mach. FEnd S.

FRecursion transl_instr.
From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.
Case Ljumptable arg tbl :=
(fun f ep k =>
   do r <- ireg_of arg;
   OK (Asm.Pbtbl r tbl :: k)).
FEnd transl_instr.

FRecursion it1_is_parent.
Case _ := (fun before => false).
FEnd it1_is_parent.

FRecursion transl_instr_label_sig.
Case _ := (fun c k => tail_nolabel k c).
FEnd transl_instr_label_sig.

FInduction transl_instr_label.
FProof.
all: fsimpl; intros; TailNoLabel; fsimpl; fsimpl in H.
+ monadInv H. TailNoLabel.
Qed. FEnd transl_instr_label.

FInduction transl_instr_label'.
FProof.
all: intros; exploit transl_instr_label; eauto; do 2 fsimpl; try (intros [A B]; apply B).
Qed. FEnd transl_instr_label'.

FInduction is_mach_label_correct.
FProof.
+ intros. fsimpl. fdiscriminate.
Qed. FEnd is_mach_label_correct.

(*FLemma ireg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
FProofLemma.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed. CloseFLemma.*)

FInduction step_simulation.
FProof.
all: intros; inv MS.
(* Ljumptable *)
+ assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e1; congruence). subst f0.
  inv AT. monadInv H2.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H1); intro NOOV.
  exploit find_label_goto_label. eauto. eauto.
  instantiate (2 := rs0#X5 <- Vundef #X31 <- Vundef).
  Simpl. eauto.
  eauto.
  intros [tc' [rs' [A [B C]]]]. fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  exploit ireg_val; eauto. rewrite e. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. unfold Asm.exec_instrPbtbl. rewrite <- H5. unfold S.label in e0; unfold Asm.label; rewrite e0. eexact A.
  econstructor; eauto.
  eapply agree_undef_regs; eauto.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.
Qed. FEnd step_simulation.

FEnd Asmgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Lfam.
FEnd Lfam.

Family Mach extends Lfam.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

MetaData set_res.
Fixpoint set_res (res: builtin_res mreg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => Regmap.set r v rs
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.
FEnd set_res.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin:
      forall ge s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (State s f sp (Lbuiltin ef args res :: b) rs m)
        t (State s f sp b rs' m').

FEnd Mach.

Family Asmgen.

FRecursion transl_instr.
Case Lbuiltin ef args res :=
  (fun f ep k => OK (Asm.Pbuiltin ef (List.map (map_builtin_arg preg_of) args) (map_builtin_res preg_of res) :: k)).
FEnd transl_instr.

FRecursion it1_is_parent.
Case _ := (fun before => false).
FEnd it1_is_parent.

FRecursion transl_instr_label_sig.
Case _ := (fun c k => tail_nolabel k c).
FEnd transl_instr_label_sig.

FInduction transl_instr_label.
FProof.
all: fsimpl; intros; TailNoLabel; fsimpl; fsimpl in H.
+ monadInv H. TailNoLabel.
Qed. FEnd transl_instr_label.

FInduction transl_instr_label'.
FProof.
all: intros; exploit transl_instr_label; eauto; do 2 fsimpl; try (intros [A B]; apply B).
Qed. FEnd transl_instr_label'.

FInduction is_mach_label_correct.
FProof.
+ intros. fsimpl. fdiscriminate.
Qed. FEnd is_mach_label_correct.

From Rocqet Require Import Machregs.
FLemma builtin_arg_match:
  forall ge (rs: Asm.regset) sp m a v,
  eval_builtin_arg ge (fun r => rs (preg_of r)) sp m a v ->
  eval_builtin_arg ge rs sp m (map_builtin_arg preg_of a) v.
FProofLemma.
  induction 1; simpl; eauto with barg.
Qed. CloseFLemma.

FLemma builtin_args_match:
  forall ge ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall al vl, eval_builtin_args ge ms sp m al vl ->
  exists vl', eval_builtin_args ge rs sp m' (map (map_builtin_arg preg_of) al) vl'
           /\ Val.lessdef_list vl vl'.
FProofLemma.
  induction 3; intros; simpl.
  exists (@nil val); split; constructor.
  exploit (@eval_builtin_arg_lessdef _ ge ms (fun r => rs (preg_of r))); eauto.
  intros; eapply preg_val; eauto.
  intros (v1' & A & B).
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto. apply builtin_arg_match; auto.
Qed. CloseFLemma.

FLemma set_res_other:
  forall r res v rs,
  data_preg r = false ->
  Asm.set_res (map_builtin_res preg_of res) v rs r = rs r.
FProofLemma.
  induction res; simpl; intros.
- apply Pregmap.gso. red; intros; subst r. rewrite preg_of_data in H; discriminate.
- auto.
- rewrite IHres2, IHres1; auto.
Qed. CloseFLemma.

Inherit match_stack. 

FLemma agree_set_res:
  forall res ms sp rs v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (S.set_res res v ms) sp (Asm.set_res (map_builtin_res preg_of res) v' rs).
FProofLemma.
  induction res; simpl; intros.
- eapply agree_set_mreg; eauto. rewrite Pregmap.gss. auto.
  intros. apply Pregmap.gso; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_lessdef; auto.
  apply Val.loword_lessdef; auto.
Qed. CloseFLemma.

FInduction step_simulation.
FProof.
all: intros; inv MS.
(* Lbuiltin *)
+ inv AT. monadInv H2.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H1); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply Asm.exec_step_builtin. eauto. eauto. fsimpl in EQ.  fsimpl in EQ0. monadInv EQ0.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := (Genv.globalenv prog)); eauto.  
  exact (symbols_preserved prog tprog TRANSF).
  eapply external_call_symbols_preserved; eauto. eapply senv_preserved; eauto.
  eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold Asm.nextinstr. rewrite Pregmap.gss.
  rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite ! Pregmap.gso by congruence.
  rewrite <- H. simpl. econstructor; eauto. fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  eapply code_tail_next_int; eauto.  fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  rewrite (preg_notin_charact PC (destroyed_by_builtin ef)). intros. simple apply not_eq_sym; trivial. auto with asmgen.
  reflexivity. (* auto with asmgen.*)
  apply agree_nextinstr. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros. rewrite undef_regs_other_2; auto.
  rewrite ! Pregmap.gso; auto with asmgen. rewrite it1_is_parent_Lbuiltin_eq. unfold it1_is_parentLbuiltin.
  congruence.
Qed. FEnd step_simulation.

(* ... *)
FEnd Asmgen.

FEnd Comp_Builtin.

(*
Trait Comp_Heap extends Base.

Family Lfam.
FEnd Lfam.

Family Mach extends Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

(*From Rocqet Require Import Machregs.
From Rocqet Require Import Mregisters.*)

(* From Rocqet Require Import Registers.*)
(*From Rocqet Require Import Prelude.*)
(* Open Scope asm.*)
Inherit undef_regs.
FDefinition fff := self__Mach.undef_regs.
FDefinition ddd := Machregs.destroyed_by_load.
FDefinition eee := Machregs.destroyed_by_store.
From Rocqet Require Import Mregisters.
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lload:
      forall ge s f sp chunk addr args_ dst c (rs_: Mregisters.regset) m a v rs',
      eval_addressing ge sp addr cheat (*List.map rs_ args_*) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs_)#dst <- v) ->
      step ge (State s f sp (Lload chunk addr args_ dst :: c) rs_ m)
        E0 (State s f sp c rs' m).
(*| exec_Lstore:
      forall ge s f sp chunk addr args src c rs_ m m' a rs',
      eval_addressing ge sp addr rs_##args = Some a ->
      Mem.storev chunk m a (rs_ src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs_ ->
      step ge (State s f sp (Lstore chunk addr args src :: c) rs_ m)
        E0 (State s f sp c rs' m').*)

(*| exec_Lload:
      forall ge s f sp chunk addr args dst_ c (rs_ : Mregisters.regset) m a v rs',
      eval_addressing ge sp addr cheat (*List.map rs args*) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = (Regmap.set cheat (*dst_*) v (fff (ddd chunk addr) rs_ )) ->
      step ge (State s f sp (Lload chunk addr args dst_ :: c) rs_ m)
        E0 (State s f sp c rs' m)
| exec_Lstore:
      forall ge s f sp chunk addr args src c (rs: Mregisters.regset) m m' a rs',
      eval_addressing ge sp addr cheat (*List.map rs args*) = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = fff (eee chunk addr) rs ->
      step ge (State s f sp (Lstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m').*)
FEnd Mach.

(*From Rocqet Require Import Locations.
From Rocqet Require Import Conventions1.
(* just before semantics of asm *)
From Rocqet Require Import Machregs.

From Rocqet Require Import Registers.

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

From Rocqet Require Import Mregisters.*)

Family Asmgen.
Family S extends Mach. FEnd S.

Inherit indexed_memory_access.

From Rocqet Require Import Errors.
Open Scope error_monad_scope.
FDefinition transl_memory_access
     := fun (mk_instr: ireg -> Asm.offset -> Asm.instruction)
            (addr: addressing) (args: list mreg) (k: Asm.code) =>
  match addr, args with
  | Aindexed ofs, a1 :: nil =>
      do rs <- ireg_of a1;
      OK (indexed_memory_access mk_instr rs ofs k)
  | Aglobal id ofs, nil =>
    OK (Asm.Ploadsymbol_high X31 id ofs :: mk_instr X31 (Asm.Ofslow id ofs) :: k)
  | Ainstack ofs, nil =>
      OK (indexed_memory_access mk_instr SP ofs k)
  | _, _ =>
      Error(msg "Asmgen.transl_memory_access")
  end.

FDefinition transl_load := fun
  (chunk: memory_chunk) (addr: addressing)
  (args: list mreg) (dst: mreg) (k: Asm.code) =>
  match chunk with
  | Mint8signed =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plb r)  addr args k
  | Mint8unsigned =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plbu r) addr args k
  | Mint16signed =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plh r)  addr args k
  | Mint16unsigned =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plhu r) addr args k
  | Mint32 =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Plw r)  addr args k
  | Mint64 =>
      do r <- ireg_of dst;
      transl_memory_access (Asm.Pld r)  addr args k
  | Mfloat32 =>
      do r <- freg_of dst;
      transl_memory_access (Asm.Pfls r) addr args k
  | Mfloat64 =>
      do r <- freg_of dst;
      transl_memory_access (Asm.Pfld r) addr args k
  | _ =>
      Error (msg "Asmgen.transl_load")
  end.

FDefinition transl_store := fun (chunk: memory_chunk) (addr: addressing)
           (args: list mreg) (src: mreg) (k: Asm.code) =>
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psb r)  addr args k
  | Mint16unsigned =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psh r)  addr args k
  | Mint32 =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psw r)  addr args k
  | Mint64 =>
      do r <- ireg_of src;
      transl_memory_access (Asm.Psd r)  addr args k
  | Mfloat32 =>
      do r <- freg_of src;
      transl_memory_access (Asm.Pfss r) addr args k
  | Mfloat64 =>
      do r <- freg_of src;
      transl_memory_access (Asm.Pfsd r) addr args k
  | _ =>
      Error (msg "Asmgen.transl_store")
  end.

FRecursion transl_instr.
Case Lload chunk addr args dst :=
 (fun f ep k => transl_load chunk addr args dst k).
Case Lstore chunk addr args src :=
 (fun f ep k => transl_store chunk addr args src k).
FEnd transl_instr.

FRecursion it1_is_parent.
Case _ := (fun before => false).
FEnd it1_is_parent.

Inherit nolabel.
Inherit tail_nolabel.
Inherit TailNoLabel.
Inherit indexed_memory_access_label.
FLemma transl_memory_access_label:
  forall (mk_instr: ireg -> Asm.offset -> Asm.instruction) addr args k c,
  (forall r o, nolabel (mk_instr r o)) ->
  transl_memory_access mk_instr addr args k = OK c ->
  tail_nolabel k c.
FProofLemma.
unfold transl_memory_access; intros; destruct addr; TailNoLabel. monadInv H0. apply indexed_memory_access_label; auto. apply indexed_memory_access_label; auto.
Qed. CloseFLemma.

FRecursion transl_instr_label_sig.
Case _ := (fun c k => tail_nolabel k c).
FEnd transl_instr_label_sig.

FInduction transl_instr_label.
FProof.
all: fsimpl; intros; TailNoLabel; fsimpl; fsimpl in H.
+ destruct m; monadInv H;  eapply transl_memory_access_label; eauto; intros; exact I.
+ destruct m; monadInv H;  eapply transl_memory_access_label; eauto; intros; exact I.
Qed. FEnd transl_instr_label.

FInduction transl_instr_label'.
FProof.
all: intros; exploit transl_instr_label; eauto; do 2 fsimpl; try (intros [A B]; apply B).
Qed. FEnd transl_instr_label'.

FInduction is_mach_label_correct.
FProof.
+ apply cheat. (* fdiscriminate *)
+ apply cheat. (* fdiscriminate *)
Qed. FEnd is_mach_label_correct.


(*From Rocqet Require Import Machregs.*)
(* From Rocqet Require Import Registers.*)
(*From Rocqet Require Import Prelude.*)
(*Open Scope asm.*)
From Rocqet Require Import Mregisters.
FInduction step_simulation.
FProof.
all: intros; inv MS.
(* Lload *)
+ assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen.
  simpl; congruence.

(* Lstore *)
+ assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR. exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; congruence.
Qed. FEnd step_simulation.

FEnd Asmgen.

FEnd Comp_Heap.*)

Trait Comp_Field extends Base (* ,Comp_Heap*).
FEnd Comp_Field.

Trait Comp_Call extends Base.

Family Lfam.
FEnd Lfam.

Family Mach extends Lfam.
FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FDefinition find_function_ptr
        := fun (ge: genv) (ros: mreg + ident) (rs: regset) =>
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

(* should be abstract and overrideen for Asmgen *)

MetaData return_address_offset.
(* Axiom from CompCert *)
Axiom return_address_offset: function -> code -> ptrofs -> Prop.
FEnd return_address_offset.

(* FOpaque Definition return_address_offset: function -> code -> ptrofs -> Prop := cheat.*)

(*FDefinition return_address_offset := fun (f: function) (c: code) (ofs: ptrofs) =>
  forall tf tc,
  transf_function f = OK tf ->
  transl_code f c false = OK tc ->
  code_tail (Ptrofs.unsigned ofs) (fn_code tf) tc.*)

Inherit load_stack.

MetaData extcall_arg.
Inductive extcall_arg (rs: regset) (m: mem) (sp: val): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall ofs ty v,
      load_stack m sp ty (Ptrofs.repr (0 (*Stacklayout.fe_ofs_arg*) + 4 * ofs)) = Some v ->
      extcall_arg rs m sp (S Outgoing ofs ty) v.
FEnd extcall_arg.

MetaData extcall_arg_pair.
Inductive extcall_arg_pair (rs: regset) (m: mem) (sp: val): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m sp l v ->
      extcall_arg_pair rs m sp (AST.One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m sp hi vhi ->
      extcall_arg rs m sp lo vlo ->
      extcall_arg_pair rs m sp (Twolong hi lo) (Val.longofwords vhi vlo).
FEnd extcall_arg_pair.

FDefinition extcall_arguments
    := fun (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) =>
  list_forall2 (extcall_arg_pair rs m sp) (loc_arguments sg) args.

FDefinition undef_caller_save_regs := fun (rs: regset) =>
  fun r => if is_callee_save r then rs r else Vundef.

FDefinition set_pair := fun (p: rpair mreg) (v: val) (rs: regset) =>
  match p with
  | AST.One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lcall:
      forall ge s fb sp sig ros c rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      return_address_offset f c ra ->
      step ge (State s fb sp (Lcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs m)
| exec_Ltailcall:
      forall ge s fb stk soff sig ros c rs m f f' m',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      load_stack m (Vptr stk soff) Tptr (fn_link_ofs f) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr (fn_retaddr_ofs f) = Some (parent_ra s) ->
      Mem.free m stk 0 (fn_stacksize f) = Some m' ->
      step ge (State s fb (Vptr stk soff) (Ltailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m')
| exec_function_external:
      forall ge s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (AST.External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
      step ge (Callstate s fb rs m)
         t (Returnstate s rs' m').

FEnd Mach.

Family Asmgen.
Family S extends Mach. FEnd S.
From Rocqet Require Import Errors.
Open Scope error_monad_scope.

FRecursion transl_instr.
Case Lcall sig reg_or_ident :=
  (fun f ep k =>
     match reg_or_ident with
     | (inl r) =>
         do r1 <- ireg_of r;
         OK (Asm.Pjal_r r1 sig :: k)
     | (inr symb) =>
         OK (Asm.Pjal_s symb sig :: k)
     end).
Case Ltailcall sig reg_or_ident :=
  (fun f ep k =>
     match reg_or_ident with
     | (inl r) =>
         do r1 <- ireg_of r;
         OK (make_epilogue f (Asm.Pj_r r1 sig :: k))
     | (inr symb) => OK (make_epilogue f (Asm.Pj_s symb sig :: k))
     end).
FEnd transl_instr.

FRecursion it1_is_parent.
Case _ := (fun before => false).
FEnd it1_is_parent.

FRecursion transl_instr_label_sig.
Case _ := (fun c k => tail_nolabel k c).
FEnd transl_instr_label_sig.

FInduction transl_instr_label.
FProof.
all: fsimpl; intros; TailNoLabel; fsimpl; fsimpl in H.
+ destruct s0; monadInv H; TailNoLabel.
+ destruct s0; monadInv H; (eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel]).
Qed. FEnd transl_instr_label.

FInduction transl_instr_label'.
FProof.
all: intros; exploit transl_instr_label; eauto; do 2 fsimpl; try (intros [A B]; apply B).
Qed. FEnd transl_instr_label'.

FInduction is_mach_label_correct.
FProof.
+ intros. fsimpl. fdiscriminate.
+ intros. fsimpl. fdiscriminate.
Qed. FEnd is_mach_label_correct.

(* return_address_offset is an Axiom *)
MetaData return_address_offset_correct.
Axiom return_address_offset_correct:
  forall ge b ofs fb f c tf tc ofs',
  transl_code_at_pc ge (Vptr b ofs) fb f c false tf tc ->
  S.return_address_offset f c ofs' ->
  ofs' = ofs.
FEnd return_address_offset_correct.

FLemma extcall_arg_match:
  forall ms sp rs m m' l v,
  agree ms sp rs ->
  Mem.extends m m' ->
  S.extcall_arg ms m sp l v ->
  exists v', Asm.extcall_arg rs m' l v' /\ Val.lessdef v v'.
FProofLemma.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val; eauto.
  unfold S.load_stack in H2.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ H) in A.
  exists v'; split; auto.
  econstructor. eauto. assumption.
Qed. CloseFLemma.

FLemma extcall_arg_pair_match:
  forall ms sp rs m m' p v,
  agree ms sp rs ->
  Mem.extends m m' ->
  S.extcall_arg_pair ms m sp p v ->
  exists v', Asm.extcall_arg_pair rs m' p v' /\ Val.lessdef v v'.
FProofLemma.
  intros. inv H1.
- exploit extcall_arg_match; eauto. intros (v' & A & B). exists v'; split; auto. constructor; auto.
- exploit extcall_arg_match. eauto. eauto. eexact H2. intros (v1 & A1 & B1).
  exploit extcall_arg_match. eauto. eauto. eexact H3. intros (v2 & A2 & B2).
  exists (Val.longofwords v1 v2); split. constructor; auto. apply Val.longofwords_lessdef; auto.
Qed. CloseFLemma.

FLemma extcall_args_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall ll vl,
  list_forall2 (S.extcall_arg_pair ms m sp) ll vl ->
  exists vl', list_forall2 (Asm.extcall_arg_pair rs m') ll vl' /\ Val.lessdef_list vl vl'.
FProofLemma.
  induction 3; intros.
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_pair_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed. CloseFLemma.

FLemma extcall_arguments_match:
  forall ms m m' sp rs sg args,
  agree ms sp rs -> Mem.extends m m' ->
  S.extcall_arguments ms m sp sg args ->
  exists args', Asm.extcall_arguments rs m' sg args' /\ Val.lessdef_list args args'.
FProofLemma.
  unfold S.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed. CloseFLemma.

FLemma agree_set_pair:
  forall sp p v v' ms rs,
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (S.set_pair p v ms) sp (Asm.set_pair (map_rpair preg_of p) v' rs).
FProofLemma.
  intros. destruct p; simpl.
- apply agree_set_mreg_parallel; auto.
- apply agree_set_mreg_parallel. apply agree_set_mreg_parallel; auto.
  apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed. CloseFLemma.

FLemma agree_undef_caller_save_regs:
  forall ms sp rs,
  agree ms sp rs ->
  agree (S.undef_caller_save_regs ms) sp (Asm.undef_caller_save_regs rs).
FProofLemma.
  intros. destruct H. unfold S.undef_caller_save_regs, Asm.undef_caller_save_regs; split.
- unfold proj_sumbool; rewrite dec_eq_true. auto.
- auto.
- intros. unfold proj_sumbool. rewrite dec_eq_false by (apply preg_of_not_SP).
  destruct (in_dec preg_eq (preg_of r) (List.map preg_of (List.filter is_callee_save all_mregs))); simpl.
+ apply list_in_map_inv in i. destruct i as (mr & A & B).
  assert (r = mr) by (apply preg_of_injective; auto). subst mr; clear A.
  apply List.filter_In in B. destruct B as [C D]. rewrite D. auto.
+ destruct (is_callee_save r) eqn:CS; auto.
  elim n. apply List.in_map. apply List.filter_In. auto using all_mregs_complete.
Qed. CloseFLemma.

FInduction step_simulation.
FProof.
all: intros; inv MS.
(* Lcall *)
+ assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e0; congruence). subst f0.
  inv AT.
  assert (NOOV: ((Z.le (list_length_z (Asm.fn_code tf)) Ptrofs.max_unsigned))).
    eapply transf_function_no_overflow; eauto.
    destruct ros as [rf|fid]; simpl in e; monadInv H2.
- (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert e; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H2; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H3). intro CT1.
  assert (TCA: transl_code_at_pc (Genv.globalenv prog) (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply Asm.exec_step_internal. Simpl. rewrite <- H; simpl; eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Asm.exec_instrPjal_r. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl.
  Simpl. rewrite <- H. auto.
- (* Direct call *) fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  generalize (code_tail_next_int _ _ _ _ NOOV H3). intro CT1.
  assert (TCA: transl_code_at_pc (Genv.globalenv prog) (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply Asm.exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Asm.exec_instrPjal_s. unfold Genv.symbol_address.
  rewrite (symbols_preserved prog tprog TRANSF). rewrite e. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl.
  Simpl. rewrite <- H. auto.

(* Ltailcall *)
+ assert (f0 = f) by (unfold S.fundef in FIND; unfold S.fundef in e0; congruence).  subst f0.
  inversion AT; subst.
  assert (NOOV: (list_length_z (Asm.fn_code tf) <= Ptrofs.max_unsigned)%Z).
    eapply transf_function_no_overflow; eauto.  exploit Mem.loadv_extends. eauto. eexact e1. auto. simpl. intros [parent' [A B]].
  destruct ros as [rf|fid]; simpl in e; monadInv H2.
- (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert e; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H2; intros LD; inv LD; auto.
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.
  Simpl. rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen; eauto using preg_of_not_SP). assumption.
- (* Direct call *)
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z). fsimpl in EQ. fsimpl in EQ0. monadInv EQ0.
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.
  apply agree_set_other; auto with asmgen.
  Simpl. unfold Genv.symbol_address.
  rewrite (symbols_preserved prog tprog TRANSF). rewrite e. auto.

(* external function *)
+ exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply Asm.exec_step_external; eauto.
  eapply external_call_symbols_preserved; eauto. eapply senv_preserved; eauto.
  econstructor; eauto.
  unfold Asm.loc_external_result. apply agree_set_other; auto. apply agree_set_pair; auto.
  apply agree_undef_caller_save_regs; auto.
Qed. FEnd step_simulation.

FEnd Asmgen.

FEnd Comp_Call.

Trait Comp_Switch extends Comp_Loops. FEnd Comp_Switch.

Family Comp extends
  (*Comp_Heap,*)
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Field,
  Comp_Call,  
  Comp_Builtin.

Family Asmgen.
Final Family S := Mach.
FEnd Asmgen.

FEnd Comp.
