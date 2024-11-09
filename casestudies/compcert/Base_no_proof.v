From NFPOP Require Import Loader.

From NFPOP Require Import Coqlib.
From NFPOP Require Import Errors.
From NFPOP Require Import Values.
From NFPOP Require Import AST.
From NFPOP Require Import Integers. 
From NFPOP Require Import Floats.
From NFPOP Require Import Memory.
From NFPOP Require Import Globalenvs.
From NFPOP Require Import Smallstep.
From NFPOP Require Import Events.
From NFPOP Require Import Maps.
From NFPOP Require Import Linking.
Require Import NFPOP.CompCert.lib.Ctypes.
From NFPOP Require Import Cop.
From NFPOP Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From NFPOP Require Import Prelude.

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
| Pnop : instruction. (**r nop instruction *)
                       
FDefinition code := list instruction.
MetaData function.
Record function : Type := mkfunction { fn_sig: signature; fn_code: self__Common.code }.
FEnd function.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

(*
(* Operational Semantics *)    
FDefinition regset := Pregmap.t val.
FDefinition genv := Genv.t fundef unit.

Open Scope asm.
          
MetaData undef_regs.
Fixpoint undef_regs (l: list preg) (rs: self__Common.regset) : self__Common.regset :=
match l with
| nil => rs
| r :: l' => undef_regs l' (rs#r <- Vundef)
end.
FEnd undef_regs.
          
MetaData set_regs.
Fixpoint set_regs (rl: list preg) (vl: list val) (rs: self__Common.regset) : self__Common.regset :=
match rl, vl with
| r1 :: rl', v1 :: vl' =>  set_regs rl' vl' (rs#r1 <- v1)
| _, _ => rs
end.
FEnd set_regs.

MetaData find_instr.
Fixpoint find_instr (pos: Z) (c: self__Common.code) {struct c} : option self__Common.instruction :=
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
Fixpoint label_pos (lbl: self__Common.label) (pos: Z) (c: self__Common.code) {struct c} : option Z :=
match c with
| nil => None
| instr :: c' =>
  if self__Common.is_label instr lbl then Some (pos + 1) else label_pos lbl (pos + 1) c'
end.
FEnd label_pos.
          
MetaData outcome.
Inductive outcome: Type :=
| Next:  self__Common.regset -> mem -> outcome
| Stuck: outcome.
FEnd outcome.
          
FDefinition nextinstr := fun (rs: regset) =>
  Pregmap.set PC (Val.offset_ptr (rs PC) Ptrofs.one) rs.

FDefinition goto_label := fun (f: self__Common.function) (lbl: self__Common.label) (rs: self__Common.regset) (m: mem) =>
match label_pos lbl 0 (self__Common.fn_code f) with
| None => self__Common.Stuck
| Some pos =>
    match (rs PC) with
    | Vptr b ofs => self__Common.Next (Pregmap.set PC (Vptr b (Ptrofs.repr pos)) rs) m
    | _          => self__Common.Stuck
    end
end.

MetaData low_half.
Parameter low_half: self__Common.genv -> ident -> ptrofs -> ptrofs.
FEnd low_half.

MetaData high_half.
Parameter high_half: self__Common.genv -> ident -> ptrofs -> val.
FEnd high_half.
                    
FDefinition eval_offset : self__Common.genv -> self__Common.offset -> ptrofs := fun ge ofs =>
match ofs with
| self__Common.Ofsimm n => n
| self__Common.Ofslow id delta => low_half ge id delta
end.          

FDefinition exec_load := fun (ge : genv) (chunk: memory_chunk) (rs: regset) (m: mem)
    (d: preg) (a: ireg) (ofs: offset) =>
match  Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ge ofs)) with
| None => self__Common.Stuck
| Some v => self__Common.Next (nextinstr (Pregmap.set d v rs)) m
end.          
          
FDefinition exec_store := fun (ge : genv) (chunk: memory_chunk) (rs: regset) (m: mem)
  (s: preg) (a: ireg) (ofs: offset) =>
match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ge ofs)) (rs s) with
| None => self__Common.Stuck
| Some m' => self__Common.Next (nextinstr rs) m'
end.

FDefinition eval_branch := fun (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) =>
match res with
| Some true  => goto_label f l rs m
| Some false => self__Common.Next (nextinstr rs) m
| None => self__Common.Stuck
end.
          
FRecursion exec_instr about instruction motive (fun (_ : instruction) => genv -> function -> regset -> mem -> outcome) by _rect.
Case Plabel lbl := (fun ge f rs m => self__Common.Next (nextinstr rs) m).
Case Pbtbl r tbl := 
(fun ge f rs m => 
  match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => self__Common.Stuck
          | Some lbl => goto_label f lbl (rs#X5 <- Vundef #X31 <- Vundef) m
          end
      | _ => self__Common.Stuck
      end).
Case Pj_l lbl := (fun ge f rs m => goto_label f lbl rs m).
Case Pj_r r sg := (fun ge f rs m => self__Common.Next (rs#PC <- (rs#r)) m).
Case Pj_s s sg := (fun ge f rs m =>  self__Common.Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero) #X31 <- Vundef) m).
Case Pjal_s s sg := 
(fun ge f rs m =>  
   self__Common.Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)
                    #RA <- (Val.offset_ptr rs#PC Ptrofs.one)) m).
Case Pjal_r r sg := 
(fun ge f rs m => 
    self__Common.Next (rs#PC <- (rs#r)
              #RA <- (Val.offset_ptr rs#PC Ptrofs.one)) m).
(** The following instructions and directives are not generated directly by Asmgen,
    so we do not model them. *)
Case Pnop := (fun ge f rs m => self__Common.Stuck). 
Case Pcfi_rel_offset a := (fun ge f rs m =>   self__Common.Next (nextinstr rs) m).
Case Pallocframe sz pos := 
(fun ge f rs m => 
   let (m1, stk) := Mem.alloc m 0 sz in
   let sp := (Vptr stk Ptrofs.zero) in
   match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
   | None => self__Common.Stuck
   | Some m2 => self__Common.Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m2
   end).
Case Pfreeframe sz pos := 
(fun ge f rs m => 
  match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
  | None => self__Common.Stuck
  | Some v =>
      match rs SP with
      | Vptr stk ofs =>
          match Mem.free m stk 0 sz with
          | None => self__Common.Stuck
          | Some m' => self__Common.Next (nextinstr (rs#SP <- v #X31 <- Vundef)) m'
          end
      | _ => self__Common.Stuck
      end
  end).
FEnd exec_instr.

(** Execution of the instruction at [rs PC]. *)

MetaData state.
Inductive state: Type :=
| State: self__Common.regset -> mem -> state.
FEnd state.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_step_internal:
    forall ge b ofs f i rs m rs' m',
    rs PC = Vptr b ofs ->
    Genv.find_funct_ptr ge b = Some (AST.Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (self__Common.fn_code f) = Some i ->
    exec_instr i ge f rs m = self__Common.Next rs' m' ->
    step ge (self__Common.State rs m) E0 (self__Common.State rs' m').        

MetaData initial_state.
Inductive initial_state (p: self__Common.program): self__Common.state -> Prop :=
| initial_state_intro: forall m0,
    let ge := Genv.globalenv p in
    let rs0 :=
      (Pregmap.init Vundef)
      # PC <- (Genv.symbol_address ge p.(AST.prog_main) Ptrofs.zero)
      # SP <- Vnullptr
      # RA <- Vnullptr in
    Genv.init_mem p = Some m0 ->
    initial_state p (self__Common.State rs0 m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Common.state -> int -> Prop :=
| final_state_intro: forall rs m r,
   rs PC = Vnullptr ->
   rs X10 = Vint r ->
    final_state (self__Common.State rs m) r.
FEnd final_state.*)

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

(*
FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.
          
FRecursion exec_instr.
Case Pmv d s := (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (rs#s))) m).
Case Paddiw d s i :=  (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m).
Case Psltiw  d s i := (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m).
Case Psltiuw d s i :=  (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m).
Case Pandiw d s i := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.and rs##s (Vint i)))) m).
Case Poriw d s i := (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.or rs##s (Vint i)))) m).
Case Pxoriw d s i := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i)))) m).
Case Pslliw d s i := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i)))) m).
Case Psrliw d s i := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i)))) m).
Case Psraiw d s i := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i)))) m).
Case Pluiw d i := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m).
Case Paddw d s1 s2 := (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m).
Case Psubw d s1 s2 :=  (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m).
Case Psltw d s1 s2 :=  (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m).
Case Psltuw d s1 s2 := (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m). 
Case Pseqw d s1 s2 :=  (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m).
Case Psnew d s1 s2 :=  (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m).
Case Pandw d s1 s2 :=  (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m).
Case Porw d s1 s2 :=  (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m).
Case Pxorw d s1 s2 := (fun ge f rs m =>   self__RV32I.Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m). 
Case Psllw d s1 s2 := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m). 
Case Psrlw d s1 s2 := (fun ge f rs m =>  self__RV32I.Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m). 
Case Psraw d s1 s2 := (fun ge f rs m => self__RV32I.Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m). 
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
FEnd exec_instr. *)

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
| Pmull  : ireg -> ireg0 -> ireg0 -> instruction (**r integer multiply low *)
| Pmulhl : ireg -> ireg0 -> ireg0 -> instruction (**r integer multiply high signed *)
| Pmulhul: ireg -> ireg0 -> ireg0 -> instruction (**r integer multiply high unsigned *)
| Pdivl  : ireg -> ireg0 -> ireg0 -> instruction (**r integer division *)
| Pdivul : ireg -> ireg0 -> ireg0 -> instruction (**r unsigned integer division *)
| Preml  : ireg -> ireg0 -> ireg0 -> instruction (**r integer remainder *)
| Premul : ireg -> ireg0 -> ireg0 -> instruction (**r unsigned integer remainder *)
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

(*
FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Paddil d s i := (fun ge f rs m => self__RV64I.Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m).
Case Psltil d s i := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (Vlong i))))) m).
Case Psltiul d s i := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (Vlong i))))) m).
Case Pandil d s i := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m).
Case Poril d s i := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.orl rs###s (Vlong i)))) m).
Case Pxoril d s i := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.xorl rs###s (Vlong i)))) m).
Case Psllil d s i := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.shll rs###s (Vint i)))) m).
Case Psrlil d s i := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m).
Case Psrail d s i := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.shrl rs###s (Vint i)))) m).
Case Pluil d i := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Vlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m).
Case Paddl d s1 s2 := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m).
Case Psubl d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m).
Case Pmull d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m).
Case Pmulhl d s1 s2 := (fun ge f rs m => self__RV64I.Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m).
Case Pmulhul d s1 s2 := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m).
Case Pdivl d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m).
Case Pdivul d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m).
Case Preml d s1 s2 := (fun ge f rs m => self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m).
Case Premul d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m).
Case Psltl d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m).
Case Psltul d s1 s2 := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m).
Case Pseql d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m).
Case Psnel d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m).
Case Pandl d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m).
Case Porl d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m).
Case Pxorl d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m).
Case Pslll d s1 s2 := (fun ge f rs m =>   self__RV64I.Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m).
Case Psrll d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m).
Case Psral d s1 s2 := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m).
Case Pcvtl2w d s := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#d <- (Val.loword rs##s))) m).
Case Pcvtw2l r := (fun ge f rs m =>  self__RV64I.Next (nextinstr (rs#r <- (Val.longofint rs#r))) m).
Case Pbeql s1 s2 l :=  (fun ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs###s1 rs###s2)).
Case Pbnel s1 s2 l :=  (fun ge f rs m =>   eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs###s1 rs###s2)).
Case Pbltl s1 s2 l :=  (fun ge f rs m =>  eval_branch f l rs m (Val.cmpl_bool Clt rs###s1 rs###s2)).
Case Pbltul s1 s2 l := (fun ge f rs m => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###s1 rs###s2)).
Case Pbgel s1 s2 l :=  (fun ge f rs m =>  eval_branch f l rs m (Val.cmpl_bool Cge rs###s1 rs###s2)).
Case Pbgeul s1 s2 l := (fun ge f rs m =>  eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge rs###s1 rs###s2)).
Case Pld d a ofs := (fun ge f rs m =>  exec_load ge Mint64 rs m d a ofs).
Case Psd s a ofs := (fun ge f rs m => exec_store ge Mint64 rs m s a ofs).
Case Ploadli rd i :=  (fun ge f rs m => self__RV64I.Next (nextinstr (rs#X31 <- Vundef #rd <- (Vlong i))) m).
Case Pld_a d a ofs := (fun ge f rs m => exec_load ge Many64 rs m d a ofs).
Case Psd_a s a ofs := (fun ge f rs m => exec_store ge Many64 rs m s a ofs).
FEnd exec_instr.*)

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

(*
FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pmulw d s1 s2 := (fun ge f rs m =>   self__M.Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m).
Case Pmulhw d s1 s2 := (fun ge f rs m => self__M.Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m).
Case Pmulhuw d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m).
Case Pdivw d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m).
Case Pdivuw d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m).
Case Premw d s1 s2 := (fun ge f rs m => self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m).
Case Premuw d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m).
Case Pmull d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m).
Case Pmulhl d s1 s2 := (fun ge f rs m =>   self__M.Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m).
Case Pmulhul d s1 s2 := (fun ge f rs m => self__M.Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m).
Case Pdivl d s1 s2 := (fun ge f rs m =>   self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m).
Case Pdivul d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m).
Case Preml d s1 s2 := (fun ge f rs m =>  self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m).
Case Premul d s1 s2 := (fun ge f rs m =>   self__M.Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m).
FEnd exec_instr.*)

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

(*FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pfmv d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (rs#s))) m).
Case Pfls d a ofs := (fun ge f rs m => exec_load ge Mfloat32 rs m d a ofs).
Case Pfss s a ofs := (fun ge f rs m => exec_store ge Mfloat32 rs m s a ofs).
Case Pfnegs d s := (fun ge f rs m => self__F.Next (nextinstr (rs#d <- (Val.negfs rs#s))) m).
Case Pfabss d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.absfs rs#s))) m).
Case Pfadds d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m).
Case Pfsubs d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m).
Case Pfmuls d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m).
Case Pfdivs d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m).
Case Pfeqs d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m).
Case Pflts d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m).
Case Pfles d s1 s2 := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m).
Case Pfcvtws d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m).
Case Pfcvtwus d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m).
Case Pfcvtsw d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m).
Case Pfcvtswu d s := (fun ge f rs m => self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m).
Case Pfcvtls d s := (fun ge f rs m => self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m).
Case Pfcvtlus d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m).
Case Pfcvtsl d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m).
Case Pfcvtslu d s := (fun ge f rs m =>  self__F.Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m).
Case Ploadsi rd f := (fun ge _ rs m =>  self__F.Next (nextinstr (rs#X31 <- Vundef #rd <- (Vsingle f))) m).

(*not in the execution model *)
Case Pfmins a b c := (fun ge f rs m => self__F.Stuck).
Case Pfmaxs a b c := (fun ge f rs m => self__F.Stuck).
Case Pfsqrts a b := (fun ge f rs m => self__F.Stuck).
Case Pfmadds a b c d := (fun ge f rs m => self__F.Stuck).
Case Pfmsubs a b c d := (fun ge f rs m => self__F.Stuck).
Case Pfnmadds a b c d := (fun ge f rs m => self__F.Stuck).
Case Pfnmsubs a b c d := (fun ge f rs m => self__F.Stuck).
Case Pfmvxs a b := (fun ge f rs m => self__F.Stuck).
Case Pfmvsx a b := (fun ge f rs m => self__F.Stuck).
Case Pfmvxd a b := (fun ge f rs m => self__F.Stuck).
Case Pfmvdx a b := (fun ge f rs m => self__F.Stuck).

FEnd exec_instr.*)

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

(*
FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FRecursion exec_instr.
Case Pfld d a ofs := (fun ge f rs m =>  exec_load ge Mfloat64 rs m d a ofs).
Case Pfsd s a ofs := (fun ge f rs m => exec_store ge Mfloat64 rs m s a ofs). 
Case Pfnegd d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.negf rs#s))) m).
Case Pfabsd d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.absf rs#s))) m).
Case Pfaddd d s1 s2 := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m).
Case Pfsubd d s1 s2 := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m).
Case Pfmuld d s1 s2 := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m).
Case Pfdivd d s1 s2 := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m).
Case Pfeqd d s1 s2 := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m).
Case Pfltd d s1 s2 := (fun ge f rs m =>   self__D.Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m).
Case Pfled d s1 s2 := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m).
Case Ploadfi rd f := (fun ge _ rs m => self__D.Next (nextinstr (rs#X31 <- Vundef #rd <- (Vfloat f))) m).
Case Pfcvtwd d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m).
Case Pfcvtwud d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m).
Case Pfcvtdw d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m).
Case Pfcvtdwu d s := (fun ge f rs m => self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m).
Case Pfcvtld d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m).
Case Pfcvtlud d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m).
Case Pfcvtdl d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m).
Case Pfcvtdlu d s := (fun ge f rs m =>  self__D.Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m).
Case Pfcvtds d s := (fun ge f rs m =>   self__D.Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m).
Case Pfcvtsd d s := (fun ge f rs m => self__D.Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m).
Case Pfld_a d a ofs := (fun ge f rs m => exec_load ge Many64 rs m d a ofs).
Case Pfsd_a s a ofs := (fun ge f rs m => exec_store ge Many64 rs m s a ofs).

(* not modeled *)
Case Pfmind d s1 s2 := (fun ge f rs m => self__D.Stuck ).
Case Pfmaxd d s1 s2 := (fun ge f rs m => self__D.Stuck).
Case Pfsqrtd a b := (fun ge f rs m => self__D.Stuck).
Case Pfmaddd a b c d := (fun ge f rs m => self__D.Stuck).
Case Pfmsubd  a b c d := (fun ge f rs m => self__D.Stuck).
Case Pfnmaddd a b c d  := (fun ge f rs m => self__D.Stuck).
Case Pfnmsubd a b c d  := (fun ge f rs m => self__D.Stuck).

FEnd exec_instr.*)

FEnd D.

(* Standard extension for vector operations *)
Family V.
FEnd V.

FEnd RV.

Family Z extends RV.RV64I.

FEnd Z.

Check Z.Psw_a.


Trait Base.

Family C.
FInductive expr : Type :=
| Eval : val -> type -> expr (* constant *)
| Evar : ident -> type -> expr (* variable *)        
| Ecast : expr -> type -> expr (* type cast (ty)r *)
| Eseqand : expr -> expr -> type -> expr (* sequential "and" r1 && r2 *)
| Eseqor : expr -> expr -> type -> expr (* sequential "or" r1 || r2 *)
| Econdition : expr -> expr -> expr -> type -> expr (* conditional r1 ? r2 : r3 *)
| Esizeof : type -> type -> expr (* size of a type *)
| Ealignof : type -> type -> expr (* natural alignment of a type *)        
| Ecomma : expr -> expr -> type -> expr (* sequence expression r1, r2 *)                
| Eparen : expr -> type -> type -> expr. 
        
FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect.
Case Eval v ty := ty.
Case Evar x ty := ty.          
Case Ecast r ty := ty. 
Case Eseqand r1 r2 ty := ty. 
Case Eseqor r1 r2 ty := ty. 
Case Econdition r1 r2 r3 ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.          
Case Ecomma r1 r2 ty := ty.
Case Eparen e ty' ty := ty.
FEnd typeof.

FDefinition label := ident.     
FInductive stmt : Type :=
| Sseq : stmt -> stmt -> stmt
| Sskip : stmt
| Sdo : expr -> stmt(* evaluate expression for side effects *)        
| Sifthenelse : expr -> stmt -> stmt -> stmt(* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt.

MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: self__C.stmt
}.
FEnd function.

FDefinition var_names := fun (vars: list(ident * type)) =>
  List.map (@fst ident type) vars.

FDefinition fundef := Ctypes.fundef function.

FDefinition type_of_function : function -> type := fun f => 
  Tfunction (type_of_params (self__C.fn_params f)) (self__C.fn_return f) (self__C.fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f => 
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

(*
(* Semantics *)
MetaData genv.
Record genv := { genv_genv :> Genv.t self__C.fundef type; genv_cenv :> composite_env }.
FEnd genv.

FDefinition globalenv : program -> genv := fun p =>
  {| self__C.genv_genv := Genv.globalenv p; self__C.genv_cenv := p.(prog_comp_env) |}.

FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (self__C.genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z) := fun ge e => 
    List.map (block_of_binding ge) (PTree.elements e).

MetaData assign_loc.
Inductive assign_loc (ge : self__C.genv) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                              bitfield -> val -> trace -> mem -> val -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ge ty m b ofs Full v E0 m' v
  | assign_loc_volatile: forall v chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store (self__C.genv_genv ge) chunk m b ofs v t m' ->
      assign_loc ge ty m b ofs Full v t m' v
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (alignof_blockcopy (self__C.genv_cenv ge) ty | Ptrofs.unsigned ofs') ->
      (alignof_blockcopy (self__C.genv_cenv ge) ty | Ptrofs.unsigned ofs) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof (self__C.genv_cenv ge) ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof (self__C.genv_cenv ge) ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof (self__C.genv_cenv ge) ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ge ty m b ofs Full (Vptr b' ofs') E0 m' (Vptr b' ofs')
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ge ty m b ofs (Bits sz sg pos width) v E0 m' v'.
FEnd assign_loc.

MetaData alloc_variables.
Inductive alloc_variables (ge : self__C.genv) : self__C.env -> mem ->
                           list (ident * type) ->
                           self__C.env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables ge e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof (self__C.genv_cenv ge) ty) = (m1, b1) ->
      alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables ge e m ((id, ty) :: vars) e2 m2.
FEnd alloc_variables.

MetaData bind_parameters.
Inductive bind_parameters (ge : self__C.genv) (e: self__C.env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ge e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl v1' b m1 m2,
      PTree.get id e = Some(b, ty) ->
      self__C.assign_loc ge ty m b Ptrofs.zero Full v1 E0 m1 v1' ->
      bind_parameters ge e m1 params vl m2 ->
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2.
FEnd bind_parameters.

FInductive cont: Type :=
| Kstop: cont
| Kdo: cont -> cont(* Kdo k = after x in x; *)
| Kseq: stmt -> cont -> cont(* Kseq s2 k = after s1 in s1;s2 *)
| Kifthenelse: stmt -> stmt -> cont -> cont(* Kifthenelse s1 s2 k = after x in if (x) { s1 } else { s2 } *)
| Kreturn: cont -> cont. (* Kreturn k = after e in return e; *)              

FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kdo k := k.
Case Kseq s k := (call_cont k).
Case Kifthenelse s1 s2 k := (call_cont k).
Case Kreturn k := (call_cont k).            
FEnd call_cont.

FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.          
Case Kstop := True.
Case Kdo k := False.
Case Kseq s k := False.
Case Kifthenelse s1 s2 k := False.
Case Kreturn k := False.
FEnd is_call_cont.

MetaData state.
Inductive state: Type :=
| State(* execution of a stmt *)
    (f: self__C.function) (s: self__C.stmt)
    (k: self__C.cont) (e: self__C.env) (m: mem) : state
| ExprState(* reduction of an expression *)
    (f: self__C.function) (r: self__C.expr)
    (k: self__C.cont) (e: self__C.env) (m: mem) : state
| Callstate(* calling a function *)
    (fd: self__C.fundef) (args: list val)
    (k: self__C.cont) (m: mem) : state
| Returnstate(* returning from a function *)
    (res: val) (k: self__C.cont) (m: mem) : state
| Stuckstate. (* undefined behavior occurred *)
FEnd state.
        
FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
Case Sskip := (fun lbl k => None).
Case Sseq s1 s2 :=
  (fun lbl k =>
     match find_label s1 lbl (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sdo r := (fun lbl k => None).
Case Sifthenelse a s1 s2 :=
  (fun lbl k =>
      match find_label s1 lbl k with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sreturn a := (fun lbl k => None).
Case Slabel lbl' s' := (fun lbl k => if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sgoto lbl' := (fun lbl k => None).
FEnd find_label.

(* deterministic evaluation strategy *)

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
| esr_val: forall ge e m v ty,
    eval_simple_rvalue ge e m (Eval v ty) v                       
| esr_cast: forall ge e m ty r1 v1 v,
    eval_simple_rvalue ge e m r1 v1 ->
    Cop.sem_cast v1 (typeof r1) ty m = Some v ->
    eval_simple_rvalue ge e m (Ecast r1 ty) v                       
| esr_sizeof: forall ge e m ty1 ty,
    eval_simple_rvalue ge e m (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.sizeof (self__C.genv_cenv ge) ty1)))
| esr_alignof: forall ge e m ty1 ty,
    eval_simple_rvalue ge e m (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.alignof (self__C.genv_cenv ge) ty1))).
                
FRecursion is_val about expr motive (fun (e : expr) => Prop) by _rect.
Case Eval v ty := True.
Case Evar x ty := False.
Case Ecast r ty := False.
Case Eseqand r1 r2 ty := False.
Case Eseqor r1 r2 ty := False.
Case Econdition r1 r2 r3 ty := False.
Case Esizeof ty' ty := False.
Case Ealignof ty' ty := True.
Case Ecomma r1 r2 ty := False.
Case Eparen e ty' ty := False.
FEnd is_val.
        
MetaData kind.
Inductive kind : Type := LV | RV.
FEnd kind.
        
FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_top: forall k,
    leftcontext k k (fun x => x)  
| lctx_cast: forall k F ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Ecast (F x) ty)
| lctx_seqand: forall k F r2 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Eseqand (F x) r2 ty)
| lctx_seqor: forall k F r2 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Eseqor (F x) r2 ty)
| lctx_condition: forall k F r2 r3 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Econdition (F x) r2 r3 ty)
| lctx_comma: forall k F e2 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Ecomma (F x) e2 ty)
| lctx_paren: forall k F tycast ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Eparen (F x) tycast ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_expr: forall ge f r k e m v ty,
    eval_simple_rvalue ge e m r v ->
    is_val r ->
    ty = typeof r ->
    estep ge (self__C.ExprState f r k e m)
      E0 (self__C.ExprState f (Eval v ty) k e m)      
| step_seqand_true: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some true ->
    estep ge (self__C.ExprState f (F (Eseqand r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eparen r2 type_bool ty)) k e m)      
| step_seqand_false: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some false ->
    estep ge (self__C.ExprState f (F (Eseqand r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eval (Vint Int.zero) ty)) k e m)      
| step_seqor_true: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some true ->
    estep ge (self__C.ExprState f (F (Eseqor r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eval (Vint Int.one) ty)) k e m)      
| step_seqor_false: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some false ->
    estep ge (self__C.ExprState f (F (Eseqor r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eparen r2 type_bool ty)) k e m)      
| step_condition: forall ge f F r1 r2 r3 ty k e m v b,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some b ->
    estep ge (self__C.ExprState f (F (Econdition r1 r2 r3 ty)) k e m)
      E0 (self__C.ExprState f (F (Eparen (if b then r2 else r3) ty ty)) k e m)      
| step_comma: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    ty = typeof r2 ->
    estep ge (self__C.ExprState f (F (Ecomma r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F r2) k e m)      
| step_paren: forall ge f F r tycast ty k e m v1 v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r v1 ->
    sem_cast v1 (typeof r) tycast m = Some v ->
    estep ge (self__C.ExprState f (F (Eparen r tycast ty)) k e m)
      E0 (self__C.ExprState f (F (Eval v ty)) k e m).
        
FInductive sstep: genv -> state -> trace -> state -> Prop :=
| step_do_1: forall ge f x k e m,
    sstep ge (self__C.State f (Sdo x) k e m)
      E0 (self__C.ExprState f x (Kdo k) e m)
| step_do_2: forall ge f v ty k e m,
    sstep ge (self__C.ExprState f (Eval v ty) (Kdo k) e m)
      E0 (self__C.State f Sskip k e m)      
| step_seq: forall ge f s1 s2 k e m,
    sstep ge (self__C.State f (Sseq s1 s2) k e m)
      E0 (self__C.State f s1 (Kseq s2 k) e m)      
| step_skip_seq: forall ge f s k e m,
    sstep ge (self__C.State f Sskip (Kseq s k) e m)
      E0 (self__C.State f s k e m)      
| step_ifthenelse_1: forall ge f a s1 s2 k e m,
    sstep ge (self__C.State f (Sifthenelse a s1 s2) k e m)
      E0 (self__C.ExprState f a (Kifthenelse s1 s2 k) e m)      
| step_ifthenelse_2: forall ge f v ty s1 s2 k e m b,
    Cop.bool_val v ty m = Some b ->
    sstep ge (self__C.ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m)
      E0 (self__C.State f (if b then s1 else s2) k e m)
| step_return_0: forall ge f k e m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    sstep ge (self__C.State f (Sreturn None) k e m)
      E0 (self__C.Returnstate Vundef (call_cont k) m')      
| step_return_1: forall ge f x k e m,
      sstep ge (self__C.State f (Sreturn (Some x)) k e m)
        E0 (self__C.ExprState f x (Kreturn k) e m)        
| step_return_2: forall ge f v1 ty k e m v2 m',
      Cop.sem_cast v1 ty f.(self__C.fn_return) m = Some v2 ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      sstep ge (self__C.ExprState f (Eval v1 ty) (Kreturn k) e m)
        E0 (self__C.Returnstate v2 (call_cont k) m')        
| step_skip_call: forall ge f k e m m',
   is_call_cont k ->
   Mem.free_list m (blocks_of_env ge e) = Some m' ->
   sstep ge (self__C.State f Sskip k e m)
     E0 (self__C.Returnstate Vundef k m')
| step_label: forall ge f lbl s k e m,
      sstep ge (self__C.State f (Slabel lbl s) k e m)
         E0 (self__C.State f s k e m)
| step_goto: forall ge f lbl k e m s' k',
    find_label f.(self__C.fn_body) lbl (call_cont k) = Some (s', k') ->
    sstep ge (self__C.State f (Sgoto lbl) k e m)
       E0 (self__C.State f s' k' e m)
| step_internal_function: forall ge f vargs k m e m1 m2,
   list_norepet (var_names (self__C.fn_params f) ++ var_names (self__C.fn_vars f)) ->
   alloc_variables ge empty_env m (f.(self__C.fn_params) ++ f.(self__C.fn_vars)) e m1 ->
   bind_parameters ge e m1 f.(self__C.fn_params) vargs m2 ->
   sstep ge (self__C.Callstate (Internal f) vargs k m)
      E0 (self__C.State f f.(self__C.fn_body) k e m2).

FDefinition step : genv -> state -> trace -> state -> Prop := fun ge S t S' => 
  estep ge S t S' \/ sstep ge S t S'.

MetaData initial_state.
Inductive initial_state (p: self__C.program): self__C.state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := self__C.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol (self__C.genv_genv ge) p.(prog_main) = Some b ->
      Genv.find_funct_ptr (self__C.genv_genv ge) b = Some f ->
      self__C.type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (self__C.Callstate f nil self__C.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__C.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__C.Returnstate (Vint r) self__C.Kstop m) r.
FEnd final_state.*)

FEnd C. 


Family Clight.
FInductive expr : Type :=          
| Econst_int: int -> type -> expr(* integer literal *)
| Econst_float: float -> type -> expr(* double float literal *)
| Econst_single: float32 -> type -> expr(* single float literal *)
| Econst_long: int64 -> type -> expr(* long integer literal *)                                            
| Etempvar: ident -> type -> expr (* temporary variable *)          
| Esizeof: type -> type -> expr (* size of a type *)
| Ecast: expr -> type -> expr
| Ealignof: type -> type -> expr. (* alignment of a type *)
       
FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect. 
Case Econst_int i ty := ty. 
Case Econst_float f ty := ty. 
Case Econst_single s ty := ty. 
Case Econst_long l ty := ty. 
Case Etempvar v ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.
Case Ecast e ty := ty.
FEnd typeof.
       
FDefinition label := ident.
FInductive stmt : Type :=                                        
| Sskip : stmt (* do nothing *)
| Sset : ident -> expr -> stmt (* assignment tempvar = rvalue *)
| Sseq : stmt -> stmt -> stmt (* sequence *)
| Sifthenelse : expr -> stmt -> stmt -> stmt (* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt.
              
MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: self__Clight.stmt
}.
FEnd function.
              
FDefinition fundef := Ctypes.fundef function.
       
FDefinition type_of_function : function -> type := fun f => 
  Tfunction (type_of_params (self__Clight.fn_params f)) (self__Clight.fn_return f) (self__Clight.fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f => 
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

(*
(* Semantics *)

MetaData genv.
Record genv := { genv_genv :> Genv.t self__Clight.fundef type; genv_cenv :> composite_env }.
FEnd genv.
FDefinition globalenv : program -> genv := fun p => 
  {| self__Clight.genv_genv := Genv.globalenv p; self__Clight.genv_cenv := p.(prog_comp_env) |}.


FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).
FDefinition temp_env := PTree.t val.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Econst_int: forall ge e le m i ty,
    eval_expr ge e le m (Econst_int i ty) (Vint i)
| eval_Econst_float: forall ge e le m f ty,
    eval_expr ge e le m (Econst_float f ty) (Vfloat f)
| eval_Econst_single: forall ge e le m f ty,
    eval_expr ge e le m (Econst_single f ty) (Vsingle f)
| eval_Econst_long: forall ge e le m i ty,
    eval_expr ge e le m (Econst_long i ty) (Vlong i)
| eval_Ecast: forall ge e le m a ty v1 v,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v ->
    eval_expr ge e le m (Ecast a ty) v
| eval_Etempvar: forall ge e le m id ty v,
    PTree.get id le = Some v ->
    eval_expr ge e le m (Etempvar id ty) v.

FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont. (* Kseq s2 k = after s1 in s1;s2 *)

FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.       
Case Kstop := Kstop.
Case Kseq s k := (Kseq s k).
FEnd call_cont.
            
FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.                   
Case Kstop := True.
Case Kseq s k := False.
FEnd is_call_cont.
            
FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect. 
Case Sskip := (fun lbl k => None). 
Case Sset id e := (fun lbl k => None).
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end). 
Case Sifthenelse a s1 s2 := 
 (fun lbl k => 
     match find_label s1 lbl k with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sreturn a := (fun lbl k => None).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sgoto lbl' :=  (fun lbl k => None).
FEnd find_label.

MetaData state.
Inductive state: Type :=
  | State
      (f: self__Clight.function)
      (s: self__Clight.stmt)
      (k: self__Clight.cont)
      (e: self__Clight.env)
      (le: self__Clight.temp_env)
      (m: mem) : state
  | Callstate
      (fd: self__Clight.fundef)
      (args: list val)
      (k: self__Clight.cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: self__Clight.cont)
      (m: mem) : state.
FEnd state.

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (self__Clight.genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z)  := fun ge e => 
  List.map (block_of_binding ge) (PTree.elements e).

(* To be overriden in SimplExpr & Cshmgen *)
FOpaque Definition function_entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop := cheat.

FInductive step : genv -> state -> trace -> state -> Prop :=  
| step_skip_seq: forall ge f s k e le m,
  step ge (self__Clight.State f Sskip (Kseq s k) e le m)
    E0 (self__Clight.State f s k e le m)
| step_set: forall ge f id a k e le m v,
  eval_expr ge e le m a v ->
  step ge (self__Clight.State f (Sset id a) k e le m)
    E0 (self__Clight.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
  step ge (self__Clight.State f (Sseq s1 s2) k e le m)
    E0 (self__Clight.State f s1 (Kseq s2 k) e le m)
| step_ifthenelse: forall ge f a s1 s2 k e le m v1 b,
    eval_expr ge e le m a v1 ->
    Cop.bool_val v1 (typeof a) m = Some b ->
    step ge (self__Clight.State f (Sifthenelse a s1 s2) k e le m)
      E0 (self__Clight.State f (if b then s1 else s2) k e le m)      
| step_return_0: forall ge f k e le m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f (Sreturn None) k e le m)
      E0 (self__Clight.Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f a k e le m v v' m',
    eval_expr ge e le m a v ->
    Cop.sem_cast v (typeof a) f.(self__Clight.fn_return) m = Some v' ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f (Sreturn (Some a)) k e le m)
      E0 (self__Clight.Returnstate v' (call_cont k) m')      
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f Sskip k e le m)
      E0 (self__Clight.Returnstate Vundef k m')
| step_label: forall ge f lbl s k e le m,
  step ge (self__Clight.State f (Slabel lbl s) k e le m)
    E0 (self__Clight.State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
  find_label  f.(self__Clight.fn_body) lbl (call_cont k) = Some (s', k') ->
  step ge (self__Clight.State f (Sgoto lbl) k e le m)
    E0 (self__Clight.State f s' k' e le m)    
| step_internal_function: forall ge f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      step ge (self__Clight.Callstate (Internal f) vargs k m)
        E0 (self__Clight.State f f.(self__Clight.fn_body) k e le m1).

MetaData initial_state.
Inductive initial_state (p: self__Clight.program): self__Clight.state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      self__Clight.type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (self__Clight.Callstate f nil self__Clight.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Clight.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__Clight.Returnstate (Vint r) self__Clight.Kstop m) r.
FEnd final_state.*)

FEnd Clight.

(* C -> Clight *)
Family SimplExpr.

Local Open Scope gensym_monad_scope.

MetaData makeseq_rec.
Fixpoint makeseq_rec (s: self__Base.Clight.stmt) (l: list self__Base.Clight.stmt) : self__Base.Clight.stmt :=
   match l with
   | nil => s
   | s' :: l' => makeseq_rec (self__Base.Clight.Sseq s s') l'
    end.
FEnd makeseq_rec.
      
FDefinition makeseq : list self__Base.Clight.stmt -> self__Base.Clight.stmt := fun l => 
  makeseq_rec self__Base.Clight.Sskip l.

MetaData set_destination.
Inductive set_destination : Type :=
| SDbase (tycast ty: type) (tmp: ident)
| SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).
FEnd set_destination.

MetaData destination.
Inductive destination : Type :=
| For_val
| For_effects
| For_set (sd: self__SimplExpr.set_destination).
FEnd destination.

MetaData do_set. 
Fixpoint do_set (sd: self__SimplExpr.set_destination) (a: self__Base.Clight.expr) : list self__Base.Clight.stmt :=
    match sd with
    | self__SimplExpr.SDbase tycast ty tmp => self__Base.Clight.Sset tmp (self__Base.Clight.Ecast a tycast) :: nil
    | self__SimplExpr.SDcons tycast ty tmp sd' => self__Base.Clight.Sset tmp (self__Base.Clight.Ecast a tycast) :: do_set sd' (self__Base.Clight.Etempvar tmp ty)
    end.
FEnd do_set.

FDefinition finish := fun (dst: destination) (sl: list Clight.stmt) (a: Clight.expr) => 
  match dst with
  | self__SimplExpr.For_val => (sl, a)
  | self__SimplExpr.For_effects => (sl, a)
  | self__SimplExpr.For_set sd => (sl ++ do_set sd a, a)
  end.

FDefinition sd_temp := fun (sd: set_destination) =>
  match sd with self__SimplExpr.SDbase _ _ tmp => tmp | self__SimplExpr.SDcons _ _ tmp _ => tmp end.
         
FDefinition sd_head_type := fun (sd: set_destination) => 
  match sd with self__SimplExpr.SDbase _ ty _ => ty | self__SimplExpr.SDcons _ ty _ _ => ty end.
         
FDefinition temp_for_sd : type -> set_destination -> mon ident := fun ty sd => 
  if type_eq ty (sd_head_type sd) then ret (sd_temp sd) else gensym ty.
    
FDefinition dummy_expr := Clight.Econst_int Int.zero type_int32s.
      
FRecursion eval_simpl_expr about Clight.expr motive (fun (_ : Clight.expr) => option val) by _rect.          
Case Econst_float n ty := (Some(Vfloat n)).
Case Econst_int n ty := (Some(Vint n)).
Case Econst_single n ty := (Some(Vsingle n)).
Case Econst_long n ty := (Some(Vlong n)).
Case Ecast b ty := 
  (match eval_simpl_expr b with
    | None => None
    | Some v => Cop.sem_cast v (Clight.typeof b) ty Mem.empty
    end).
Case Etempvar id ty := None.
Case Esizeof ty' ty := None.
Case Ealignof ty' ty := None.
FEnd eval_simpl_expr.

FDefinition makeif : Clight.expr -> Clight.stmt -> Clight.stmt -> Clight.stmt :=
  fun a s1 s2 =>
    match eval_simpl_expr a with
    | Some v =>
        match Cop.bool_val v (Clight.typeof a) Mem.empty with
        | Some b => if b then s1 else s2
        | None => Clight.Sifthenelse a s1 s2
        end
    | None => Clight.Sifthenelse a s1 s2
    end.
      
FRecursion transl_expr about C.expr motive (fun (_ : C.expr) => destination -> mon (list Clight.stmt * Clight.expr)) by _rect.
Case Evar id ty := (fun dst => ret (finish dst nil (Clight.Etempvar id ty))).
Case Eval v ty := 
  (fun dst => 
    match v with 
    | Vint n => ret (finish dst nil (Clight.Econst_int n ty)) 
    | Vlong n =>  ret (finish dst nil (Clight.Econst_long n ty))
    | Vfloat n => ret (finish dst nil (Clight.Econst_float n ty))
    | Vsingle n => ret (finish dst nil (Clight.Econst_single n ty))
    | _ => error (msg "SimplExpr.transl_expr: Eval") end).
Case Ecast r1 ty :=
  (fun dst => 
      match dst with
      | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
          do (sl1, a1) <- transl_expr r1 self__SimplExpr.For_val;
          ret (finish dst sl1 (Clight.Ecast a1 ty))
      | self__SimplExpr.For_effects =>
          transl_expr r1 self__SimplExpr.For_effects end).
Case Ecomma r1 r2 ty := 
   (fun dst => 
      do (sl1, a1) <- transl_expr r1 self__SimplExpr.For_effects;
      do (sl2, a2) <- transl_expr r2 dst;
      ret (sl1 ++ sl2, a2)).
Case Econdition r1 r2 r3 ty :=
  (fun dst => 
      do (sl1, a1) <- transl_expr r1 self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase ty ty t in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd);
          do (sl3, a3) <- transl_expr r3 (self__SimplExpr.For_set sd);
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               Clight.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 self__SimplExpr.For_effects;
          do (sl3, a3) <- transl_expr r3 self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons ty ty t sd in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd');
          do (sl3, a3) <- transl_expr r3 (self__SimplExpr.For_set sd');
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      end).
Case Eseqor r1 r2 ty := 
  (fun dst => 
    do (sl1, a1) <- transl_expr r1 self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd);
          ret (sl1 ++
               makeif a1 (Clight.Sset t (Clight.Econst_int Int.one ty)) (makeseq sl2) :: nil,
               Clight.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 Clight.Sskip (makeseq sl2) :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq (do_set sd (Clight.Econst_int Int.one ty))) (makeseq sl2) :: nil,
               dummy_expr)
      end).
Case Eseqand r1 r2 ty := 
  (fun dst => 
    do (sl1, a1) <- transl_expr r1 self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd);
          ret (sl1 ++
               makeif a1 (makeseq sl2) (Clight.Sset t (Clight.Econst_int Int.zero ty)) :: nil,
               Clight.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) Clight.Sskip :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (Clight.Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      end).                          
Case Esizeof ty' ty := (fun dst => ret (finish dst nil (Clight.Esizeof ty' ty))).
Case Ealignof ty' ty := (fun dst => ret (finish dst nil (Clight.Ealignof ty' ty))).
Case Eparen e tycast ty := (fun dst => error (msg "SimplExpr.transl_expr: paren")).
FEnd transl_expr.

FDefinition transl_expression : C.expr -> mon (Clight.stmt * Clight.expr) := fun r =>
  do (sl, a) <- transl_expr r self__SimplExpr.For_val; ret (makeseq sl, a).

FDefinition transl_expr_stmt : C.expr -> mon Clight.stmt := fun r =>
  do (sl, a) <- transl_expr r self__SimplExpr.For_effects; ret (makeseq sl).

FDefinition transl_if : C.expr -> Clight.stmt -> Clight.stmt -> mon Clight.stmt  := fun r s1 s2 => 
  do (sl, a) <- transl_expr r self__SimplExpr.For_val;
  ret (makeseq (sl ++ makeif a s1 s2 :: nil)).

Closing Fact is_Sskip:
  forall s, {s = C.Sskip} + {s <> C.Sskip} by {  destruct s; ((left; reflexivity) || (right; congruence)) }.

FRecursion transl_stmt about C.stmt motive (fun (_ : C.stmt) => mon Clight.stmt) by _rect.
Case Sskip := (ret Clight.Sskip).
Case Sdo e := (transl_expr_stmt e).
Case Sseq s1 s2 := 
  (do ts1 <- transl_stmt s1;
   do ts2 <- transl_stmt s2;
   ret (Clight.Sseq ts1 ts2)). 
Case Sifthenelse e s1 s2 := 
  (do ts1 <- transl_stmt s1;
   do ts2 <- transl_stmt s2;
   do (s', a) <- transl_expression e;
    if is_Sskip s1 && is_Sskip s2 then
      ret (Clight.Sseq s' Clight.Sskip)
    else
      ret (Clight.Sseq s' (Clight.Sifthenelse a ts1 ts2))).
Case Sreturn e := 
  (match e with
    | None => ret (Clight.Sreturn None)
    | Some e =>
        do (s', a) <- transl_expression e;
        ret (Clight.Sseq s' (Clight.Sreturn (Some a)))
    end).
Case Slabel lbl s1 := 
  (do ts1 <- transl_stmt s1;
    ret (Clight.Slabel lbl ts1)).
Case Sgoto lbl := (ret (Clight.Sgoto lbl)).
FEnd transl_stmt.

FDefinition transl_function : C.function -> res Clight.function := fun f => 
  match transl_stmt f.(self__Base.C.fn_body) (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody g i =>
      OK (Clight.mkfunction
              f.(self__Base.C.fn_return)
              f.(self__Base.C.fn_callconv)
              f.(self__Base.C.fn_params)
              f.(self__Base.C.fn_vars)
              g.(gen_trail)
              tbody)
  end.      

Local Open Scope error_monad_scope.

FDefinition transl_fundef : composite_env -> C.fundef -> res Clight.fundef := fun _ fd =>
    match fd with
    | Internal f =>
        do tf <- transl_function f; OK (Internal tf)
    | External ef targs tres cc =>
      OK (External ef targs tres cc)           
    end.
     
FDefinition transl_program : C.program -> res Clight.program := fun p =>     
  do p1 <- AST.transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.

(*
(* Relational specification of translation *)     
FDefinition final : self__SimplExpr.destination -> Clight.expr -> list Clight.stmt := fun dst a => 
match dst with
| self__SimplExpr.For_val => nil
| self__SimplExpr.For_effects => nil
| self__SimplExpr.For_set sd => do_set sd a
end.

FInductive tr_expr : Clight.temp_env -> destination -> C.expr -> list Clight.stmt -> Clight.expr -> list ident -> Prop :=     
| tr_val_effect: forall le v ty any tmp,
    tr_expr le self__SimplExpr.For_effects (C.Eval v ty) nil any tmp
| tr_val_value: forall le v ty a tmp,
    Clight.typeof a = ty ->
    (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      Clight.eval_expr tge e le' m a v) ->
    tr_expr le self__SimplExpr.For_val (C.Eval v ty) nil a tmp
| tr_val_set: forall le sd v ty a any tmp,
    Clight.typeof a = ty ->
    (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      Clight.eval_expr tge e le' m a v) ->
    tr_expr le (self__SimplExpr.For_set sd) (C.Eval v ty)
                (do_set sd a) any tmp
| tr_sizeof: forall le dst ty' ty tmp,
    tr_expr le dst (C.Esizeof ty' ty)
        (final dst (Clight.Esizeof ty' ty))
        (Clight.Esizeof ty' ty) tmp
| tr_alignof: forall le dst ty' ty tmp,
    tr_expr le dst (C.Ealignof ty' ty)
        (final dst (Clight.Ealignof ty' ty))
        (Clight.Ealignof ty' ty) tmp
| tr_cast_effects: forall le e1 ty sl1 a1 any tmp,
    tr_expr le self__SimplExpr.For_effects e1 sl1 a1 tmp ->
    tr_expr le self__SimplExpr.For_effects (C.Ecast e1 ty)
                sl1 any tmp
| tr_cast_val: forall le dst e1 ty sl1 a1 tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp ->
    tr_expr le dst (C.Ecast e1 ty)
                (sl1 ++ final dst (Clight.Ecast a1 ty))
                (Clight.Ecast a1 ty) tmp
| tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr le self__SimplExpr.For_val (C.Eseqand e1 e2 ty)
          (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2)
          (Clight.Sset t (Clight.Econst_int Int.zero ty)) :: nil)
          (Clight.Etempvar t ty) tmp
| tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr le self__SimplExpr.For_effects (C.Eseqand e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq sl2) Clight.Sskip :: nil)
                  any tmp
| tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr le (self__SimplExpr.For_set sd) (C.Eseqand e1 e2 ty)
                  (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2)
          (self__SimplExpr.makeseq (self__SimplExpr.do_set sd (Clight.Econst_int Int.zero ty))) :: nil)
                  any tmp
| tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr le self__SimplExpr.For_val (C.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 (Clight.Sset t (Clight.Econst_int Int.one ty))
                                    (self__SimplExpr.makeseq sl2) :: nil)
                  (Clight.Etempvar t ty) tmp
| tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr le self__SimplExpr.For_effects (C.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 Clight.Sskip (makeseq sl2) :: nil)
                  any tmp
| tr_seqor_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr le (self__SimplExpr.For_set sd) (C.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq (do_set sd (Clight.Econst_int Int.one ty)))
                  (makeseq sl2) :: nil)
                  any tmp
| tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e2 sl2 a2 tmp2 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
    tr_expr le self__SimplExpr.For_val (C.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    (Clight.Etempvar t ty) tmp
| tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
    tr_expr le self__SimplExpr.For_effects e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
    tr_expr le self__SimplExpr.For_effects (C.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (self__SimplExpr.makeseq sl2) (self__SimplExpr.makeseq sl3) :: nil)
                    any tmp
| tr_condition_set: forall le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
    tr_expr le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e2 sl2 a2 tmp2 ->
    tr_expr le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
    tr_expr le (self__SimplExpr.For_set sd) (C.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    any tmp                    
| tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
    tr_expr le self__SimplExpr.For_effects e1 sl1 a1 tmp1 ->
    tr_expr le dst e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr le dst (C.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp.

MetaData tr_top.
Inductive tr_top (ce : composite_env):
  self__Base.Clight.genv -> self__Base.Clight.env ->
  self__Base.Clight.temp_env -> mem ->  self__SimplExpr.destination ->
  self__Base.C.expr -> list self__Base.Clight.stmt ->
  self__Base.Clight.expr -> list ident -> Prop :=
| tr_top_val_val: forall ge e le m v ty a tmp,
    self__Base.Clight.typeof a = ty -> self__Base.Clight.eval_expr ge e le m a v ->
    tr_top ce ge e le m self__SimplExpr.For_val (self__Base.C.Eval v ty) nil a tmp
| tr_top_base: forall ge e le m dst r sl a tmp,
    self__SimplExpr.tr_expr le dst r sl a tmp ->
    tr_top ce ge e le m dst r sl a tmp.
FEnd tr_top.

MetaData tr_expression.
Inductive tr_expression (ce : composite_env): self__Base.C.expr -> self__Base.Clight.stmt -> self__Base.Clight.expr -> Prop :=
| tr_expression_intro: forall r sl a tmps,
    (forall ge e le m, self__SimplExpr.tr_top ce ge e le m self__SimplExpr.For_val r sl a tmps) ->
    tr_expression ce r (self__SimplExpr.makeseq sl) a.
FEnd tr_expression.
             
MetaData tr_expr_stmt.
Inductive tr_expr_stmt (ce : composite_env) : self__Base.C.expr -> self__Base.Clight.stmt -> Prop :=
| tr_expr_stmt_intro: forall r sl a tmps,
    (forall ge e le m, self__SimplExpr.tr_top ce ge e le m self__SimplExpr.For_effects r sl a tmps) ->
    tr_expr_stmt ce r (self__SimplExpr.makeseq sl).
FEnd tr_expr_stmt.

MetaData tr_if.
Inductive tr_if (ce : composite_env) : self__Base.C.expr -> self__Base.Clight.stmt -> self__Base.Clight.stmt -> self__Base.Clight.stmt  -> Prop :=
| tr_if_intro: forall r s1 s2 sl a tmps,
    (forall ge e le m, self__SimplExpr.tr_top ce ge e le m self__SimplExpr.For_val r sl a tmps) ->
    tr_if ce r s1 s2 (self__SimplExpr.makeseq (sl ++ self__SimplExpr.makeif a s1 s2 :: nil)).
FEnd tr_if.

FInductive tr_stmt: composite_env -> C.stmt -> Clight.stmt -> Prop :=
| tr_skip: forall ce, 
    tr_stmt ce C.Sskip Clight.Sskip
| tr_do: forall ce r s,
    tr_expr_stmt ce r s ->
    tr_stmt ce (C.Sdo r) s
| tr_seq: forall ce s1 s2 ts1 ts2,
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    tr_stmt ce (C.Sseq s1 s2) (Clight.Sseq ts1 ts2)
| tr_ifthenelse_empty: forall ce r s' a,
    tr_expression ce r s' a ->
    tr_stmt ce (C.Sifthenelse r C.Sskip C.Sskip) (Clight.Sseq s' Clight.Sskip)
| tr_ifthenelse: forall ce r s1 s2 s' a ts1 ts2,
    tr_expression ce r s' a ->
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    tr_stmt ce (C.Sifthenelse r s1 s2) (Clight.Sseq s' (Clight.Sifthenelse a ts1 ts2))
| tr_return_none: forall ce, 
    tr_stmt ce (C.Sreturn None) (Clight.Sreturn None)
| tr_return_some: forall ce r s' a,
    tr_expression ce r s' a ->
    tr_stmt ce (C.Sreturn (Some r)) (Clight.Sseq s' (Clight.Sreturn (Some a)))
| tr_label: forall ce lbl s ts,
    tr_stmt ce s ts ->
    tr_stmt ce (C.Slabel lbl s) (Clight.Slabel lbl ts)
| tr_goto: forall ce lbl,
    tr_stmt ce (C.Sgoto lbl) (Clight.Sgoto lbl).
             
(* Translation meets spec *)
(*
    Lemma transl_meets_spec:
     (forall r dst g sl a g' I,
      transl_expr ce dst r g = Res (sl, a) g' I ->
      dest_below dst g ->
      exists tmps, (forall le, tr_expr le dst r sl a (add_dest dst tmps)) /\ contained tmps g g')
    /\
     (forall rl g sl al g' I,
      transl_exprlist ce rl g = Res (sl, al) g' I ->
      exists tmps, (forall le, tr_exprlist le rl sl al tmps) /\ contained tmps g g').
  Proof.
  
  Lemma transl_expr_meets_spec:
     forall r dst g sl a g' I,
     transl_expr ce dst r g = Res (sl, a) g' I ->
     dest_below dst g ->
     exists tmps, forall ge e le m, tr_top ge e le m dst r sl a tmps.
  Proof.
  
  Lemma transl_expression_meets_spec:
    forall r g s a g' I,
    transl_expression ce r g = Res (s, a) g' I ->
    tr_expression r s a.
  Proof.
  
  Lemma transl_expr_stmt_meets_spec:
    forall r g s g' I,
    transl_expr_stmt ce r g = Res s g' I ->
    tr_expr_stmt r s.
  Proof.
  
  Lemma transl_if_meets_spec:
forall r s1 s2 g s g' I,
   transl_if ce r s1 s2 g = Res s g' I ->
   tr_if r s1 s2 s.
 Proof.
 
 Lemma transl_stmt_meets_spec:
   forall s g ts g' I, transl_stmt ce s g = Res ts g' I -> tr_stmt s ts
 with transl_lblstmt_meets_spec:
   forall s g ts g' I, transl_lblstmt ce s g = Res ts g' I -> tr_lblstmts s ts.
 Proof.
*)
             
MetaData tr_function.
Inductive tr_function (ce : composite_env) :  self__Base.C.function -> self__Base.Clight.function -> Prop :=
| tr_function_intro: forall f tf,
    self__SimplExpr.tr_stmt ce f.(self__Base.C.fn_body) tf.(self__Base.Clight.fn_body) ->
    self__Base.Clight.fn_return tf = self__Base.C.fn_return f ->
    self__Base.Clight.fn_callconv tf = self__Base.C.fn_callconv f ->
    self__Base.Clight.fn_params tf = self__Base.C.fn_params f ->
    self__Base.Clight.fn_vars tf = self__Base.C.fn_vars f ->
    tr_function ce f tf.
FEnd tr_function.

(* Lemma transl_function_spec:
    forall f tf,
    transl_function ce f = OK tf ->
    tr_function f tf. *)
                
MetaData tr_fundef.
Inductive tr_fundef (p: self__Base.C.program): self__Base.C.fundef -> self__Base.Clight.fundef -> Prop :=
    | tr_internal: forall f tf,
        self__SimplExpr.tr_function p.(prog_comp_env) f tf ->
        tr_fundef p (Internal f) (Internal tf).                    
FEnd tr_fundef.
                
(* Lemma transl_fundef_spec:
   forall p fd tfd,
   transl_fundef p.(prog_comp_env) fd = OK tfd ->
   tr_fundef p fd tfd.*)
          
(* correctness of the pass *)
FDefinition match_prog := fun (p: C.program) (tp: Clight.program) =>
    match_program_gen tr_fundef eq p p tp
 /\ prog_types tp = prog_types p.

(* Variable prog: C.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := C.globalenv prog.
Let tge := Clight.globalenv tprog. *)
              
FInductive match_cont : composite_env -> C.cont -> Clight.cont -> Prop :=
| match_Kstop: forall ce, 
    match_cont ce C.Kstop Clight.Kstop
| match_Kseq: forall ce s k ts tk,
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont ce (C.Kseq s k) (Clight.Kseq ts tk)              
with match_cont_exp : composite_env -> destination -> Clight.expr -> C.cont -> Clight.cont -> Prop :=
| match_Kdo: forall ce k a tk,
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_effects a (C.Kdo k) tk
| match_Kifthenelse_empty: forall ce a k tk,
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_val a (C.Kifthenelse C.Sskip C.Sskip k) (Clight.Kseq Clight.Sskip tk)
| match_Kifthenelse_1: forall ce a s1 s2 k ts1 ts2 tk,
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_val a (C.Kifthenelse s1 s2 k) (Clight.Kseq (Clight.Sifthenelse a ts1 ts2) tk)
| match_Kreturn: forall ce k a tk,
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_val a (C.Kreturn k) (Clight.Kseq (Clight.Sreturn (Some a)) tk).

MetaData Kseqlist.
Fixpoint Kseqlist (sl: list self__Base.Clight.stmt) (k: self__Base.Clight.cont) :=
match sl with
| nil => k
| s :: l => self__Base.Clight.Kseq s (Kseqlist l k)
end.
FEnd Kseqlist.
      
MetaData match_states.
Inductive match_states: self__Base.C.state -> self__Base.Clight.state -> Prop :=
    | match_exprstates: forall tge f r k e m tf sl tk le dest a tmps (cu: self__Base.C.program)
        (* (LINK: linkorder cu prog)*)
        (TRF: self__SimplExpr.tr_function cu.(prog_comp_env) f tf)
        (TR: self__SimplExpr.tr_top cu.(prog_comp_env) tge e le m dest r sl a tmps)
        (MK: self__SimplExpr.match_cont_exp cu.(prog_comp_env) dest a k tk),
        match_states (self__Base.C.ExprState f r k e m)
                      (self__Base.Clight.State tf self__Base.Clight.Sskip (self__SimplExpr.Kseqlist sl tk) e le m)
    | match_regularstates: forall f s k e m tf ts tk le (cu: self__Base.C.program)
        (* (LINK: linkorder cu prog) *)
        (TRF: self__SimplExpr.tr_function cu.(prog_comp_env) f tf)
        (TR: self__SimplExpr.tr_stmt cu.(prog_comp_env) s ts)
        (MK: self__SimplExpr.match_cont cu.(prog_comp_env) k tk),
        match_states (self__Base.C.State f s k e m)
                      (self__Base.Clight.State tf ts tk e le m)
    | match_callstates: forall fd args k m tfd tk cu
        (* (LINK: linkorder cu prog)*)
        (TR: self__SimplExpr.tr_fundef cu fd tfd)
        (MK: forall ce, self__SimplExpr.match_cont ce k tk),
        match_states (self__Base.C.Callstate fd args k m)
                      (self__Base.Clight.Callstate tfd args tk m)
    | match_returnstates: forall res k m tk
        (MK: forall ce, self__SimplExpr.match_cont ce k tk),
        match_states (self__Base.C.Returnstate res k m)
                      (self__Base.Clight.Returnstate res tk m)
    | match_stuckstate: forall S,
        match_states self__Base.C.Stuckstate S.
FEnd match_states.
              
FRecursion esize about C.expr motive (fun (_ : C.expr) => nat) by _rect.
Case Evar := (fun _ _ => 1%nat).
Case Eval := (fun _ _ => 0%nat).                                                      
Case Ecast r1 ty := (S(esize r1)).
Case Eseqand r1 r2 ty := (S(esize r1)).
Case Eseqor r1 r2 ty := (S(esize r1)).
Case Econdition r1 r2 r3 ty := (S(esize r1)).
Case Esizeof ty' ty := 1%nat.
Case Ealignof ty' ty:= 1%nat.                    
Case Ecomma r1 r2 ty := (S(esize r1 + esize r2)%nat).
Case Eparen r1 tycast ty := (S(esize r1)).
FEnd esize.

FRecursion measure_stmt about C.stmt motive (fun (_ : C.stmt) => nat) by _rect.
Case Sskip := 0%nat.
Case Sdo r := ((esize r + 2)%nat).
Case Sifthenelse r s1 s2 := ((esize r + 2)%nat).                       
Case Slabel lbl s := 0%nat.
Case Sgoto lbl := 0%nat. 
Case Sseq s1 s2 := 0%nat.
Case Sreturn e := 0%nat.                   
FEnd measure_stmt.

FDefinition measure : C.state -> nat := fun st => 
  match st with
  | self__Base.C.ExprState _ r _ _ _ => (esize r + 1)%nat
  | self__Base.C.State _ s _ _ _ => measure_stmt s  
  | _ => 0%nat
  end.
              
(*FRecursion measure about C.state motive (fun (_ : C.state) => nat) by _rect.
Case ExprState f r k e m := ((esize r + 1)%nat).
Case State f s k e m := (measure_stmt s).
Case Callstate f vs k m := 0%nat. 
Case Returnstate v k m := 0%nat.
Case Stuckstate := 0%nat.
FEnd measure.*)
              
FInduction estep_simulation about C.estep 
   motive (fun ge S1 t S2 (_ : C.estep ge S1 t S2) => 
           forall prog tprog tge, match_prog prog tprog -> 
           C.globalenv prog = ge -> Clight.globalenv tprog = tge ->
           forall T1 (MS : match_states S1 T1),
           exists T2,
           (plus Clight.step tge T1 t T2 \/ (star Clight.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
           /\ match_states S2 T2).
FProof.
(* expr *)
+ intros. apply cheat.                 
(* seqand true *)                  
+ intros. apply cheat.
(* seqand false *)                 
+ intros. apply cheat.
(* seqor true *)
+ intros. apply cheat.
(* seqor false *)
+ apply cheat.
(* condition *)
+ apply cheat.
(* comma *)
+ apply cheat.
(* paren *)
+ apply cheat.
Qed. FEnd estep_simulation.
              
FInduction sstep_simulation about C.sstep 
   motive (fun ge S1 t S2 (_ : C.sstep ge S1 t S2) => 
           forall prog tprog tge, match_prog prog tprog -> C.globalenv prog = ge -> Clight.globalenv tprog = tge ->
           forall T1 (MS : match_states S1 T1),
           exists T2,
           (plus Clight.step tge T1 t T2 \/
              (star Clight.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
                    /\ match_states S2 T2).
FProof.
(* do 1 *)
+ apply cheat.
(* do 2 *)
+ intros. apply cheat.
(* seq *)
+ intros. apply cheat.
(* skip seq *)
+ intros. apply cheat.
(* ifthenelse empty *)
+ apply cheat.
(* ifthenelse non empty *)
+ apply cheat.
(* return none *)
+ apply cheat.
(* return some 1 *)
+ apply cheat.
(* return some 2 *)
+ intros. apply cheat.
(* skip return *)
+ apply cheat.
(* label *)
+ apply cheat.
(* goto *)
+ apply cheat.
(* internal function *)
+ apply cheat.
Qed. FEnd sstep_simulation.
              
FLemma simulation :
     (forall ge S1 t S2 (_ : C.step ge S1 t S2),
     forall prog tprog tge, match_prog prog tprog -> C.globalenv prog = ge -> Clight.globalenv tprog = tge ->
     forall T1 (MS : match_states S1 T1),
        exists T2,
         (plus Clight.step tge T1 t T2 \/
           (star Clight.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
     /\ match_states S2 T2).
FProofLemma.
intros ge S1 t S2 STEP. destruct STEP.
- apply self__SimplExpr.estep_simulation; auto.
- apply self__SimplExpr.sstep_simulation; auto.
Qed. CloseFLemma.
              
FLemma transl_initial_states:
   forall S prog tprog (_ : match_prog prog tprog),                 
   C.initial_state prog S ->
   exists T, Clight.initial_state tprog T /\ match_states S T.
FProofLemma.
apply cheat.
Qed. CloseFLemma.
              
FLemma transl_final_states:
   forall S T r,
   match_states S T -> C.final_state S r -> Clight.final_state T r.
FProofLemma.
apply cheat.                  
Qed. CloseFLemma.*)
          
FEnd SimplExpr.

(* C family languages: Csharpminor, Cminor, CminorSel *)
Family Cfam.

FInductive expr : Type :=
| Evar : ident -> expr. (* reading a temporary variable *)            

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sset : ident -> expr -> stmt            
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt.
       
FOpaque Definition function : Type := cheat.
FOpaque Definition function_body : function -> stmt := cheat.
FOpaque Definition function_locals : function -> list ident := cheat.
FOpaque Definition function_params : function -> list ident := cheat.       
FOpaque Definition function_sig : function -> signature := cheat.
       
FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

(*
FDefinition genv := Genv.t fundef unit.
       
(* Function env/stack space *)
FOpaque Definition fenv : Type := cheat.
FOpaque Definition empty_fenv : fenv := cheat.
       
FDefinition env := PTree.t val.            
FDefinition empty_env : env := PTree.empty val.
       
MetaData set_params.
Fixpoint set_params (vl: list val) (il: list ident) {struct il} : self__Cfam.env :=
 match il, vl with
 | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
 | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
 | _, _ => PTree.empty val
 end.
FEnd set_params.

MetaData set_locals.
Fixpoint set_locals (il: list ident) (e: self__Cfam.env) {struct il} : self__Cfam.env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.
FEnd set_locals.
       
FDefinition init_env : function -> list val -> env := fun f vargs => 
  set_locals (function_locals f) (set_params vargs (function_params f)).            

(* Semantics for allocation of variables and binding of parameters at function entry. *)
FOpaque Definition free_fenv : mem -> fenv -> function -> option mem := cheat.            
FOpaque Definition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := cheat.
       
MetaData create_undef_temps.
Fixpoint create_undef_temps (temps: list ident) : self__Cfam.env :=
 match temps with
 | nil => PTree.empty val
 | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
end.
FEnd create_undef_temps.

MetaData bind_parameters.
Fixpoint bind_parameters (formals: list ident) (args: list val)
             (le: self__Cfam.env) : option self__Cfam.env :=
 match formals, args with
 | nil, nil => Some le
 | id :: xl, v :: vl => bind_parameters xl vl (PTree.set id v le)
 | _, _ => None
 end.
FEnd bind_parameters.
            
FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.
                   
MetaData state.
Inductive state: Type :=
  | State:(* Execution within a function *)
      forall (f: self__Cfam.function)(* currently executing function *)
             (s: self__Cfam.stmt)(* statement under consideration *)
             (k: self__Cfam.cont)(* its continuation -- what to do next *)
             (sp: self__Cfam.fenv) (* current "function" environment: i.e stackspace, ... *)
             (e: self__Cfam.env)(* current local environment *)
             (m: mem),(* current memory state *)
      state
  | Callstate:(* Invocation of a function *)
      forall (f: self__Cfam.fundef)(* function to invoke *)
             (args: list val)(* arguments provided by caller *)
             (k: self__Cfam.cont)(* what to do next *)
             (m: mem),(* memory state *)
      state
  | Returnstate:(* Return from a function *)
      forall (v: val)(* Return value *)
             (k: self__Cfam.cont)(* what to do next *)
             (m: mem),(* memory state *)
      state.
FEnd state.
            
FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq := (fun s c call_cont_c => call_cont_c).             
FEnd call_cont.
               
FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
Case Kstop := True.                   
Case Kseq := (fun s c call_cont_c => False).
FEnd is_call_cont.              

FDefinition letenv := list val.
               
FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Evar: forall ge lenv e le m id v,
    PTree.get id le = Some v ->
    eval_expr ge e le m lenv (Evar id) v.
                           
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
    step ge (self__Cfam.State f Sskip (Kseq s k) e le m)
      E0 (self__Cfam.State f s k e le m)              
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->                       
    free_fenv m e f = Some m' ->
    step ge (self__Cfam.State f Sskip k e le m)
      E0 (self__Cfam.Returnstate Vundef k m')
| step_set: forall lenv ge f id a k e le m v,
    eval_expr ge e le m lenv a v ->
    step ge (self__Cfam.State f (Sset id a) k e le m)
      E0 (self__Cfam.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
    step ge (self__Cfam.State f (Sseq s1 s2) k e le m)
      E0 (self__Cfam.State f s1 (Kseq s2 k) e le m)              
| step_return_0: forall ge f k e le m m',                       
    free_fenv m e f = Some m' ->
    step ge (self__Cfam.State f (Sreturn None) k e le m)
      E0 (self__Cfam.Returnstate Vundef (call_cont k) m')            
| step_return_1: forall lenv ge f a k e le m v m',
    eval_expr ge e le m lenv a v ->
    free_fenv m e f = Some m' ->
    step ge (self__Cfam.State f (Sreturn (Some a)) k e le m)
      E0 (self__Cfam.Returnstate v (call_cont k) m')
| step_internal_function: forall ge f vargs k m m1 e le,                                               
    alloc_fenv empty_fenv m f e m1 ->
    init_env f vargs = le ->                        
     step ge (self__Cfam.Callstate (AST.Internal f) vargs k m)
       E0 (self__Cfam.State f (function_body f) k e le m1).
            
MetaData initial_state.
Inductive initial_state (p: self__Cfam.program): self__Cfam.state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__Cfam.funsig f = signature_main ->               
    initial_state p (self__Cfam.Callstate f nil self__Cfam.Kstop m0).
FEnd initial_state.
            
MetaData final_state.
Inductive final_state: self__Cfam.state -> int -> Prop :=
| final_state_intro: forall r m,
   final_state (self__Cfam.Returnstate (Vint r) self__Cfam.Kstop m) r.
FEnd final_state.*)

FEnd Cfam.

Family Csharpminor extends Cfam.

FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant.

FInductive expr : Type := Econst : constant -> expr. (* constants *)
       
FInductive stmt : Type := Sifthenelse: expr -> stmt -> stmt -> stmt.
       
(* function *)
MetaData fn.
Record fn : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list (ident * Z);
  fn_temps: list ident;
  fn_body: self__Csharpminor.stmt
}.
FEnd fn.       
FOverride Definition function := fn.
FOverride Definition function_body := self__Csharpminor.fn_body.
FOverride Definition function_locals := self__Csharpminor.fn_temps.
FOverride Definition function_params := self__Csharpminor.fn_params.
FOverride Definition function_sig := self__Csharpminor.fn_sig.

(*
(* function stack environment *)       
FOverride Definition fenv := PTree.t (block * Z).
FOverride Definition empty_fenv := PTree.empty (block * Z).

FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
 match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
  List.map block_of_binding (PTree.elements e).

FOverride Definition free_fenv := fun m e f => Mem.free_list m (blocks_of_env e).
   
MetaData alloc_variables.
Inductive alloc_variables: self__Csharpminor.fenv -> mem ->
               list (ident * Z) ->
               self__Csharpminor.fenv -> mem -> Prop :=
| alloc_variables_nil:
  forall e m,
    alloc_variables e m nil e m
| alloc_variables_cons:
  forall e m id sz vars m1 b1 m2 e2,
    Mem.alloc m 0 sz = (m1, b1) ->
    alloc_variables (PTree.set id (b1, sz) e) m1 vars e2 m2 ->
    alloc_variables e m ((id, sz) :: vars) e2 m2.
FEnd alloc_variables.
         
FOverride Definition alloc_fenv := fun e m f e' m' => 
  list_norepet (map fst f.(self__Csharpminor.fn_vars)) /\
  list_norepet f.(self__Csharpminor.fn_params) /\
  list_disjoint f.(self__Csharpminor.fn_params) f.(self__Csharpminor.fn_temps) /\
  alloc_variables self__Csharpminor.empty_fenv m (self__Csharpminor.fn_vars f) e m'.

FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
Case Ointconst := (fun n => Some (Vint n)). 
Case Ofloatconst := (fun n => Some (Vfloat n)).
Case Osingleconst := (fun n => Some (Vsingle n)).
Case Olongconst := (fun n => Some (Vlong n)).
FEnd eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Econst: forall ge lenv e le m cst v,
    eval_constant cst = Some v ->
    eval_expr ge e le m lenv (Econst cst) v.
                           
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Csharpminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Csharpminor.State f (if b then s1 else s2) k sp e m).

*)

FEnd Csharpminor.

(* Clight -> Csharpminor *)
Family Cshmgen.
FDefinition make_intconst := fun (n: int) => Csharpminor.Econst (Csharpminor.Ointconst n).
FDefinition make_longconst := fun (f: int64) => Csharpminor.Econst (Csharpminor.Olongconst f).
FDefinition make_floatconst := fun (f: float) => Csharpminor.Econst (Csharpminor.Ofloatconst f).
FDefinition make_singleconst := fun (f: float32) => Csharpminor.Econst (Csharpminor.Osingleconst f).
FDefinition make_ptrofsconst := fun (n: Z) =>
  if Archi.ptr64 then make_longconst (Int64.repr n) else make_intconst (Int.repr n).            

FDefinition sizeof : composite_env -> type -> res Z := fun ce t => 
  if complete_type ce t
  then OK (Ctypes.sizeof ce t)
  else Error (msg "incomplete type").

FDefinition alignof : composite_env -> type -> res Z := fun ce t => 
  if complete_type ce t
  then OK (Ctypes.alignof ce t)
  else Error (msg "incomplete type").

(* TODO: they rely on binary/unary ops *)
(* To be overriden in a compiler that supports operations *)
FOpaque Definition make_cast : type -> type -> Csharpminor.expr -> res Csharpminor.expr :=
  fun _ _ e => OK e.
FOpaque Definition make_boolean : Csharpminor.expr -> type -> Csharpminor.expr :=
  fun e _ => e.

FRecursion transl_expr about Clight.expr motive (fun (_ : Clight.expr) => composite_env -> res Csharpminor.expr) by _rect.
Case Econst_int n ty := (fun ce => OK(make_intconst n)). 
Case Econst_float n ty := (fun ce => OK(make_floatconst n)).
Case Econst_single n ty := (fun ce => OK(make_singleconst n)).
Case Econst_long n ty := (fun ce => OK(make_longconst n)).
Case Etempvar id ty := (fun ce => OK(Csharpminor.Evar id)). 
Case Esizeof ty' ty := (fun ce => do sz <- sizeof ce ty'; OK(make_ptrofsconst sz)).
Case Ealignof ty' ty := (fun ce => do al <- alignof ce ty'; OK(make_ptrofsconst al)).
Case Ecast b ty := (fun ce => do tb <- transl_expr b ce; make_cast (Clight.typeof b) ty tb).
FEnd transl_expr.

(* (nbrk : nat) -> if Clight.stmt terminates on break return Csharpminor.exit nbrk
   (ncnt : nat) -> if Clight.smt terminates on continue return Csharpminor.exit ncnt
*)      
      
FRecursion transl_stmt about Clight.stmt motive (fun (_ : Clight.stmt) => composite_env -> type -> nat -> nat -> res Csharpminor.stmt) by _rect.
Case Sskip := (fun ce tyret nbrk ncnt => OK Csharpminor.Sskip).   
Case Sset x b :=
(fun ce tyret nbrk ncnt => 
  do tb <- transl_expr b ce;
  OK (Csharpminor.Sset x tb)).
Case Sseq s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (Csharpminor.Sseq ts1 ts2)).
Case Sifthenelse e s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do te <- transl_expr e ce;
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (Csharpminor.Sifthenelse (make_boolean te (Clight.typeof e)) ts1 ts2)).
Case Sreturn e :=
(fun ce tyret nbrk ncnt =>
   match e with
   | None => OK (Csharpminor.Sreturn None)
   | Some e => 
       do te <- transl_expr e ce;
       do te' <- make_cast (Clight.typeof e) tyret te;
       OK (Csharpminor.Sreturn (Some te'))
   end).
Case Slabel lbl s :=
(fun ce tyret nbrk ncnt => 
  do ts <- transl_stmt s ce tyret nbrk ncnt;
  OK (Csharpminor.Slabel lbl ts)).
Case Sgoto lbl := (fun ce tyret nbrk ncnt => OK (Csharpminor.Sgoto lbl)).
FEnd transl_stmt.

(* Translation of functions *)
FDefinition transl_var := fun (ce: composite_env) (v: ident * type) =>
  do sz <- sizeof ce (snd v); OK (fst v, sz).
      
FDefinition signature_of_function := fun (f: Clight.function) =>
  {| sig_args := map typ_of_type (map snd (Clight.fn_params f));
    sig_res  := rettype_of_type (Clight.fn_return f);
    sig_cc   := Clight.fn_callconv f |}.
      
FDefinition transl_function : composite_env -> Clight.function -> res Csharpminor.function :=
  fun (ce: composite_env) (f: Clight.function)  =>
  do tbody <- transl_stmt (Clight.fn_body f) ce f.(self__Base.Clight.fn_return) 1%nat 0%nat;
  do tvars <- mmap (transl_var ce) (self__Base.Clight.fn_vars f);
  OK (Csharpminor.mkfunction
        (signature_of_function f)
        (map fst (Clight.fn_params f))
        tvars
        (map fst (Clight.fn_temps f))
        tbody).      

FDefinition transl_fundef : composite_env -> ident -> Clight.fundef -> res Csharpminor.fundef :=
  fun (ce: composite_env) (id: ident) (f: Clight.fundef) =>
  match f with
  | Internal g =>
      do tg <- transl_function ce g; OK(AST.Internal tg)
  | External ef args res cconv =>
      if signature_eq (ef_sig ef) (signature_of_type args res cconv)
      then OK(AST.External ef)
      else Error(msg "Cshmgen.transl_fundef: wrong external signature")
  end.

FDefinition transl_globvar := fun (id: ident) (ty: type) => OK tt.

FDefinition transl_program : Clight.program -> res Csharpminor.program := fun p => 
  transform_partial_program2 (transl_fundef p.(prog_comp_env)) transl_globvar p.


(*
(* correctness of translation *)

MetaData match_fundef.
Inductive match_fundef (p: self__Base.Clight.program) : self__Base.Clight.fundef -> self__Base.Csharpminor.fundef -> Prop :=
  | match_fundef_internal: forall f tf,
      self__Cshmgen.transl_function p.(prog_comp_env) f = OK tf ->
      match_fundef p (Ctypes.Internal f) (AST.Internal tf)
  | match_fundef_external: forall ef args res cc,
      ef_sig ef = signature_of_type args res cc ->
      match_fundef p (Ctypes.External ef args res cc) (AST.External ef).
FEnd match_fundef.

FDefinition match_varinfo : type -> unit -> Prop := fun v tv => True.

FDefinition match_prog : Clight.program -> Csharpminor.program -> Prop := fun p tp =>
  match_program_gen match_fundef match_varinfo p p tp.

FInductive match_transl
  : self__Base.Csharpminor.stmt -> self__Base.Csharpminor.cont ->
    self__Base.Csharpminor.stmt -> self__Base.Csharpminor.cont -> Prop :=
| match_transl_0: forall ts tk,
    match_transl ts tk ts tk.

(* | match_transl_1: forall ts tk,
    match_transl (self__Base.Csharpminor.Sblock ts) tk ts
      (self__Base.Csharpminor.Kblock tk).*)

FInductive match_cont : composite_env -> type -> nat -> nat -> Clight.cont -> Csharpminor.cont -> Prop :=
| match_Kstop: forall ce tyret nbrk ncnt,
    match_cont ce tyret nbrk ncnt Clight.Kstop Csharpminor.Kstop      
| match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
    transl_stmt s ce tyret nbrk ncnt = OK ts ->
    match_cont ce tyret nbrk ncnt k tk ->
    match_cont ce tyret nbrk ncnt (Clight.Kseq s k) (Csharpminor.Kseq ts tk).
               
(*| match_Kloop1: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
    transl_stmt s1 tyret 1%nat 0%nat = OK ts1 ->
    transl_stmt s2 tyret 0%nat (S ncnt) = OK ts2 ->
    match_cont tyret nbrk ncnt k tk ->
    match_cont tyret 1%nat 0%nat
               (Clight.Sem.Kloop1 s1 s2 k)
               (Csharpminor.Sem.Kblock
                  (Csharpminor.Sem.Kseq ts2
                     (Csharpminor.Sem.Kseq
                        (Csharpminor.Sloop
                           (Csharpminor.Sseq
                              (Csharpminor.Sblock ts1) ts2))
                        (Csharpminor.Sem.Kblock tk))))
| match_Kloop2: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
    transl_stmt s1 tyret 1%nat 0%nat = OK ts1 ->
    transl_stmt s2 tyret 0%nat (S ncnt) = OK ts2 ->
    match_cont tyret nbrk ncnt k tk ->
    match_cont tyret 0%nat (S ncnt)
               (Clight.Sem.Kloop2 s1 s2 k)
               (Csharpminor.Sem.Kseq
                  (Csharpminor.Sloop
                     (Csharpminor.Sseq
                        (Csharpminor.Sblock ts1) ts2))
                  (Csharpminor.Sem.Kblock tk)).*)

(*
Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := globalenv prog.
Let tge := Genv.globalenv tprog.
*)

MetaData match_env.
Record match_env
  (prog: self__Base.Clight.program)
  (e: self__Base.Clight.env) (te: self__Base.Csharpminor.fenv) : Prop :=
 mk_match_env {
   me_local:
     forall id b ty,
       e!id = Some (b, ty) ->
       let ge := self__Base.Clight.globalenv prog in 
       te!id = Some(b, sizeof (self__Base.Clight.genv_cenv ge) ty);
   me_local_inv:
     forall id b sz,
     te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
}.
FEnd match_env.

MetaData match_states.
Inductive match_states : self__Base.Clight.state -> self__Base.Csharpminor.state -> Prop :=
| match_state:
    forall f nbrk ncnt s k e le m tf ts tk te ts' tk' (cu : self__Base.Clight.program)
        (* (LINK: linkorder cu prog)*)
        (TRF: self__Cshmgen.transl_function cu.(prog_comp_env) f = OK tf)
        (TR: self__Cshmgen.transl_stmt s cu.(prog_comp_env) (self__Base.Clight.fn_return f) nbrk ncnt = OK ts)
        (MTR: self__Cshmgen.match_transl ts tk ts' tk')
        (MENV: self__Cshmgen.match_env cu e te)
        (MK: self__Cshmgen.match_cont cu.(prog_comp_env) (self__Base.Clight.fn_return f) nbrk ncnt k tk),
    match_states (self__Base.Clight.State f s k e le m)
      (self__Base.Csharpminor.State tf ts' tk' te le m)      
| match_callstate:
    forall fd args k m tfd tk targs tres cconv cu ce
        (* (LINK: linkorder cu prog)*)
        (TR: self__Cshmgen.match_fundef cu fd tfd)
        (MK: self__Cshmgen.match_cont ce tres 0%nat 0%nat k tk)
        (ISCC: self__Base.Clight.is_call_cont k)
        (TY: self__Base.Clight.type_of_fundef fd = Tfunction targs tres cconv),
    match_states (self__Base.Clight.Callstate fd args k m)
      (self__Base.Csharpminor.Callstate tfd args tk m)      
| match_returnstate:
    forall res tres k m tk ce
        (MK: self__Cshmgen.match_cont ce tres 0%nat 0%nat k tk),
        (* (WT: wt_val res tres),*) (* Need Ctyping.v? *)
    match_states (self__Base.Clight.Returnstate res k m)
      (self__Base.Csharpminor.Returnstate res tk m).
FEnd match_states.
                 
FInduction transl_step about Clight.step
  motive (fun ge S1 t S2 (_ : Clight.step ge S1 t S2) => 
            forall prog tprog tge, match_prog prog tprog ->
            Clight.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall T1, match_states S1 T1 -> 
  exists T2, plus Csharpminor.step tge T1 t T2 /\ match_states S2 T2).            
FProof.              
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.  
Qed. FEnd transl_step.
                
FLemma transl_initial_states:
  forall S prog tprog, Clight.initial_state prog S -> transl_program prog = OK tprog ->
  exists R, Csharpminor.initial_state tprog R /\ match_states S R.
FProofLemma. apply cheat. Qed. CloseFLemma.          
          
FLemma transl_final_states:
  forall S R r,
  match_states S R -> Clight.final_state S r -> Csharpminor.final_state R r.
FProofLemma. apply cheat. Qed. CloseFLemma.*)

FEnd Cshmgen.



Family Cminor extends Cfam.

FInductive expr : Type := Econst : Csharpminor.constant -> expr.        
FInductive stmt : Type := Sifthenelse: expr -> stmt -> stmt -> stmt.  
        
MetaData fn.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: self__Cminor.stmt
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_body := self__Cminor.fn_body.
FOverride Definition function_locals := self__Cminor.fn_vars.
FOverride Definition function_params := self__Cminor.fn_params.
FOverride Definition function_sig := self__Cminor.fn_sig.

(*
(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FOverride Definition fenv := block.
   
FOverride Definition free_fenv := fun m sp f => Mem.free m sp 0 f.(self__Cminor.fn_stackspace).
          
FOverride Definition alloc_fenv := fun sp m f sp' m' => Mem.alloc m 0 f.(self__Cminor.fn_stackspace) = (m', sp).

FDefinition eval_constant := Csharpminor.eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Econst: forall ge lenv e le m cst v,
    eval_constant cst = Some v ->
    eval_expr ge e le m lenv (Econst cst) v.
                           
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Cminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Cminor.State f (if b then s1 else s2) k sp e m).*)

FEnd Cminor.

(* RISC-V *)
Family Asm extends RV.RV64I, RV.D.
(* Operations *)
FInductive condition : Type :=
| Ccomp : comparison -> condition       (**r signed integer comparison *)
| Ccompimm : comparison -> int -> condition. (**r signed integer comparison with a constant *)

FInductive operation : Type :=
| Omove : operation                    (**r [rd = r1] *)
| Ointconst : int -> operation       (**r [rd] is set to the given integer constant *)
| Olongconst : int64 -> operation    (**r [rd] is set to the given integer constant *)
| Ofloatconst : float -> operation   (**r [rd] is set to the given float constant *)
| Osingleconst : float32 -> operation (**r [rd] is set to the given float constant *)
| Oaddrstack : ptrofs -> operation (**r [rd] is set to the stack pointer plus the given offset *)
| Ocmp : condition -> operation.  (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

FRecursion negate_condition about condition motive (fun (_ : condition) => condition) by _rect.
Case Ccomp c := (Ccomp(negate_comparison c)).
Case Ccompimm c n := (Ccompimm (negate_comparison c) n).
FEnd negate_condition.

FRecursion eval_condition about condition motive (fun (_ : condition) => list val -> mem -> option bool) by _rect.
Case Ccomp c := 
(fun vl m =>
   match vl with 
   | v1 :: v2 :: nil => Val.cmp_bool c v1 v2
   | _ => None end).
Case Ccompimm c n := 
(fun vl m =>
   match vl with 
   | v1 :: nil => Val.cmp_bool c v1 (Vint n)
   | _ => None end).
FEnd eval_condition.

FRecursion shift_stack_operation about operation motive (fun (_ : operation) => Z -> operation) by _rect.
Case Omove := (fun delta => Omove).
Case Ointconst i := (fun delta => Ointconst i). 
Case Olongconst i := (fun delta => Olongconst i).
Case Ofloatconst i := (fun delta => Ofloatconst i).
Case Osingleconst i := (fun delta => Osingleconst i).
Case Oaddrstack ofs := (fun delta => Oaddrstack (Ptrofs.add ofs (Ptrofs.repr delta))).
Case Ocmp c := (fun delta => Ocmp c).
FEnd shift_stack_operation.             

FRecursion eval_operation about operation motive (fun (_ : operation) => forall F V, Genv.t F V -> val -> list val -> mem -> option val) by _rect.
Case Omove := 
(fun F V ge sp vl m => 
  match vl with 
  | v1 :: nil => Some v1 
  | _ => None end).
Case Ointconst n := 
(fun F V ge sp vl m =>  
    match vl with 
    | nil => Some (Vint n)
    | _ => None end).
Case Olongconst n := 
(fun F V ge sp vl m =>  
  match vl with 
  | nil => Some (Vlong n)
  | _ => None end).
Case Ofloatconst n := 
(fun F V ge sp vl m =>  
  match vl with 
  | nil => Some (Vfloat n)
  | _ => None end).
Case Osingleconst n := 
(fun F V ge sp vl m =>  
  match vl with 
  | nil => Some (Vsingle n)
  | _ => None end).                
Case Oaddrstack ofs := 
(fun F V ge sp vl m =>
  match vl with 
  | nil => Some (Val.offset_ptr sp ofs)
  | _ => None end).
Case Ocmp c := 
(fun F V ge sp vl m =>
    match vl with 
    | v1 :: v2 :: nil => Some (Val.of_optbool (eval_condition c vl m))
    | _ => None end).
FEnd eval_operation.
     
FEnd Asm.

Family CminorSel extends Cfam.
FInductive expr : Type :=
| Econdition : condexpr -> expr -> expr -> expr
| Eop : Asm.operation -> exprlist -> expr
| Elet : expr -> expr -> expr
| Eletvar : nat -> expr
with exprlist : Type :=
| Enil: exprlist
| Econs: expr -> exprlist -> exprlist
with condexpr : Type :=
| CEcond : Asm.condition -> exprlist -> condexpr
| CEcondition : condexpr -> condexpr -> condexpr -> condexpr
| CElet: expr -> condexpr -> condexpr.
       
FInductive stmt : Type := Sifthenelse: condexpr -> stmt -> stmt -> stmt.

MetaData fn.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: self__CminorSel.stmt
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_body := self__CminorSel.fn_body.
FOverride Definition function_locals := self__CminorSel.fn_vars.
FOverride Definition function_params := self__CminorSel.fn_params.
FOverride Definition function_sig := self__CminorSel.fn_sig.

(*
(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FOverride Definition fenv := block.   
FOverride Definition free_fenv := fun m sp f => Mem.free m sp 0 f.(self__CminorSel.fn_stackspace).          
FOverride Definition alloc_fenv := fun sp m f sp' m' => Mem.alloc m 0 f.(self__CminorSel.fn_stackspace) = (m', sp).          
FDefinition eval_operation := fun op => Asm.eval_operation op fundef unit.
             
FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eop: forall ge sp e m le op al vl v,
    eval_exprlist ge sp e m le al vl ->
    eval_operation op ge (Vptr sp Ptrofs.zero) vl m = Some v ->
    eval_expr ge sp e m le (Eop op al) v
| eval_Econdition: forall ge sp e m le a b c va v,
    eval_condexpr ge sp e m le a va ->
    eval_expr ge sp e m le (if va then b else c) v ->
    eval_expr ge sp e m le (Econdition a b c) v
| eval_Elet: forall ge sp e m le a b v1 v2,
    eval_expr ge sp e m le a v1 ->
    eval_expr ge sp e m (v1 :: le) b v2 ->
    eval_expr ge sp e m le (Elet a b) v2
| eval_Eletvar: forall ge sp e m le n v,
    nth_error le n = Some v ->
    eval_expr ge sp e m le (Eletvar n) v
with eval_exprlist: genv -> fenv -> env -> mem -> letenv -> self__CminorSel.exprlist -> list val -> Prop :=
| eval_Enil: forall ge sp e m le,
    eval_exprlist ge sp e m le Enil nil
| eval_Econs: forall ge sp e m le a1 al v1 vl,
    eval_expr ge sp e m le a1 v1 -> eval_exprlist ge sp e m le al vl ->
    eval_exprlist ge sp e m le (Econs a1 al) (v1 :: vl)
with eval_condexpr: genv -> fenv -> env -> mem -> letenv -> self__CminorSel.condexpr -> bool -> Prop :=
| eval_CEcond: forall ge sp e m le cond al vl vb,
    eval_exprlist ge sp e m le al vl ->
    Asm.eval_condition cond vl m = Some vb ->
    eval_condexpr ge sp e m le (CEcond cond al) vb
| eval_CEcondition: forall ge sp e m le a b c va v,
    eval_condexpr ge sp e m le a va ->
    eval_condexpr ge sp e m le (if va then b else c) v ->
    eval_condexpr ge sp e m le (CEcondition a b c) v
| eval_CElet: forall ge sp e m le a b v1 v2,
    eval_expr ge sp e m le a v1 ->
    eval_condexpr ge sp e m (v1 :: le) b v2 ->
    eval_condexpr ge sp e m le (CElet a b) v2.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall ge f c s1 s2 k sp e m b,
   eval_condexpr ge sp e m nil c b ->
   step ge (self__CminorSel.State f (Sifthenelse c s1 s2) k sp e m)
     E0 (self__CminorSel.State f (if b then s1 else s2) k sp e m).
*)
FEnd CminorSel.


(* A translation between C family languages *)
Family Cfamtransl.
      Family Source extends Cfam.
      FEnd Source.

      Family Target extends Cfam.
      FEnd Target.
   
      FRecursion transl_expr about Source.expr motive (fun (_ : Source.expr) => res Target.expr) by _rect.
         Case Evar := (fun id => OK (Target.Evar id)).
         Case Econst := cheat.
      FEnd transl_expr.

      FRecursion transl_stmt about Source.stmt motive (fun (_ : Source.stmt) => res Target.stmt) by _rect.
          Case Sskip := (OK (Target.Sskip)).
          Case Sset := (fun id e =>
                       do te <- transl_expr e;
                       OK (Target.Sset id te)).
          Case Sseq := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 =>                        
                          do ts1 <- transl_stmt_s1; 
                          do ts2 <- transl_stmt_s2; 
                          OK (Target.Sseq ts1 ts2)).
          Case Sifthenelse := (fun e s1 transl_stmt_s1 s2 transl_stmt_s2 =>                               
                                   do te <- transl_expr e;
                                   do ts1 <- transl_stmt_s1;
                                   do ts2 <- transl_stmt_s2;
                                   OK (Target.Sifthenelse te ts1 ts2)).          
          Case Sreturn := (fun expr =>
                             match expr with
                             | None => OK (Target.Sreturn None)
                             | Some expr =>
                                  do te <- transl_expr expr;
                                  OK (Target.Sreturn (Some te))
                             end).
      FEnd transl_stmt.
      
      FOpaque Definition transl_function : Source.function -> res Target.function :=
        cheat.
      FOpaque Definition transl_fundef : Source.fundef -> res Target.fundef := 
        cheat.
FEnd Cfamtransl.

   (* Csharpminor -> Cminor *)
Family Cminorgen.
      FDefinition compilenv := PTree.t Z.

      FRecursion translate_constant about
         Csharpminor.constant motive (fun (_ : Csharpminor.constant) => Cminor.constant) by _rect.
           Case Ointconst := (fun n => Cminor.Ointconst n).
           Case Ofloatconst := (fun n => Cminor.Ofloatconst n).
           Case Osingleconst := (fun n => Cminor.Osingleconst n).
           Case Olongconst := (fun n => Cminor.Olongconst n).
      FEnd translate_constant.
   
      FRecursion transl_expr about Csharpminor.expr motive (fun (_ : Csharpminor.expr) => compilenv -> res Cminor.expr) by _rect.
           Case Evar := (fun id => fun cenv => OK (Cminor.Evar id)).
           Case Econst := (fun cst => fun cenv => OK (Cminor.Econst (translate_constant cst))).
      FEnd transl_expr.

      FDefinition exit_env := list bool.

      MetaData shift_exit.
      Fixpoint shift_exit (e: self__Cminorgen.exit_env) (n: nat) {struct e} : nat :=
        match e, n with
        | nil, _ => n
        | false :: e', _ => S (shift_exit e' n)
        | true :: e', O => O
        | true :: e', S m => S (shift_exit e' m)
        end.
      FEnd shift_exit.
    
      FRecursion transl_stmt about Csharpminor.stmt motive (fun (_ : Csharpminor.stmt) => compilenv -> exit_env -> res Cminor.stmt) by _rect.
            Case Sskip := (fun cenv xenv => OK (Cminor.Sskip)).
            Case Sset := (fun id e => fun cenv xenv =>
                         do te <- transl_expr e cenv;
                         OK (Cminor.Sassign id te)).
            Case Sseq := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 =>
                          fun cenv xenv =>
                            do ts1 <- transl_stmt_s1 cenv xenv;
                            do ts2 <- transl_stmt_s2 cenv xenv;
                            OK (Cminor.Sseq ts1 ts2)).
            Case Sifthenelse := (fun e s1 transl_stmt_s1 s2 transl_stmt_s2 =>
                                 fun cenv xenv =>
                                     do te <- transl_expr e cenv;
                                     do ts1 <- transl_stmt_s1 cenv xenv;
                                     do ts2 <- transl_stmt_s2 cenv xenv;
                                     OK (Cminor.Sifthenelse te ts1 ts2)).
            Case Sloop := (fun s1 transl_stmt_s1 =>
                           fun cenv xenv =>
                              do ts <- transl_stmt_s1 cenv xenv;
                              OK (Cminor.Sloop ts)).
            Case Sblock := (fun s transl_stmt_s =>
                            fun cenv xenv =>
                               do ts <- transl_stmt_s cenv (true :: xenv);
                               OK (Cminor.Sblock ts)).
            Case Sexit := (fun n => fun cenv xenv =>  OK (Cminor.Sexit (shift_exit xenv n))).
            Case Sreturn := (fun expr => fun cenv xenv =>
                               match expr with
                               | None => OK (Cminor.Sreturn None)
                               | Some expr =>
                                    do te <- transl_expr expr cenv;
                                    OK (Cminor.Sreturn (Some te))
                               end).
            Case Slabel := (fun lbl s transl_stmt_s =>
                            fun cenv xenv =>
                              do ts <- transl_stmt_s cenv xenv;
                              OK (Cminor.Slabel lbl ts)).
            Case Sgoto := (fun lbl => fun cenv xenv => OK (Cminor.Sgoto lbl)).
      FEnd transl_stmt.

      (* Stack layout *)
      FDefinition block_alignment : Z -> Z := fun sz =>
          if zlt sz 2 then 1
          else if zlt sz 4 then 2
          else if zlt sz 8 then 4 else 8.

      FDefinition assign_variable : compilenv * Z -> ident * Z -> compilenv * Z := 
          fun cenv_stacksize id_sz => 
          let (id, sz) := id_sz in
          let (cenv, stacksize) := cenv_stacksize in
          let ofs := align stacksize (block_alignment sz) in
          (PTree.set id ofs cenv, ofs + Z.max 0 sz).

      FDefinition assign_variables : compilenv * Z -> list (ident * Z) -> compilenv * Z :=
          fun cenv_stacksize vars => List.fold_left assign_variable vars cenv_stacksize.

      FDefinition build_compilenv : Csharpminor.function -> compilenv * Z :=
          fun f => assign_variables (PTree.empty Z, 0) (VarSort.sort (Csharpminor.fn_vars f)).

      (* Translate Function, Fundef, Program *)
      FDefinition transl_funbody := 
      fun (cenv: compilenv) (stacksize: Z) (f: Csharpminor.function) =>
        do tbody <- transl_stmt f.(self__Imp.Csharpminor.fn_body) cenv nil ;
        OK (Cminor.mkfunction
              (Csharpminor.fn_sig f)
              (Csharpminor.fn_params f)
              (Csharpminor.fn_temps f)
              stacksize
              tbody).

      FDefinition transl_function := fun (f: Csharpminor.function) => 
        let (cenv, stacksize) := build_compilenv f in
        if zle stacksize Ptrofs.max_unsigned
        then transl_funbody cenv stacksize f
        else Error(msg "Cminorgen: too many local variables, stack size exceeded").

      FDefinition transl_fundef : Csharpminor.fundef -> res Cminor.fundef := fun f => 
        transf_partial_fundef transl_function f.

      FDefinition transl_program : Csharpminor.program -> res Cminor.program := fun p => 
        transform_partial_program transl_fundef p.
FEnd Cminorgen.     

   (* Cminor -> CminorSel *)
Family Selection.
       FDefinition longconst : int64 -> expr := fun n =>
          if Archi.splitlong then SplitLong.longconst n else CminorSel.Eop (Asm.Olongconst n) CminorSel.Enil.

       FRecurcion sel_constant about Cminor.constant motive (fun (_ : Cminor.constant) => CminorSel.expr).
           Case Ointconst := (fun n => CminorSel.Eop (Asm.Ointconst n) CminorSel.Enil).
           Case Ofloatconst := (fun n => CminorSel.Eop (Asm.Ofloatconst f) CminorSel.Enil).
           Case Osingleconst := (fun n =>  CminorSel.Eop (Asm.Osingleconst f) CminorSel.Enil).
           Case Olongconst := (fun n => longconst n).
       FEnd sel_constant.

       FRecursion sel_expr about Cminor.expr motive (fun (_ : Cminor.expr) => CminorSel.expr).          
           Case Evar := (fun id => CminorSel.Evar id).
           Case Econst := (fun cst => sel_constant cst).           
       FEnd sel_expr.
       
       FRecursion select_condition about Asm.operation motive (fun (_ : Asm.operation) => CminorSel.exprlist -> condition) by _rect.
           Case Ocmp := (fun c args => CminorSel.CEcond c args).
       FEnd select_condition.
       
       FRecursion condexpr_of_expr about CminorSel.expr motive (fun (_ : Cminor.expr) => CminorSel.condexpr) by _rect.
           Case Eop op args := select_condition op args.
           Case Econdition a b c := (CminorSel.CEcondition a (condexpr_of_expr b) (condexpr_of_expr c))
           Case Elet a b := (CElet a (condexpr_of_expr b)).
           Case Eletvar n := (CminorSel.CEcond (Asm.Ccompuimm Cne Int.zero) (CminorSel.Econs e Cminor.Enil)).
           Case Evar i := (CminorSel.CEcond (Asm.Ccompuimm Cne Int.zero) (CminorSel.Econs e Cminor.Enil)).
       FEnd condexpr_of_expr.

       Function condexpr_of_expr (e: expr) : condexpr :=
           match e with
           | Eop (Ocmp c) el => CEcond c el
           | Econdition a b c => CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)
           | Elet a b => CElet a (condexpr_of_expr b)
           | _ => CEcond (Ccompuimm Cne Int.zero) (e ::: Enil)
           end.
       
       FRecursion sel_stmt about Cminor.stmt 
                            motive (fun (_ : Cminor.stmt) => res CminorSel.stmt) by _rect.
          Case Sskip := (OK CminorSel.Sskip).
          Case Sassign id e := (OK (CminorSel.Sassign id (sel_expr e))).
          Case Sseq s1 s2 := (
                 do s1' <- sel_stmt s1 ; 
                 do s2' <- sel_stmt s2 ;
                 OK (CminorSel.Sseq s1' s2')).
          Case Sifthenelse e ifso ifnot := (
               (* For simplicity, don't use the
                  "if conversion heuristics" present in CompCert *)                      
                 do ifso' <- sel_stmt ifso ;
                 do ifnot' <- sel_stmt ifnot ;
                 OK (Sifthenelse (condexpr_of_expr (sel_expr e)) ifso' ifnot')).
          Case Sloop body := (do body' <- sel_stmt body; OK (CminorSel.Sloop body')).
          Case Sblock s := (do body' <- sel_stmt body; OK (CminorSel.Sblock body')). 
          Case Sexit := (OK (CminorSel.Sexit n)).
          Case Sreturn e := (match e with 
                             | None => OK (CminorSel.Sreturn None) 
                             | Some e => OK (CminorSel.Sreturn (Some (sel_expr e)))).
          Case Slabel lbl body := (do body' <- sel_stmt body; OK (CminorSel.Slabel lbl body')) 
          Case Sgoto := (OK (CminorSel.Sgoto lbl)).
        FEnd sel_stmt.

       FDefinition sel_function : Cminor.function -> res function := fun f =>             
             do body' <- sel_stmt f.(self__Imp.Cminor.fn_body);
             OK (self__Imp.CminorSel.mkfunction
                   f.(self__Imp.Cminor.fn_sig)
                   f.(self__Imp.Cminor.fn_params)
                   f.(self__Imp.Cminor.fn_vars)
                   f.(self__Imp.Cminor.fn_stackspace)
                   body').

       FDefinition sel_fundef : Cminor.fundef -> res fundef := fun f =>
         transf_partial_fundef (sel_function) f.

       FDefinition sel_program : Cminor.program -> res program := fun p =>         
        transform_partial_program (sel_fundef) p.

FEnd Selection.


Family RTL.
FDefinition node := positive.

From NFPOP Require Import Registers.
      
FInductive instruction: Type :=
| Inop: node -> instruction
| Iop: Asm.operation -> list reg -> reg -> node -> instruction          
| Icond: Asm.condition -> list reg -> node -> node -> instruction
| Ireturn: option reg -> instruction.

FDefinition code: Type := PTree.t instruction.

MetaData function.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: self__RTL.code;
  fn_entrypoint: self__RTL.node
}.
FEnd function.

FDefinition fundef := AST.fundef function.

FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => self__RTL.fn_sig f
  | AST.External ef => ef_sig ef
  end.

(*
(* operational semantics *)             
FDefinition genv := Genv.t fundef unit.
FDefinition regset := Regmap.t val.

FDefinition eval_operation := fun op => Asm.eval_operation op fundef unit.

MetaData init_regs.
Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : self__RTL.regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.
FEnd init_regs.

MetaData stackframe.
Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)(* where to store the result *)
             (f: self__RTL.function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (pc: self__RTL.node)(* program point in calling function *)
             (rs: self__RTL.regset),(* register state in calling function *)
      stackframe.
FEnd stackframe.

MetaData state.
Inductive state : Type :=
  | State:
      forall (stack: list self__RTL.stackframe)(* call stack *)
             (f: self__RTL.function)(* current function *)
             (sp: val)(* stack pointer *)
             (pc: self__RTL.node)(* current program point in c *)
             (rs: self__RTL.regset)(* register state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list self__RTL.stackframe)(* call stack *)
             (f: self__RTL.fundef)(* function to call *)
             (args: list val)(* arguments to the call *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list self__RTL.stackframe)(* call stack *)
             (v: val)(* return value for the call *)
             (m: mem),(* memory state *)
      state.           
FEnd state.          
           
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Inop:
    forall ge s f sp pc rs m pc',
    (self__RTL.fn_code f)!pc = Some(Inop pc') ->
    step ge (self__RTL.State s f sp pc rs m)
      E0 (self__RTL.State s f sp pc' rs m)
| exec_Iop:
    forall ge s f sp pc rs m op args res pc' v,
    (self__RTL.fn_code f)!pc = Some(Iop op args res pc') ->
    eval_operation op ge sp rs##args m = Some v ->
    step ge (self__RTL.State s f sp pc rs m)
      E0 (self__RTL.State s f sp pc' (rs#res <- v) m)
| exec_Icond:
    forall ge s f sp pc rs m cond args ifso ifnot b pc',
    (self__RTL.fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
    Asm.eval_condition cond rs##args m = Some b ->
    pc' = (if b then ifso else ifnot) ->
    step ge (self__RTL.State s f sp pc rs m)
      E0 (self__RTL.State s f sp pc' rs m)
| exec_Ireturn:
    forall ge s f stk pc rs m or m',
    (self__RTL.fn_code f)!pc = Some(Ireturn or) ->
    Mem.free m stk 0 f.(self__RTL.fn_stacksize) = Some m' ->
    step ge (self__RTL.State s f (Vptr stk Ptrofs.zero) pc rs m)
      E0 (self__RTL.Returnstate s (regmap_optget or Vundef rs) m')
| exec_return:
    forall ge res f sp pc rs s vres m,
    step ge (self__RTL.Returnstate (self__RTL.Stackframe res f sp pc rs :: s) vres m)
      E0 (self__RTL.State s f sp pc (rs#res <- vres) m).

MetaData initial_state.
Inductive initial_state (p: self__RTL.program): self__RTL.state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__RTL.funsig f = signature_main ->
    initial_state p (self__RTL.Callstate nil f nil m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__RTL.state -> int -> Prop :=
   | final_state_intro: forall r m,
      final_state (self__RTL.Returnstate nil (Vint r) m) r.
FEnd final_state.      *)

FEnd RTL.

From NFPOP Require Import RTLmonad.

(* CminorSel -> RTL *)
Family RTLgen.
FDefinition res := fun (A : Type) => res A RTL.instruction.
FDefinition mon := fun (A : Type) => mon A RTL.instruction.
FDefinition state := state RTL.instruction.

FLemma init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty RTL.instruction)!pc = None.
FProofLemma. intros; right; apply PTree.gempty. Qed. CloseFLemma.

FDefinition init_state : state :=
  mkstate RTL.instruction 1%positive 1%positive (PTree.empty RTL.instruction) init_state_wf.

FLemma add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode RTL.instruction) in
  Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code RTL.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_instr_incr:
  forall s i,
  let n := s.(st_nextnode RTL.instruction) in
  state_incr RTL.instruction s (mkstate RTL.instruction s.(st_nextreg RTL.instruction)
                (Pos.succ n)
                (PTree.set n i s.(st_code RTL.instruction))
                (add_instr_wf s i)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition add_instr : RTL.instruction -> mon RTL.node := fun (i: RTL.instruction) =>
  fun s =>
    let n := s.(st_nextnode RTL.instruction) in
    OK n
       (mkstate RTL.instruction s.(st_nextreg RTL.instruction) (Pos.succ n) (PTree.set n i s.(st_code RTL.instruction))
                (add_instr_wf s i))
       (add_instr_incr s i).

FLemma reserve_instr_wf:
  forall s pc,
    Plt pc (Pos.succ s.(st_nextnode RTL.instruction)) \/ s.(st_code RTL.instruction)!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode RTL.instruction) in
  state_incr RTL.instruction s (mkstate RTL.instruction s.(st_nextreg RTL.instruction)
                (Pos.succ n)
                s.(st_code RTL.instruction)
                    (reserve_instr_wf s)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition reserve_instr : mon RTL.node :=
  fun (s: state) =>
  let n := s.(st_nextnode RTL.instruction) in
  OK n
     (mkstate RTL.instruction s.(st_nextreg RTL.instruction) (Pos.succ n) s.(st_code RTL.instruction) (reserve_instr_wf s))
     (reserve_instr_incr s).

FLemma update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode RTL.instruction) ->
  forall pc,
    Plt pc s.(st_nextnode RTL.instruction) \/ (PTree.set n i s.(st_code RTL.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode RTL.instruction)),
  s.(st_code RTL.instruction)!n = None ->
  state_incr RTL.instruction s
             (mkstate RTL.instruction s.(st_nextreg RTL.instruction) s.(st_nextnode RTL.instruction) (PTree.set n i s.(st_code RTL.instruction))
                     (update_instr_wf s n i LT)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma check_empty_node:
  forall (s: state) (n: RTL.node), { s.(st_code RTL.instruction)!n = None } + { True }.
FProofLemma.  intros. case (s.(st_code self__Base.RTL.instruction)!n); intros. right; auto. left; auto. Qed. CloseFLemma.

FDefinition update_instr : RTL.node -> RTL.instruction -> mon unit := fun (n: RTL.node) (i: RTL.instruction) => 
  fun s =>
    match plt n s.(st_nextnode RTL.instruction), check_empty_node s n with
    | left L, left EMPTY =>
        OK tt
           (mkstate RTL.instruction s.(st_nextreg RTL.instruction) s.(st_nextnode RTL.instruction) (PTree.set n i s.(st_code RTL.instruction))
                    (update_instr_wf s n i L))
           (update_instr_incr s n i L EMPTY)
    | _, _ =>
        Error (Errors.msg "RTLgen.update_instr")
    end.

FLemma new_reg_incr:
  forall s,
  state_incr RTL.instruction s (mkstate RTL.instruction (Pos.succ s.(st_nextreg RTL.instruction))
                        s.(st_nextnode RTL.instruction) s.(st_code RTL.instruction) s.(st_wf RTL.instruction)).
FProofLemma. constructor; simpl. apply Ple_refl. apply Ple_succ. auto. Qed. CloseFLemma.

FDefinition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg RTL.instruction)
       (mkstate RTL.instruction (Pos.succ s.(st_nextreg RTL.instruction)) s.(st_nextnode RTL.instruction) s.(st_code RTL.instruction) s.(st_wf RTL.instruction))
       (new_reg_incr s).

FDefinition init_mapping : mapping :=
  mkmapping (PTree.empty reg) nil.

FDefinition add_var : mapping -> ident -> mon (reg * mapping) := fun map name => 
  do r <- new_reg;
     ret (r, mkmapping (PTree.set name r map.(map_vars))
                       map.(map_letvars)).

MetaData add_vars.
Fixpoint add_vars (map: mapping) (names: list ident)
                  {struct names} : self__RTLgen.mon (list reg * mapping) :=
  match names with
  | nil => ret (nil, map)
  | n1 :: nl =>
      do (rl, map1) <- add_vars map nl;
      do (r1, map2) <- self__RTLgen.add_var map1 n1;
      ret (r1 :: rl, map2)
  end.
FEnd add_vars.

FDefinition find_var : mapping -> ident -> mon reg := fun (map: mapping) (name: ident) =>
  match PTree.get name map.(map_vars) with
  | None => error (Errors.MSG "RTLgen: unbound variable " :: Errors.CTX name :: nil)
  | Some r => ret r
  end.

FDefinition add_letvar : mapping -> reg -> mapping := fun (map: mapping) (r: reg) =>
  mkmapping map.(map_vars) (r :: map.(map_letvars)).

FDefinition find_letvar : mapping -> nat -> mon reg := fun (map: mapping) (idx: nat) =>
  match List.nth_error map.(map_letvars) idx with
  | None => error (Errors.msg "RTLgen: unbound let variable")
  | Some r => ret r
  end.

FDefinition add_move : reg -> reg -> RTL.node -> mon RTL.node := fun (rs rd: reg) (nd: RTL.node) => 
  if Reg.eq rs rd
  then ret nd
  else add_instr (RTL.Iop Asm.Omove (rs::nil) rd nd).

FRecursion alloc_reg about CminorSel.expr motive (fun (_ : CminorSel.expr) => mapping -> mon reg) by _rect.
Case Evar id := (fun map => find_var map id).
Case Eletvar n := (fun map => find_letvar map n).
Case Eop := (fun op args => fun map => new_reg).
Case Econdition c a0 a1 := (fun map => new_reg).
Case Elet a b := (fun map => new_reg).
FEnd alloc_reg.

FRecursion alloc_regs about CminorSel.exprlist motive (fun (_ : CminorSel.exprlist) => mapping -> mon (list reg)) by _rect.
Case Enil := (fun map => ret nil).
Case Econs a bl :=
(fun map =>
  do r <- alloc_reg a map;
  do rl <- alloc_regs bl map;
  ret (r :: rl)).
FEnd alloc_regs.

FRecursion transl_expr about CminorSel.expr motive (fun (_ : CminorSel.expr) => mapping -> reg -> RTL.node -> mon RTL.node)
  with transl_exprlist about CminorSel.exprlist motive (fun (_ : CminorSel.exprlist) => mapping -> list reg -> RTL.node -> mon RTL.node)
  with transl_condexpr about CminorSel.condexpr motive (fun (_ : CminorSel.condexpr) => mapping  -> RTL.node -> RTL.node -> mon RTL.node) by _rect.
Case Evar v := (fun map rd nd => do r <- find_var map v; add_move r rd nd).
Case Elet b c :=
(fun map rd nd => 
   do r <- new_reg;
   do nc <- transl_expr c (add_letvar map r) rd nd;
   transl_expr b map r nc).
Case Eop op al :=
(fun map rd nd => 
    do rl <- alloc_regs al map;
    do no <- add_instr (RTL.Iop op rl rd nd);
    transl_exprlist al map rl no).
Case Econdition a b c :=
(fun map rd nd => 
  do nfalse <- transl_expr c map rd nd;
  do ntrue <- transl_expr b map rd nd;
  transl_condexpr a map ntrue nfalse).
Case Eletvar n := (fun map rd nd => do r <- find_letvar map n; add_move r rd nd).

(* exprlist *)
Case Enil := (fun map rl nd => match rl with nil => ret nd | _ => error (Errors.msg "RTLgen.transl_exprlist") end).
Case Econs b bs :=
(fun map rl nd => 
   match rl with 
   | r :: rs =>  
       do no <- transl_exprlist bs map rs nd; 
       transl_expr b map r no
   | _ => error (Errors.msg "RTLgen.transl_exprlist") end).

(* condexpr *)
Case CEcond c al :=
(fun map ntrue nfalse => 
   do rl <- alloc_regs al map;
   do nt <- add_instr (RTL.Icond c rl ntrue nfalse);
   transl_exprlist al map rl nt).
Case CEcondition a b c :=
(fun map ntrue nfalse => 
   do nc <- transl_condexpr c map ntrue nfalse;
   do nb <- transl_condexpr b map ntrue nfalse;
   transl_condexpr a map nb nc).
Case CElet b c :=
(fun map ntrue nfalse => 
   do r <- new_reg;
   do nc <- transl_condexpr c (add_letvar map r) ntrue nfalse;
   transl_expr b map r nc).
FEnd transl_expr with transl_exprlist with transl_condexpr.
        
FDefinition labelmap : Type := PTree.t RTL.node.
        
FRecursion transl_stmt about CminorSel.stmt motive (fun (_ : CminorSel.stmt) => mapping -> RTL.node -> list RTL.node -> labelmap -> RTL.node -> option reg -> mon RTL.node) by _rect.
Case Sskip := (fun map nd nexits ngoto nret rret => ret nd).
Case Sassign v b :=
(fun map nd nexits ngoto nret rret => 
   do r <- find_var map v;
   transl_expr b map r nd). 
Case Sseq s1 s2 :=
(fun map nd nexits ngoto nret rret =>  
   do ns <- transl_stmt s2 map nd nexits ngoto nret rret;
   transl_stmt s1 map ns nexits ngoto nret rret).
Case Sifthenelse c strue sfalse :=
(fun map nd nexits ngoto nret rret => 
   (* Don't use "more likely" heuristic *)
   do ntrue <- transl_stmt strue map nd nexits ngoto nret rret;
   do nfalse <- transl_stmt sfalse map nd nexits ngoto nret rret;
   transl_condexpr c map ntrue nfalse).
Case Sreturn opt_a :=
(fun map nd nexits ngoto nret rret => 
  match opt_a, rret with
  | None, _ => ret nret
  | Some a, Some r => transl_expr a map r nret
  | _, _ => error (Errors.msg "RTLgen: type mismatch on return")
  end).
Case Slabel lbl s' :=
(fun map nd nexits ngoto nret rret => 
  do ns <- transl_stmt s' map nd nexits ngoto nret rret;
  match ngoto!lbl with
  | None => error (Errors.msg "RTLgen: unbound label")
  | Some n =>
      do xx <-
        (handle_error (update_instr n (RTL.Inop ns))
                      (error (Errors.MSG "Multiply-defined label " ::
                              Errors.CTX lbl :: nil)));
      ret ns
  end).
Case Sgoto lbl :=
(fun map nd nexits ngoto nret rret => 
  match ngoto!lbl with
  | None => error (Errors.MSG "Undefined defined label " ::
                  Errors.CTX lbl :: nil)
  | Some n => ret n
  end).
(* TODO: remove this, there is no set in CminorSel *)
Case Sset := cheat.
FEnd transl_stmt.

FDefinition alloc_label : Cminor.label -> labelmap -> mon labelmap :=
  fun (lbl: Cminor.label) (map: labelmap) =>
  do n <- reserve_instr;
  ret (PTree.set lbl n map).   

FRecursion reserve_labels about CminorSel.stmt
  motive (fun (_ : CminorSel.stmt) => labelmap -> mon labelmap) by _rect.
Case Sseq s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Sifthenelse e s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Slabel lbl s1 := (fun lm => do lm' <- reserve_labels s1 lm; alloc_label lbl lm').
Case Sskip := (fun lm => ret lm).
Case Sassign i e := (fun lm => ret lm).
Case Sset i e := (fun lm => ret lm).
Case Sreturn a := (fun lm => ret lm).
Case Sgoto lbl := (fun lm => ret lm).
FEnd reserve_labels.

FDefinition ret_reg : signature -> reg -> option reg :=
  fun (sig: signature) (rd: reg) =>
  if rettype_eq sig.(AST.sig_res) AST.Tvoid then None else Some rd.

FDefinition transl_fun : CminorSel.function -> mon (RTL.node * list reg) :=
  fun (f: CminorSel.function) => 
  do ngoto <- reserve_labels f.(self__Base.CminorSel.fn_body) (PTree.empty RTL.node);
  do (rparams, map1) <- add_vars init_mapping f.(self__Base.CminorSel.fn_params);
  do (rvars, map2) <- add_vars map1 f.(self__Base.CminorSel.fn_vars);
  do rret <- new_reg;
  let orret := ret_reg f.(self__Base.CminorSel.fn_sig) rret in
  do nret <- add_instr (RTL.Ireturn orret);
  do nentry <- transl_stmt f.(self__Base.CminorSel.fn_body) map2 nret nil ngoto nret orret;
  ret (nentry, rparams).

FDefinition transl_function : CminorSel.function -> Errors.res RTL.function := 
    fun (f: CminorSel.function) => 
  match transl_fun f init_state with
  | Error msg => Errors.Error msg
  | OK (nentry, rparams) s i =>
      Errors.OK (RTL.mkfunction
                   f.(self__Base.CminorSel.fn_sig)
                   rparams
                   f.(self__Base.CminorSel.fn_stackspace)
                   s.(st_code RTL.instruction)
                   nentry)
  end.

FDefinition transl_fundef := transf_partial_fundef transl_function.

FDefinition transl_program : CminorSel.program -> Errors.res RTL.program := 
  fun (p: CminorSel.program) =>
     transform_partial_program transl_fundef p.

(*
(* relational spec *)

FDefinition reg_in_map : mapping -> reg -> Prop := fun (m: mapping) (r: reg) =>
  (exists id, m.(map_vars)!id = Some r) \/ In r m.(map_letvars).

MetaData tr_move.
Inductive tr_move (c: self__Base.RTL.code): self__Base.RTL.node -> reg -> self__Base.RTL.node -> reg -> Prop :=
| tr_move_0: forall n r,
    tr_move c n r n r
| tr_move_1: forall ns rs nd rd,
    c!ns = Some (self__Base.RTL.Iop self__Base.Asm.Omove (rs :: nil) rd nd) ->
    tr_move c ns rs nd rd.
FEnd tr_move.

MetaData reg_map_ok.
Inductive reg_map_ok: mapping -> reg -> option AST.ident -> Prop :=
| reg_map_ok_novar: forall map rd,
    ~self__RTLgen.reg_in_map map rd ->
    reg_map_ok map rd None
| reg_map_ok_somevar: forall map rd id,
    map.(map_vars)!id = Some rd ->
    reg_map_ok map rd (Some id).

Global Hint Resolve reg_map_ok_novar: rtlg.
FEnd reg_map_ok. 
                 
FInductive tr_expr : RTL.code -> mapping -> list reg -> CminorSel.expr -> RTL.node -> RTL.node -> reg -> option AST.ident -> Prop :=
| tr_Evar: forall c map pr id ns nd r rd dst,
    map.(map_vars)!id = Some r ->
    ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
    tr_move c ns r nd rd ->
    tr_expr c map pr (CminorSel.Evar id) ns nd rd dst            
| tr_Eop: forall c map pr op al ns nd rd n1 rl dst,
    tr_exprlist c map pr al ns n1 rl ->
    c!n1 = Some (RTL.Iop op rl rd nd) ->
    reg_map_ok map rd dst -> ~In rd pr ->
    tr_expr c map pr (CminorSel.Eop op al) ns nd rd dst            
| tr_Econdition: forall c map pr a ifso ifnot ns nd rd ntrue nfalse dst,
    tr_condition c map pr a ns ntrue nfalse ->
    tr_expr c map pr ifso ntrue nd rd dst ->
    tr_expr c map pr ifnot nfalse nd rd dst ->
    tr_expr c map pr (CminorSel.Econdition a ifso ifnot) ns nd rd dst
| tr_Elet: forall c map pr b1 b2 ns nd rd n1 r dst,
    ~reg_in_map map r ->
    tr_expr c map pr b1 ns n1 r None ->
    tr_expr c (add_letvar map r) pr b2 n1 nd rd dst ->
    tr_expr c map pr (CminorSel.Elet b1 b2) ns nd rd dst
| tr_Eletvar: forall c map pr n ns nd rd r dst,
    List.nth_error map.(map_letvars) n = Some r ->
    ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
    tr_move c ns r nd rd ->
    tr_expr c map pr (CminorSel.Eletvar n) ns nd rd dst
with tr_condition : RTL.code -> mapping -> list reg -> CminorSel.condexpr -> RTL.node -> RTL.node -> RTL.node -> Prop :=
| tr_CEcond: forall c map pr cond bl ns ntrue nfalse n1 rl,
    tr_exprlist c map pr bl ns n1 rl ->
    c!n1 = Some (RTL.Icond cond rl ntrue nfalse) ->
    tr_condition c map pr (CminorSel.CEcond cond bl) ns ntrue nfalse
| tr_CEcondition: forall c map pr a1 a2 a3 ns ntrue nfalse n2 n3,
    tr_condition c map pr a1 ns n2 n3 ->
    tr_condition c map pr a2 n2 ntrue nfalse ->
    tr_condition c map pr a3 n3 ntrue nfalse ->
    tr_condition c map pr (CminorSel.CEcondition a1 a2 a3) ns ntrue nfalse
| tr_CElet: forall c map pr a b ns ntrue nfalse r n1,
    ~reg_in_map map r ->
    tr_expr c map pr a ns n1 r None ->
    tr_condition c (add_letvar map r) pr b n1 ntrue nfalse ->
    tr_condition c map pr (CminorSel.CElet a b) ns ntrue nfalse
with tr_exprlist : RTL.code -> mapping -> list reg -> CminorSel.exprlist -> RTL.node -> RTL.node -> list reg -> Prop :=
| tr_Enil: forall c map pr n,
    tr_exprlist c map pr CminorSel.Enil n n nil
| tr_Econs: forall c map pr a1 al ns nd r1 rl n1,
    tr_expr c map pr a1 ns n1 r1 None ->
    tr_exprlist c map (r1 :: pr) al n1 nd rl ->
    tr_exprlist c map pr (CminorSel.Econs a1 al) ns nd (r1 :: rl).
    
FInductive tr_stmt : RTL.code -> mapping -> CminorSel.stmt -> RTL.node -> RTL.node -> list RTL.node -> labelmap -> RTL.node -> option reg -> Prop :=
| tr_Sskip: forall c map ns nexits ngoto nret rret,
    tr_stmt c map CminorSel.Sskip ns ns nexits ngoto nret rret            
| tr_Sassign: forall c map id a ns nd nexits ngoto nret rret r,
  map.(map_vars)!id = Some r ->
  tr_expr c map nil a ns nd r (Some id) ->
  tr_stmt c map (CminorSel.Sassign id a) ns nd nexits ngoto nret rret          
| tr_Sseq: forall c map s1 s2 ns nd nexits ngoto nret rret n,
  tr_stmt c map s2 n nd nexits ngoto nret rret ->
  tr_stmt c map s1 ns n nexits ngoto nret rret ->
  tr_stmt c map (CminorSel.Sseq s1 s2) ns nd nexits ngoto nret rret
| tr_Sifthenelse: forall c map a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse,
  tr_stmt c map strue ntrue nd nexits ngoto nret rret ->
  tr_stmt c map sfalse nfalse nd nexits ngoto nret rret ->
  tr_condition c map nil a ns ntrue nfalse ->
  tr_stmt c map (CminorSel.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
| tr_Sreturn_none: forall c map nret nd nexits ngoto rret,
  tr_stmt c map (CminorSel.Sreturn None) nret nd nexits ngoto nret rret
| tr_Sreturn_some: forall c map a ns nd nexits ngoto nret rret,
  tr_expr c map nil a ns nret rret None ->
  tr_stmt c map (CminorSel.Sreturn (Some a)) ns nd nexits ngoto nret (Some rret)
| tr_Slabel: forall c map lbl s ns nd nexits ngoto nret rret n,
  ngoto!lbl = Some n ->
  c!n = Some (RTL.Inop ns) ->
  tr_stmt c map s ns nd nexits ngoto nret rret ->
  tr_stmt c map (CminorSel.Slabel lbl s) ns nd nexits ngoto nret rret
| tr_Sgoto: forall c map lbl ns nd nexits ngoto nret rret,
  ngoto!lbl = Some ns ->
  tr_stmt c map (CminorSel.Sgoto lbl) ns nd nexits ngoto nret rret.   

MetaData tr_function.
Inductive tr_function: self__Base.CminorSel.function -> self__Base.RTL.function -> Prop :=
| tr_function_intro:
    forall f code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret,
    self__RTLgen.add_vars self__RTLgen.init_mapping f.(self__Base.CminorSel.fn_params) s0 = OK (rparams, map1) s1 i1 ->
    self__RTLgen.add_vars map1 f.(self__Base.CminorSel.fn_vars) s1 = OK (rvars, map2) s2 i2 ->
    orret = self__RTLgen.ret_reg f.(self__Base.CminorSel.fn_sig) rret ->
    self__RTLgen.tr_stmt code map2 f.(self__Base.CminorSel.fn_body) nentry nret nil ngoto nret orret ->
    code!nret = Some(self__Base.RTL.Ireturn orret) ->
    tr_function f (self__Base.RTL.mkfunction
                    f.(self__Base.CminorSel.fn_sig)
                    rparams
                    f.(self__Base.CminorSel.fn_stackspace)
                    code
                    nentry).
FEnd tr_function.

(* Correctness of the spec *)
(*
Lemma tr_move_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall ns rs nd rd,
  tr_move s1.(st_code) ns rs nd rd ->
  tr_move s2.(st_code) ns rs nd rd.
Proof.

Lemma tr_expr_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr a ns nd rd dst,
  tr_expr s1.(st_code) map pr a ns nd rd dst ->
  tr_expr s2.(st_code) map pr a ns nd rd dst
with tr_condition_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr a ns ntrue nfalse,
  tr_condition s1.(st_code) map pr a ns ntrue nfalse ->
  tr_condition s2.(st_code) map pr a ns ntrue nfalse
with tr_exprlist_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr al ns nd rl,
  tr_exprlist s1.(st_code) map pr al ns nd rl ->
  tr_exprlist s2.(st_code) map pr al ns nd rl.
Proof.

Lemma add_move_charact:
  forall s ns rs nd rd s' i,
  add_move rs rd nd s = OK ns s' i ->
  tr_move s'.(st_code) ns rs nd rd.
Proof.

Lemma transl_expr_charact:
  forall a map rd nd s ns s' pr INCR
     (TR: transl_expr map a rd nd s = OK ns s' INCR)
     (WF: map_valid map s)
     (OK: target_reg_ok map pr a rd)
     (VALID: regs_valid pr s)
     (VALID2: reg_valid rd s),
   tr_expr s'.(st_code) map pr a ns nd rd None

with transl_exprlist_charact:
  forall al map rl nd s ns s' pr INCR
     (TR: transl_exprlist map al rl nd s = OK ns s' INCR)
     (WF: map_valid map s)
     (OK: target_regs_ok map pr al rl)
     (VALID1: regs_valid pr s)
     (VALID2: regs_valid rl s),
   tr_exprlist s'.(st_code) map pr al ns nd rl

with transl_condexpr_charact:
  forall a map ntrue nfalse s ns s' pr INCR
     (TR: transl_condexpr map a ntrue nfalse s = OK ns s' INCR)
     (WF: map_valid map s)
     (VALID: regs_valid pr s),
   tr_condition s'.(st_code) map pr a ns ntrue nfalse.

Proof.

A variant of transl_expr_charact, for use when the destination register is the one associated with a variable.

Lemma transl_expr_assign_charact:
  forall id a map rd nd s ns s' INCR
     (TR: transl_expr map a rd nd s = OK ns s' INCR)
     (WF: map_valid map s)
     (OK: reg_map_ok map rd (Some id)),
   tr_expr s'.(st_code) map nil a ns nd rd (Some id).
Proof.

Lemma alloc_optreg_map_ok:
  forall map optid s1 r s2 i,
  map_valid map s1 ->
  alloc_optreg map optid s1 = OK r s2 i ->
  reg_map_ok map r optid.
Proof.

Lemma tr_exitexpr_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map a ns nexits,
  tr_exitexpr s1.(st_code) map a ns nexits ->
  tr_exitexpr s2.(st_code) map a ns nexits.
Proof.

Lemma tr_stmt_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map s ns nd nexits ngoto nret rret,
  tr_stmt s1.(st_code) map s ns nd nexits ngoto nret rret ->
  tr_stmt s2.(st_code) map s ns nd nexits ngoto nret rret.
Proof.

Lemma transl_exit_charact:
  forall nexits n s ne s' incr,
  transl_exit nexits n s = OK ne s' incr ->
  nth_error nexits n = Some ne /\ s' = s.
Proof.

Lemma transl_jumptable_charact:
  forall nexits tbl s nl s' incr,
  transl_jumptable nexits tbl s = OK nl s' incr ->
  tr_jumptable nexits tbl nl /\ s' = s.
Proof.

Lemma transl_exitexpr_charact:
  forall nexits a map s ns s' INCR
     (TR: transl_exitexpr map a nexits s = OK ns s' INCR)
     (WF: map_valid map s),
  tr_exitexpr s'.(st_code) map a ns nexits.
Proof.

Lemma convert_builtin_res_charact:
  forall map oty res s res' s' INCR
    (TR: convert_builtin_res map oty res s = OK res' s' INCR)
    (WF: map_valid map s),
  tr_builtin_res map res res'.
Proof.

Lemma transl_stmt_charact:
  forall map stmt nd nexits ngoto nret rret s ns s' INCR
    (TR: transl_stmt map stmt nd nexits ngoto nret rret s = OK ns s' INCR)
    (WF: map_valid map s)
    (OK: return_reg_ok s map rret),
  tr_stmt s'.(st_code) map stmt ns nd nexits ngoto nret rret.
Proof.

Lemma transl_function_charact:
  forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
*)

*)                 
FEnd RTLgen.  

From NFPOP Require Import Machregs.

From NFPOP Require Import Conventions1.
From NFPOP Require Import Locations.
(* Some Machreg functions will defined here *)
Family M.
FRecursion destroyed_by_op about Asm.operation motive
  (fun (_ : Asm.operation) => list mreg) by _rect.
Case Omove := nil.
Case Ointconst n := nil.
Case Olongconst n := nil.
Case Ofloatconst f := nil.
Case Osingleconst s := nil.
Case Oaddrstack addr := nil.
Case Ocmp c := nil.
FEnd destroyed_by_op.

FDefinition destroyed_by_cond : Asm.condition -> list mreg := fun cond => nil. 
FEnd M.


Family LTL.
FDefinition node := positive.

FInductive instruction: Type :=
| Lop : Asm.operation -> list mreg -> mreg -> instruction
| Lgetstack : slot -> Z -> typ -> mreg -> instruction
| Lsetstack : mreg -> slot -> Z -> typ -> instruction 
| Lbranch : node -> instruction
| Lcond : Asm.condition -> list mreg -> node -> node -> instruction
| Lreturn : instruction.
       
FDefinition bblock := list instruction.
FDefinition code: Type := PTree.t bblock.

MetaData function.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: self__LTL.code;
  fn_entrypoint: self__LTL.node
}.
FEnd function.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => self__LTL.fn_sig f
  | AST.External ef => ef_sig ef
  end.
(*      
FDefinition genv := Genv.t fundef unit.
FDefinition locset := Locmap.t.

FDefinition eval_operation := fun op => Asm.eval_operation op fundef unit.

MetaData stackframe.
Inductive stackframe : Type :=
  | Stackframe:
      forall (f: self__LTL.function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (ls: self__LTL.locset)(* location state in calling function *)
             (bb: self__LTL.bblock),(* continuation in calling function *)
        stackframe.
FEnd stackframe.

MetaData state.
Inductive state : Type :=
  | State:
      forall (stack: list self__LTL.stackframe)(* call stack *)
             (f: self__LTL.function)(* function currently executing *)
             (sp: val)(* stack pointer *)
             (pc: self__LTL.node)(* current program point *)
             (ls: self__LTL.locset)(* location state *)
             (m: mem),(* memory state *)
      state
  | Block:
      forall (stack: list self__LTL.stackframe)(* call stack *)
             (f: self__LTL.function)(* function currently executing *)
             (sp: val)(* stack pointer *)
             (bb: self__LTL.bblock)(* current basic block *)
             (ls: self__LTL.locset)(* location state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list self__LTL.stackframe)(* call stack *)
             (f: self__LTL.fundef)(* function to call *)
             (ls: self__LTL.locset)(* location state of caller *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list self__LTL.stackframe)(* call stack *)
             (ls: self__LTL.locset)(* location state of callee *)
             (m: mem),(* memory state *)
        state.
FEnd state.

FDefinition reglist : locset -> list mreg -> list val := fun rs rl => 
  List.map (fun r => rs (R r)) rl.

MetaData undef_regs.
Fixpoint undef_regs (rl: list mreg) (rs: self__LTL.locset) : self__LTL.locset :=
  match rl with
  | nil => rs
  | r1 :: rl => Locmap.set (R r1) Vundef (undef_regs rl rs)
  end.
FEnd undef_regs.

FDefinition destroyed_by_getstack : slot -> list mreg := fun s => 
  match s with
  | Incoming => temp_for_parent_frame :: nil
  | _ => nil
  end.

FDefinition parent_locset : list stackframe -> locset := fun stack => 
  match stack with
  | nil => Locmap.init Vundef
  | self__LTL.Stackframe f sp ls bb :: stack' => ls
  end.

FDefinition return_regs : locset -> locset -> locset := fun caller callee => 
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then caller (R r) else callee (R r)
    | S Outgoing ofs ty => Vundef
    | S sl ofs ty => caller (S sl ofs ty)
    end.

FDefinition call_regs : locset -> locset := fun caller => 
  fun (l: loc) =>
    match l with
    | R r => caller (R r)
    | S Local ofs ty => Vundef
    | S Incoming ofs ty => caller (S Outgoing ofs ty)
    | S Outgoing ofs ty => Vundef
    end.
             
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_start_block: forall ge s f sp pc rs m bb,
    (self__LTL.fn_code f)!pc = Some bb ->
    step ge (self__LTL.State s f sp pc rs m)
      E0 (self__LTL.Block s f sp bb rs m)
| exec_Lop: forall ge s f sp op args res bb rs m v rs',
    eval_operation op ge sp (reglist rs args) m = Some v ->
    rs' = Locmap.set (R res) v (undef_regs (M.destroyed_by_op op) rs) ->
    step ge (self__LTL.Block s f sp (Lop op args res :: bb) rs m)
      E0 (self__LTL.Block s f sp bb rs' m)      
| exec_Lgetstack: forall ge s f sp sl ofs ty dst bb rs m rs',
    rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
    step ge (self__LTL.Block s f sp (Lgetstack sl ofs ty dst :: bb) rs m)
      E0 (self__LTL.Block s f sp bb rs' m)                   
| exec_Lsetstack: forall ge s f sp src sl ofs ty bb rs m rs',
    rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
    step ge (self__LTL.Block s f sp (Lsetstack src sl ofs ty :: bb) rs m)
      E0 (self__LTL.Block s f sp bb rs' m)                   
| exec_Lbranch: forall ge s f sp pc bb rs m,
    step ge (self__LTL.Block s f sp (Lbranch pc :: bb) rs m)
      E0 (self__LTL.State s f sp pc rs m)      
| exec_Lcond: forall ge s f sp cond args pc1 pc2 bb rs b pc rs' m,
    Asm.eval_condition cond (reglist rs args) m = Some b ->
    pc = (if b then pc1 else pc2) ->
    rs' = undef_regs (M.destroyed_by_cond cond) rs ->
    step ge (self__LTL.Block s f sp (Lcond cond args pc1 pc2 :: bb) rs m)
      E0 (self__LTL.State s f sp pc rs' m)                   
| exec_Lreturn: forall ge s f sp bb rs m m',
    Mem.free m sp 0 f.(self__LTL.fn_stacksize) = Some m' ->
    step ge (self__LTL.Block s f (Vptr sp Ptrofs.zero) (Lreturn :: bb) rs m)
      E0 (self__LTL.Returnstate s (return_regs (parent_locset s) rs) m')
| exec_return: forall ge f sp rs1 bb s rs m,
    step ge (self__LTL.Returnstate (self__LTL.Stackframe f sp rs1 bb :: s) rs m)
      E0 (self__LTL.Block s f sp bb rs m)
 | exec_function_internal: forall ge s f rs m m' sp rs',
      Mem.alloc m 0 f.(self__LTL.fn_stacksize) = (m', sp) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step ge (self__LTL.Callstate s (AST.Internal f) rs m)
        E0 (self__LTL.State s f (Vptr sp Ptrofs.zero) f.(self__LTL.fn_entrypoint) rs' m').      

MetaData initial_state.
Inductive initial_state (p: self__LTL.program): self__LTL.state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__LTL.funsig f = signature_main ->
    initial_state p (self__LTL.Callstate nil f (Locmap.init Vundef) m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__LTL.state -> int -> Prop :=
| final_state_intro: forall rs m retcode,
    Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
    final_state (self__LTL.Returnstate nil rs m) retcode.
FEnd final_state.*)

FRecursion successors_instr about instruction motive (fun (_ : instruction) =>  list node -> list node) by _rect.
Case Lop op args dst := (fun rest => rest).
Case Lgetstack a b c d := (fun rest => rest). 
Case Lsetstack a b c d := (fun rest => rest).
Case Lbranch s := (fun _  => s :: nil).
Case Lcond cond args s1 s2 := (fun _ => s1 :: s2 :: nil).
Case Lreturn := (fun rest => rest).
FEnd successors_instr.

MetaData successors_block.
Fixpoint successors_block (b: self__LTL.bblock) : list self__LTL.node :=
  match b with
  | nil => nil(* should never happen *)
  | op :: b' => self__LTL.successors_instr op (successors_block b')
  end.
FEnd successors_block.

FEnd LTL.

Family Lfam.
FDefinition label := positive.

FInductive instruction: Type :=
| Lop : Asm.operation -> list mreg -> mreg -> instruction
| Lcond : Asm.condition -> list mreg -> label -> instruction
| Llabel: label -> instruction
| Lgoto: label -> instruction                                                     
| Lreturn : instruction.

FDefinition code: Type := list instruction.

FOpaque Definition function : Type := cheat.
FOpaque Definition function_sig: function -> signature := cheat.
FOpaque Definition function_stacksize: function -> Z := cheat.
FOpaque Definition function_code: function -> code := cheat.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

(*
FDefinition genv := Genv.t fundef unit.
FDefinition eval_operation := fun op => Asm.eval_operation op fundef unit.
(* regset/locset *)
FOpaque Definition storeset : Type := cheat.
(* function/block *)
FOpaque Definition func_ptr : Type := cheat.
FOpaque Definition call_func_ptr : Type := cheat.
(* return address / locset *)
FOpaque Definition stack_state : Type := cheat.


MetaData stackframe.
Inductive stackframe : Type :=
| Stackframe:
    forall (f: self__Lfam.func_ptr)(* calling function *)
           (sp: val)(* stack pointer in calling function *)
           (ls: self__Lfam.stack_state)(* location state in calling function *)
           (bb: self__Lfam.code), (* program point in calling function *)
      stackframe.
FEnd stackframe.

MetaData state.
Inductive state: Type :=
| State:
    forall (stack: list self__Lfam.stackframe)(* call stack *)
           (f: self__Lfam.func_ptr)(* function currently executing *)
           (sp: val)(* stack pointer *)
           (c: self__Lfam.code)(* current program point *)
           (rs: self__Lfam.storeset)(* location state *)
           (m: mem),(* memory state *)
    state
| Callstate:
    forall (stack: list self__Lfam.stackframe)(* call stack *)
           (f: self__Lfam.call_func_ptr)(* function to call *)
           (rs: self__Lfam.storeset)(* location state at point of call *)
           (m: mem),(* memory state *)
    state
| Returnstate:
    forall (stack: list self__Lfam.stackframe)(* call stack *)
           (rs: self__Lfam.storeset)(* location state at point of return *)
           (m: mem),(* memory state *)
    state.
FEnd state.

FRecursion is_label about instruction motive (fun (_ : instruction) => label -> bool) by _rect.
Case Lop op arg dst := (fun lbl => false).
(*Case Lgetstack s i t dst := (fun lbl => false). 
Case Lsetstack d s i t := (fun lbl => false). *)
Case Lcond c args l := (fun lbl => false). 
Case Llabel lbl' := (fun lbl => if peq lbl lbl' then true else false).
Case Lgoto lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false). 
FEnd is_label.

MetaData find_label.
Fixpoint find_label (lbl: self__Lfam.label) (c: self__Lfam.code) {struct c} : option self__Lfam.code :=
  match c with
  | nil => None
  | i1 :: il => if self__Lfam.is_label i1 lbl then Some il else find_label lbl il
  end.
FEnd find_label.

(* FDefinition parent_locset : list stackframe -> locset := fun stack => 
  match stack with
  | nil => Locmap.init Vundef
  | self__Lfam.Stackframe f sp ls c :: stack' => ls
  end. *)

FOpaque Definition reglist : storeset -> list mreg -> list val := cheat.
FOpaque Definition undef_regs : list mreg -> storeset -> storeset := cheat.
FOpaque Definition set_storeset : mreg -> val -> storeset -> storeset := cheat.
FOpaque Definition find_func_ptr : genv -> func_ptr -> option fundef := cheat. 


FInductive step: genv -> state -> trace -> state -> Prop :=          
| exec_Llabel:
    forall ge s f sp lbl b rs m,
    step ge (self__Lfam.State s f sp (Llabel lbl :: b) rs m)
      E0 (self__Lfam.State s f sp b rs m)
| exec_Lgoto:
    forall ge s fb f sp lbl b rs m b',
    find_func_ptr ge fb = Some (AST.Internal f) -> 
    find_label lbl (function_code f) = Some b' ->
    step ge (self__Lfam.State s fb sp (Lgoto lbl :: b) rs m)
      E0 (self__Lfam.State s fb sp b' rs m)
| exec_Lop:
    forall ge s f sp op args res b rs m v rs',
    eval_operation op ge sp (reglist rs args) m = Some v ->
    rs' = set_storeset res v (undef_regs (M.destroyed_by_op op) rs) ->
    step ge (self__Lfam.State s f sp (Lop op args res :: b) rs m)
      E0 (self__Lfam.State s f sp b rs' m)
| exec_Lcond_true:
    forall ge s (fb: func_ptr) (f: function) sp cond args lbl b rs m rs' b',
    Asm.eval_condition cond (reglist rs args) m = Some true ->
    rs' = undef_regs (M.destroyed_by_cond cond) rs ->
    find_func_ptr ge fb = Some (AST.Internal f) -> 
    find_label lbl (function_code f) = Some b' ->
    step ge (self__Lfam.State s fb sp (Lcond cond args lbl :: b) rs m)
      E0 (self__Lfam.State s fb sp b' rs' m)
| exec_Lcond_false:
    forall ge s f sp cond args lbl b rs m rs',
    Asm.eval_condition cond (reglist rs args) m = Some false ->
    rs' = undef_regs (M.destroyed_by_cond cond) rs ->
    step ge (self__Lfam.State s f sp (Lcond cond args lbl :: b) rs m)
      E0 (self__Lfam.State s f sp b rs' m)
| exec_return:
      forall ge s f sp rs0 c rs m,
      step ge (self__Lfam.Returnstate (self__Lfam.Stackframe f sp rs0 c :: s) rs m)
        E0 (self__Lfam.State s f sp c rs m).*)

FEnd Lfam.

Family Linear extends Lfam.
FInductive instruction: Type :=
| Lgetstack: slot -> Z -> typ -> mreg -> instruction
| Lsetstack: mreg -> slot -> Z -> typ -> instruction.

Inherit code.

MetaData fn.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: self__Linear.code
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_sig := self__Linear.fn_sig.
FOverride Definition function_stacksize := self__Linear.fn_stacksize.
FOverride Definition function_code := self__Linear.fn_code.

(*
FOverride Definition storeset := Locmap.t.
FOverride Definition func_ptr := function.
FOverride Definition call_func_ptr := fundef.
FOverride Definition stack_state := storeset.

FRecursion is_label.
Case Lgetstack s i t dst := (fun lbl => false).
Case Lsetstack d s i t := (fun lbl => false).
FEnd is_label.

FOverride Definition reglist := LTL.reglist.
FOverride Definition undef_regs := LTL.undef_regs.
FOverride Definition set_storeset := fun dst => Locmap.set (R dst).
FOverride Definition find_func_ptr := fun ge f => Some (AST.Internal f).

FDefinition destroyed_by_getstack : slot -> list mreg := fun s => 
  match s with
  | Incoming => temp_for_parent_frame :: nil
  | _ => nil
  end.

FDefinition parent_locset : list stackframe -> storeset := fun stack => 
  match stack with
  | nil => Locmap.init Vundef
  | self__Linear.Stackframe f sp ls c :: stack' => ls
  end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lgetstack:
  forall ge s f sp sl ofs ty dst b rs m rs',
    rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
    step ge (self__Linear.State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
      E0 (self__Linear.State s f sp b rs' m)
| exec_Lsetstack:
  forall ge s f sp src sl ofs ty b rs m rs',
    rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
    step ge (self__Linear.State s f sp (Lsetstack src sl ofs ty :: b) rs m)
      E0 (self__Linear.State s f sp b rs' m)
| exec_function_internal:
    forall ge s f rs m rs' m' stk,
    Mem.alloc m 0 (function_stacksize f) = (m', stk) ->
    rs' = undef_regs destroyed_at_function_entry (LTL.call_regs rs) ->
    step ge (self__Linear.Callstate s (AST.Internal f) rs m)
      E0 (self__Linear.State s f (Vptr stk Ptrofs.zero) (function_code f) rs' m')
| exec_Lreturn:
      forall ge s f stk b rs m m',
      Mem.free m stk 0 (function_stacksize f) = Some m' ->
      step ge (self__Linear.State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m)
        E0 (self__Linear.Returnstate s (LTL.return_regs (parent_locset s) rs) m').

MetaData initial_state.
Inductive initial_state (p: self__Linear.program): self__Linear.state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__Linear.funsig f = signature_main ->
    initial_state p (self__Linear.Callstate nil f (Locmap.init Vundef) m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Linear.state -> int -> Prop :=
| final_state_intro: forall rs m retcode,
    Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
    final_state (self__Linear.Returnstate nil rs m) retcode.
FEnd final_state.*)
FEnd Linear.

Family Mach extends Lfam.
FInductive instruction: Type :=
| Lgetstack: ptrofs -> typ -> mreg -> instruction
| Lgetparam: ptrofs -> typ -> mreg -> instruction
| Lsetstack: mreg -> ptrofs -> typ -> instruction.

Inherit code.
        
MetaData fn.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_code: self__Mach.code;
  fn_stacksize: Z;
  fn_link_ofs: ptrofs;
  fn_retaddr_ofs: ptrofs 
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_sig := self__Mach.fn_sig.
FOverride Definition function_stacksize := self__Mach.fn_stacksize.
FOverride Definition function_code := self__Mach.fn_code.

From NFPOP Require Import Mregisters.        
(*
From NFPOP Require Import Mregisters.        
FOverride Definition storeset := Regmap.t val.
FOverride Definition func_ptr := block.
FOverride Definition call_func_ptr := block.
(* Asm return address in calling function *)
FOverride Definition stack_state := val.

FRecursion is_label.
Case Lgetstack ptr t dst := (fun lbl => false).
Case Lsetstack ptr i dst := (fun lbl => false).
Case Lgetparam ptr i dst := (fun lbl => false).
FEnd is_label.    

FDefinition load_stack := fun (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) =>
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

FDefinition store_stack := fun (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) =>
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

FOverride Definition reglist := fun a b => a ## b.
MetaData undef_regs_.
Fixpoint undef_regs_ (rl: list mreg) (rs: self__Mach.storeset) {struct rl} : self__Mach.storeset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs_ rl' rs)
  end.
FEnd undef_regs_.
FOverride Definition undef_regs := undef_regs_.
FOverride Definition set_storeset := fun b c a => a # b <- c.
FOverride Definition find_func_ptr := fun ge fb => Genv.find_funct_ptr ge fb.

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
| exec_Lgetstack:
      forall ge s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step ge (self__Mach.State s f sp (Lgetstack ofs ty dst :: c) rs m)
        E0 (self__Mach.State s f sp c (rs#dst <- v) m)
| exec_Lsetstack:
      forall ge s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step ge (self__Mach.State s f sp (Lsetstack src ofs ty :: c) rs m)
        E0 (self__Mach.State s f sp c rs' m')
| exec_Lgetparam:
      forall ge s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      load_stack m sp Tptr f.(self__Mach.fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step ge (self__Mach.State s fb sp (Lgetparam ofs ty dst :: c) rs m)
        E0 (self__Mach.State s fb sp c rs' m)
| exec_function_internal:
      forall ge s fb rs m f m1 m2 m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      Mem.alloc m 0 f.(self__Mach.fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr f.(self__Mach.fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tptr f.(self__Mach.fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step ge (self__Mach.Callstate s fb rs m)
        E0 (self__Mach.State s fb sp f.(self__Mach.fn_code) rs' m3)
| exec_Lreturn:
      forall ge s fb stk soff c rs m f m',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(self__Mach.fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(self__Mach.fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(self__Mach.fn_stacksize) = Some m' ->
      step ge (self__Mach.State s fb (Vptr stk soff) (Lreturn :: c) rs m)
        E0 (self__Mach.Returnstate s rs m').

MetaData initial_state.
Inductive initial_state (p: self__Mach.program): self__Mach.state -> Prop :=
  | initial_state_intro: forall fb m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(AST.prog_main) = Some fb ->
      initial_state p (self__Mach.Callstate nil fb (Regmap.init Vundef) m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Mach.state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = AST.One r ->
      rs r = Vint retcode ->
      final_state (self__Mach.Returnstate nil rs m) retcode.
FEnd final_state.*)

FEnd Mach.

(* LTL -> Linear *)
Family Linearize.

From NFPOP Require Import Lattice.
From NFPOP Require Import Kildall.

(* Determination of the order of basic blocks *)

Module DS := Dataflow_Solver(LBoolean)(NodeSetForward).

FDefinition reachable_aux : LTL.function -> option (PMap.t bool) :=
  fun (f: LTL.function) =>
  DS.fixpoint
    (LTL.fn_code f) LTL.successors_block
    (fun pc r => r)
    f.(self__Base.LTL.fn_entrypoint) true.

FDefinition reachable : LTL.function -> PMap.t bool := fun f =>
  match reachable_aux f with
  | None => PMap.init true
  | Some rs => rs
  end.

MetaData enumerate_aux.
Parameter enumerate_aux: self__Base.LTL.function -> PMap.t bool -> list self__Base.LTL.node.
FEnd enumerate_aux.

Module Nodeset := FSetAVL.Make(OrderedPositive).

From NFPOP Require Import Errors.
Open Scope error_monad_scope.

MetaData nodeset_of_list.
Fixpoint nodeset_of_list (l: list self__Base.LTL.node) (s: Nodeset.t)
                         {struct l}: res Nodeset.t :=
  match l with
  | nil => OK s
  | hd :: tl =>
      if Nodeset.mem hd s
      then Error (msg "Linearize: duplicates in enumeration")
      else nodeset_of_list tl (Nodeset.add hd s)
  end.
FEnd nodeset_of_list.

FDefinition check_reachable_aux := 
     fun (reach: PMap.t bool) (s: Nodeset.t)
     (ok: bool) (pc: LTL.node) (bb: LTL.bblock) =>
  if reach!!pc then ok && Nodeset.mem pc s else ok.

FDefinition check_reachable := 
     fun (f: LTL.function) (reach: PMap.t bool) (s: Nodeset.t) =>
  PTree.fold (check_reachable_aux reach s) f.(self__Base.LTL.fn_code) true.

FDefinition enumerate : LTL.function -> res (list LTL.node) := fun f => 
  let reach := reachable f in
  let enum := enumerate_aux f reach in
  do s <- nodeset_of_list enum Nodeset.empty;
  if check_reachable f reach s
  then OK enum
  else Error (msg "Linearize: wrong enumeration").

FRecursion starts_with_label about Linear.instruction motive (fun (_ : Linear.instruction) => Linear.label -> bool) by _rect.
Case Llabel lbl' := (fun lbl => peq lbl lbl').
Case Lop op args res := (fun lbl => false).
Case Lgetstack sl ofs ty r := (fun lbl => false).
Case Lsetstack r sl ofs ty := (fun lbl => false).
Case Lcond cond args lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false).
Case Lgoto lbl' := (fun lbl => false).
FEnd starts_with_label.

MetaData starts_with.
Fixpoint starts_with (lbl: self__Base.Linear.label) (k: self__Base.Linear.code) {struct k} : bool :=
     match k with
     | i :: k' => if self__Linearize.starts_with_label i lbl then true else starts_with lbl k'
     | _ => false
     end.
FEnd starts_with.
              
FDefinition add_branch : Linear.label -> Linear.code -> Linear.code := fun (s: Linear.label) (k: Linear.code) =>
   if starts_with s k then k else Linear.Lgoto s :: k.

FRecursion translate_instr about LTL.instruction motive (fun (_ : LTL.instruction) => (Linear.code -> Linear.code) -> Linear.code -> Linear.code) by _rect.
Case Lop op args res := (fun f k => Linear.Lop op args res :: f k).
Case Lgetstack sl ofs ty r := (fun f k => Linear.Lgetstack sl ofs ty r :: f k).
Case Lsetstack r sl ofs ty := (fun f k => Linear.Lsetstack r sl ofs ty :: f k).
Case Lbranch s := (fun f k => add_branch s k).
Case Lcond cond args s1 s2 :=
(fun f k => if starts_with s1 k then Linear.Lcond (Asm.negate_condition cond) args s2 :: add_branch s1 k else Linear.Lcond cond args s1 :: add_branch s2 k).
Case Lreturn := (fun f k => Linear.Lreturn :: f k).
FEnd translate_instr.
       
MetaData linearize_block.
Fixpoint linearize_block (b: self__Base.LTL.bblock) (k: self__Base.Linear.code) : self__Base.Linear.code :=
   match b with
   | nil => k
   | i :: b' => self__Linearize.translate_instr i (linearize_block b') k
   end.
FEnd linearize_block.

FDefinition linearize_node : LTL.function -> LTL.node -> Linear.code -> Linear.code :=
  fun (f: LTL.function) (pc: LTL.node) (k: Linear.code) =>
  match f.(self__Base.LTL.fn_code)!pc with
  | None => k
  | Some b => Linear.Llabel pc :: linearize_block b k
  end.

FDefinition linearize_body : LTL.function -> list LTL.node -> Linear.code :=
  fun (f: LTL.function) (enum: list LTL.node) =>
  list_fold_right (linearize_node f) enum nil.

FDefinition transf_function : LTL.function -> res Linear.function := fun f =>
  do enum <- enumerate f;
  OK (Linear.mkfunction
       (LTL.fn_sig f)
       (LTL.fn_stacksize f)
       (add_branch (LTL.fn_entrypoint f) (linearize_body f enum))).

FDefinition transf_fundef : LTL.fundef -> res Linear.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : LTL.program -> res Linear.program := fun p =>
  transform_partial_program transf_fundef p.

(* correctness *)

(*
Inductive match_stackframes: LTL.stackframe -> Linear.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp bb ls tf c,
      transf_function f = OK tf ->
      (forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true) ->
      is_tail c tf.(fn_code) ->
      match_stackframes
        (LTL.Stackframe f sp ls bb)
        (Linear.Stackframe tf sp ls (linearize_block bb c)).

Inductive match_states: LTL.state -> Linear.state -> Prop :=
  | match_states_add_branch:
      forall s f sp pc ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (TAIL: is_tail c tf.(fn_code)),
      match_states (LTL.State s f sp pc ls m)
                   (Linear.State ts tf sp (add_branch pc c) ls m)
  | match_states_cond_taken:
      forall s f sp pc ls m tf ts cond args c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (JUMP: eval_condition cond (reglist ls args) m = Some true),
      match_states (LTL.State s f sp pc (undef_regs (destroyed_by_cond cond) ls) m)
                   (Linear.State ts tf sp (Lcond cond args pc :: c) ls m)
  | match_states_jumptable:
      forall s f sp pc ls m tf ts arg tbl c n
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (ARG: ls (R arg) = Vint n)
        (JUMP: list_nth_z tbl (Int.unsigned n) = Some pc),
      match_states (LTL.State s f sp pc (undef_regs destroyed_by_jumptable ls) m)
                   (Linear.State ts tf sp (Ljumptable arg tbl :: c) ls m)
  | match_states_block:
      forall s f sp bb ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true)
        (TAIL: is_tail c tf.(fn_code)),
      match_states (LTL.Block s f sp bb ls m)
                   (Linear.State ts tf sp (linearize_block bb c) ls m)
  | match_states_call:
      forall s f ls m tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (LTL.Callstate s f ls m)
                   (Linear.Callstate ts tf ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (LTL.Returnstate s ls m)
                   (Linear.Returnstate ts ls m).

Theorem transf_step_correct:
  forall s1 t s2, LTL.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus Linear.step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.

Lemma transf_initial_states:
  forall st1, LTL.initial_state prog st1 ->
  exists st2, Linear.initial_state tprog st2 /\ match_states st1 st2.
Proof.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> LTL.final_state st1 r -> Linear.final_state st2 r.
Proof.


*)

FEnd Linearize.
   
(* Linear -> Mach *)
Family Stacking.

From NFPOP Require Import Bounds.
(* Fields in bounds that depend on late bound names *)

FRecursion record_regs_of_instr about Linear.instruction motive
  (fun (_ : Linear.instruction) => RegSet.t -> Regset.t) by _rect.
Case Lreturn := cheat. (* (fun u => u).*)
Case Lgetstack sl ofs ty r := cheat. (* (fun u => record_reg u r).*)
Case Lsetstack r sl ofs ty := cheat. (* (fun u => record_reg u r).*)
Case Lop op args res := cheat. (* (fun u => record_reg u res). *)
Case Llabel lbl := cheat. (* (fun u => u). *)
Case Lgoto lbl := cheat. (* (fun u => u). *)
Case Lcond cond args lbl := cheat. (* (fun u => u). *)
FEnd record_regs_of_instr.

FDefinition record_regs_of_function : Linear.function -> RegSet.t := fun f =>
  fold_left (fun u i => cheat (* record_regs_of_instr i u*)) (Linear.fn_code f) RegSet.empty.

FRecursion slots_of_instr about Linear.instruction motive
  (fun (_ : Linear.instruction) => list (slot * Z * typ)) by _rect.
Case Lreturn := nil.
Case Lgetstack sl ofs ty r := ((sl, ofs, ty) :: nil).
Case Lsetstack r sl ofs ty := ((sl, ofs, ty) :: nil).
Case Lop op args res := nil.
Case Llabel lbl := nil.
Case Lgoto lbl := nil.
Case Lcond cond args lbl := nil.
FEnd slots_of_instr.

FRecursion outgoing_space about Linear.instruction motive
  (fun (_ : Linear.instruction) => Z) by _rect.
Case Lreturn := 0.
Case Lgetstack sl ofs ty r := 0.
Case Lsetstack r sl ofs ty := 0.
Case Lop op args res := 0.
Case Llabel lbl := 0.
Case Lgoto lbl := 0.
Case Lcond cond args lbl := 0.
FEnd outgoing_space.

FDefinition max_over_instrs : (Linear.instruction -> Z) -> Linear.function -> Z := fun valu f =>
  max_over_list valu (Linear.fn_code f).

FDefinition max_over_slots_of_instr : (slot * Z * typ -> Z) -> Linear.instruction -> Z := fun valu i =>
  max_over_list valu (slots_of_instr i).

FDefinition max_over_slots_of_funct : (slot * Z * typ -> Z) -> Linear.function -> Z := fun valu f =>
  max_over_instrs (max_over_slots_of_instr valu) f.

MetaData function_bounds.
Program Definition function_bounds (f: self__Base.Linear.function) := {|
  used_callee_save := RegSet.elements (self__Stacking.record_regs_of_function f);
  bound_local := self__Stacking.max_over_slots_of_funct local_slot f;
  bound_outgoing := Z.max (self__Stacking.max_over_instrs self__Stacking.outgoing_space f) (self__Stacking.max_over_slots_of_funct outgoing_slot f);
  bound_stack_data := Z.max (self__Base.Linear.fn_stacksize f) 0
|}.
Next Obligation.
  apply cheat.
Qed.
Next Obligation.
  apply cheat.
Qed.
Next Obligation.
  apply cheat.
Qed.
Next Obligation.
  apply cheat.
Qed.
Next Obligation.
  apply cheat.
Qed.
FEnd function_bounds.

From NFPOP Require Import Stacklayout.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

FDefinition offset_arg := fun (x: Z) => fe_ofs_arg + 4 * x.

FDefinition transl_op := fun (fe: frame_env) (op: Asm.operation) =>
    Asm.shift_stack_operation op fe.(fe_stack_data).

MetaData save_callee_save_rec.
Fixpoint save_callee_save_rec (rl: list mreg) (ofs: Z) (k: self__Base.Mach.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      self__Base.Mach.Lsetstack r (Ptrofs.repr ofs1) ty :: save_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd save_callee_save_rec.

FDefinition save_callee_save := fun (fe: frame_env) (k: Mach.code) =>
  save_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

MetaData restore_callee_save_rec.
Fixpoint restore_callee_save_rec (rl: list mreg) (ofs: Z) (k: self__Base.Mach.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      self__Base.Mach.Lgetstack (Ptrofs.repr ofs1) ty r :: restore_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd restore_callee_save_rec.

FDefinition restore_callee_save := fun (fe: frame_env) (k: Mach.code) =>
  restore_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

FRecursion transl_instr about Linear.instruction motive (fun (_ : Linear.instruction) => frame_env -> Mach.code -> Mach.code) by _rect.
Case Lgetstack sl ofs ty r :=
(fun fe k => 
match sl with
| Local =>
    Mach.Lgetstack (Ptrofs.repr (offset_local fe ofs)) ty r :: k
| Incoming =>
    Mach.Lgetparam (Ptrofs.repr (offset_arg ofs)) ty r :: k
| Outgoing =>
    Mach.Lgetstack (Ptrofs.repr (offset_arg ofs)) ty r :: k
end).
Case Lsetstack r sl ofs ty :=
(fun fe k => 
  match sl with
  | Local =>
      Mach.Lsetstack r (Ptrofs.repr (offset_local fe ofs)) ty :: k
  | Incoming =>
      k
  | Outgoing =>
      Mach.Lsetstack r (Ptrofs.repr (offset_arg ofs)) ty :: k
  end).
Case Lop op args res := (fun fe k =>  Mach.Lop (transl_op fe op) args res :: k).
Case Llabel lbl := (fun fe k => Mach.Llabel lbl :: k).
Case Lgoto lbl := (fun fe k => Mach.Lgoto lbl :: k).
Case Lcond cond args lbl := (fun fe k => Mach.Lcond cond args lbl :: k).
Case Lreturn := (fun fe k =>  restore_callee_save fe (Mach.Lreturn :: k)).
FEnd transl_instr.

FDefinition transl_code : frame_env -> list Linear.instruction -> Mach.code := fun fe il =>     
  list_fold_right (fun i k => transl_instr i fe k) il nil.

FDefinition transl_body := fun (f: Linear.function) (fe: frame_env) =>
  save_callee_save fe (transl_code fe (Linear.fn_code f)).

Local Open Scope string_scope.

FDefinition transf_function : Linear.function -> res Mach.function := fun f =>
  let fe := make_env (function_bounds f) in
  (* Don't type check linear *)
  (*if negb (wt_function f) then
    Error (msg "Ill-formed Linear code")*)
  if zlt Ptrofs.max_unsigned fe.(fe_size) then
    Error (msg "Too many spilled variables, stack size exceeded")
  else
    OK (Mach.mkfunction
         f.(self__Base.Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr))).

FDefinition transf_fundef : Linear.fundef -> res Mach.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : Linear.program -> res Mach.program := fun p =>
  transform_partial_program transf_fundef p.

(* correctness *)
(*
Inductive match_states: Linear.state -> Mach.state -> Prop :=
  | match_states_intro:
      forall cs f sp c ls m cs' fb sp' rs m' j tf
        (STACKS: match_stacks j cs cs' f.(Linear.fn_sig))
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_locs f ls (parent_locset cs))
        (INJSP: j sp = Some(sp', fe_stack_data (make_env (function_bounds f))))
        (TAIL: is_tail c (Linear.fn_code f))
        (SEP: m' |= frame_contents f j sp' ls (parent_locset cs) (parent_sp cs') (parent_ra cs')
                 ** stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states (Linear.State cs f (Vptr sp Ptrofs.zero) c ls m)
                   (Mach.State cs' fb (Vptr sp' Ptrofs.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall cs f ls m cs' fb rs m' j tf
        (STACKS: match_stacks j cs cs' (Linear.funsig f))
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (AGREGS: agree_regs j ls rs)
        (SEP: m' |= stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states (Linear.Callstate cs f ls m)
                   (Mach.Callstate cs' fb rs m')
  | match_states_return:
      forall cs ls m cs' rs m' j sg
        (STACKS: match_stacks j cs cs' sg)
        (AGREGS: agree_regs j ls rs)
        (SEP: m' |= stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states (Linear.Returnstate cs ls m)
                  (Mach.Returnstate cs' rs m').

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall (WTS: wt_state s1) s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog st1 ->
  exists st2, Mach.initial_state tprog st2 /\ match_states st1 st2.
Proof.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Linear.final_state st1 r -> Mach.final_state st2 r.
Proof.
*)

FEnd Stacking.

(* Mach -> Asm *)
Family Asmgen.

FDefinition ireg_of : mreg -> res ireg := fun r =>
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

FDefinition freg_of : mreg -> res freg := fun r =>
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

MetaData immed32.
Inductive immed32 : Type :=
  | Imm32_single (imm: int)
  | Imm32_pair   (hi: int) (lo: int).
FEnd immed32.

FDefinition make_immed32 := fun (val: int) =>
  let lo := Int.sign_ext 12 val in
  if Int.eq val lo
  then self__Asmgen.Imm32_single val
  else self__Asmgen.Imm32_pair (Int.shru (Int.sub val lo) (Int.repr 12)) lo.

FDefinition load_hilo32 := fun (r: ireg) (hi lo: int) k =>
  if Int.eq lo Int.zero then Asm.Pluiw r hi :: k
  else Asm.Pluiw r hi :: Asm.Paddiw r r lo :: k.

FDefinition loadimm32 := fun (r: ireg) (n: int) (k: Asm.code) =>
  match make_immed32 n with
  | self__Asmgen.Imm32_single imm => Asm.Paddiw r X0 imm :: k
  | self__Asmgen.Imm32_pair hi lo => load_hilo32 r hi lo k
  end.

MetaData immed64.
Inductive immed64 : Type :=
  | Imm64_single (imm: int64)
  | Imm64_pair   (hi: int64) (lo: int64)
  | Imm64_large  (imm: int64).
FEnd immed64.

FDefinition make_immed64 := fun (val: int64) =>
  let lo := Int64.sign_ext 12 val in
  if Int64.eq val lo then self__Asmgen.Imm64_single lo else
  let hi := Int64.zero_ext 20 (Int64.shru (Int64.sub val lo) (Int64.repr 12)) in
  if Int64.eq val (Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo)
  then self__Asmgen.Imm64_pair hi lo
  else self__Asmgen.Imm64_large val.

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

FRecursion transl_cond_op about Asm.condition motive (fun (_ : Asm.condition) => ireg -> list mreg -> Asm.code -> res Asm.code) by _rect.
Case Ccomp c := 
(fun rd args k => 
  match args with 
  | a1 :: a2 :: nil => 
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int32s c rd r1 r2 k)
  | _ =>  Error(msg "Asmgen.transl_cond_op")
  end).
Case Ccompimm c n :=
(fun rd args k => 
  match args with 
  | a1 :: a2 :: nil => 
       do r1 <- ireg_of a1;
      OK (transl_condimm_int32s c rd r1 n k)
  | _ =>  Error(msg "Asmgen.transl_cond_op")
  end).
FEnd transl_cond_op.

From NFPOP Require Import Prelude.

FRecursion transl_op about Asm.operation motive (fun (_ : Asm.operation) => list mreg -> mreg -> Asm.code -> res Asm.code) by _rect.
Case Omove :=
(fun args res k =>
  match args with 
  | a1 :: nil =>
      match preg_of res, preg_of a1 with
      | IR r, IR a => OK (Asm.Pmv r a :: k)
      | FR r, FR a => OK (Asm.Pfmv r a :: k)
      |  _  ,  _   => Error(msg "Asmgen.Omove")
      end
  | _ =>  Error(msg "Asmgen.transl_op")
  end).
Case Ointconst n := 
(fun args res k => 
  match args with
  | nil => do rd <- ireg_of res; OK (loadimm32 rd n k)
  | _ => Error(msg "Asmgen.transl_op")
  end).
Case Olongconst n := 
(fun args res k => 
  match args with
  | nil => do rd <- ireg_of res; OK (loadimm64 rd n k)
  | _ => Error(msg "Asmgen.transl_op")
  end).
Case Ofloatconst f := 
(fun args res k => 
  match args with
  | nil => 
      do rd <- freg_of res;
      OK (if Float.eq_dec f Float.zero
          then Asm.Pfcvtdw rd X0 :: k
          else cheat Asm.Ploadfi rd f :: k)
  | _ => Error(msg "Asmgen.transl_op")
  end).
Case Osingleconst f := 
(fun args res k => 
  match args with
  | nil => 
       do rd <- freg_of res;
      OK (if Float32.eq_dec f Float32.zero
          then Asm.Pfcvtsw rd X0 :: k
          else Asm.Ploadsi rd f :: k)
  | _ => Error(msg "Asmgen.transl_op")
  end).
Case Oaddrstack n := 
(fun args res k => 
  match args with
  | nil =>  do rd <- ireg_of res; OK (addptrofs rd SP n k)
  | _ => Error(msg "Asmgen.transl_op")
  end).
Case Ocmp cmp := (fun args res k => do rd <- ireg_of res; transl_cond_op cmp rd args k).

FEnd transl_op.

FDefinition transl_cbranch_int32s := fun (cmp: comparison) (r1 r2: ireg0) (lbl: Asm.label) =>
  match cmp with
  | Ceq => Asm.Pbeqw r1 r2 lbl
  | Cne => Asm.Pbnew r1 r2 lbl
  | Clt => Asm.Pbltw r1 r2 lbl
  | Cle => Asm.Pbgew r2 r1 lbl
  | Cgt => Asm.Pbltw r2 r1 lbl
  | Cge => Asm.Pbgew r1 r2 lbl
  end.

FRecursion transl_cbranch about Asm.condition motive (fun (_ : Asm.condition) => list mreg -> Asm.label -> Asm.code -> res Asm.code) by _rect.
Case Ccomp c := 
(fun args lbl k => 
  match args with
  | a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cbranch_int32s c r1 r2 lbl :: k)
  | _ =>  Error(msg "Asmgen.transl_cond_branch")
  end).
Case Ccompimm c n := 
(fun args lbl k => 
  match args with
  | a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq n Int.zero then
            transl_cbranch_int32s c r1 X0 lbl :: k
          else
            loadimm32 X31 n (transl_cbranch_int32s c r1 X31 lbl :: k))
  | _ => Error(msg "Asmgen.transl_cond_branch")
  end).
FEnd transl_cbranch.

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

FDefinition make_epilogue := fun (f: Mach.function) (k: Asm.code) =>
  loadind_ptr SP (Mach.fn_retaddr_ofs f) RA
    (cheat Asm.Pfreeframe (Mach.fn_stacksize f) (Mach.fn_link_ofs f) :: k).

FRecursion transl_instr about Mach.instruction motive (fun (_ : Mach.instruction) => Mach.function -> bool -> Asm.code -> res Asm.code) by _rect.
Case Lgetstack ofs ty dst := (fun f ep k => loadind SP ofs ty dst k).
Case Lsetstack src ofs ty := (fun f ep k =>  storeind src SP ofs ty k).
Case Lgetparam ofs ty dst := 
(fun f ep k => 
    do c <- loadind X30 ofs ty dst k;
      OK (if ep then c
                else loadind_ptr SP (Mach.fn_link_ofs f) X30 c)).
Case Lop op args res := (fun f ep k =>  transl_op op args res k).
Case Llabel lbl := (fun f ep k =>  OK (Asm.Plabel lbl :: k)).
Case Lgoto lbl := (fun f ep k => OK (Asm.Pj_l lbl :: k)).
Case Lcond cond args lbl := (fun f ep k => transl_cbranch cond args lbl k).
Case Lreturn := (fun f ep k => OK (make_epilogue f (Asm.Pj_r RA (Mach.fn_sig f) :: k))).
FEnd transl_instr.

FRecursion it1_is_parent about Mach.instruction motive (fun (_ : Mach.instruction) => bool -> bool) by _rect.
Case Lgetstack ofs ty dst := (fun before => false).
Case Lsetstack src ofs ty := (fun before => before).
Case Lgetparam ofs ty dst := (fun before => negb (mreg_eq dst R30)).
Case Lop op args res := (fun before => before && negb (mreg_eq res R30)).
Case Llabel lbl := (fun before => false).
Case Lgoto lbl := (fun before => false).
Case Lcond cond args lbl := (fun before => false).
Case Lreturn := (fun before => false).
FEnd it1_is_parent.
      
(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)
(*MetaData transl_code.
Fixpoint transl_code (f: self__Base.Mach.function) (il: list self__Base.Mach.instruction) (it1p: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (self__Asmgen.it1_is_parent i1 it1p);
      self__Asmgen.transl_instr i1 f it1p k
  end.
FEnd transl_code.*)

(** This is an equivalent definition in continuation-passing style
  that runs in constant stack space. *)      
MetaData transl_code_rec.
Fixpoint transl_code_rec (f: self__Base.Mach.function) (il: list self__Base.Mach.instruction)
                         (it1p: bool) (k: self__Base.Asm.code -> res self__Base.Asm.code) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_code_rec f il' (self__Asmgen.it1_is_parent i1 it1p)
        (fun c1 => do c2 <- self__Asmgen.transl_instr i1 f it1p c1; k c2)
  end.      
FEnd transl_code_rec.

FDefinition transl_code' := 
  fun (f: Mach.function) (il: list Mach.instruction) (it1p: bool) =>
  transl_code_rec f il it1p (fun c => OK c).

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

FDefinition transl_function := fun (f: Mach.function) =>
  do c <- transl_code' f (Mach.fn_code f) true;
  OK (Asm.mkfunction (Mach.fn_sig f)
        (cheat Asm.Pallocframe (Mach.fn_stacksize f) (Mach.fn_link_ofs f) ::
         storeind_ptr RA SP (Mach.fn_retaddr_ofs f) (cheat Asm.Pcfi_rel_offset (Ptrofs.to_int (Mach.fn_retaddr_ofs f)):: c))).

FDefinition transf_function : Mach.function -> res Asm.function := fun f =>
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z (Asm.fn_code tf))
  then Error (msg "code size exceeded")
  else OK tf.

FDefinition transf_fundef : Mach.fundef -> res Asm.fundef := fun f =>
  transf_partial_fundef transf_function f.

FDefinition transf_program : Mach.program -> res Asm.program := fun p =>
  transform_partial_program transf_fundef p.
      
(* correctness *)

(* 
Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#X30 = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').
*)

FEnd Asmgen.

FEnd Base.

(* small extension *)
Trait Comp_Switch extends Comp_Base. 
FEnd Comp_Switch.

(* small extension *)
Trait Comp_Loop extends Comp_Base.
FEnd Comp_Loop.

(* requires work with cshmgen, selection, operation semantics *)
Trait Comp_Op extends Comp_Base.
FEnd Comp_op.

(* small extension *)
Trait Comp_Heap extends Comp_Base.
FEnd Comp_Heap.

(* small extension: Only C, Clight *)
(* Struct/Union *)
Trait Comp_Field extends Comp_Base.
FEnd Comp_Field.

(* small extension *)
Trait Comp_Call extends Comp_Base.
FEnd Comp_Call.

(* small *)
Trait Comp_External extends Comp_Base.
FEnd Comp_External.

(* small *)
Trait Comp_Builtin extends Comp_Base.
FEnd Comp_Builtin.

(* ?? *)
Trait Comp_Vector extends Comp_Base.
FEnd Comp_Vector.

Family Comp extends 
  Comp_Switch, 
  Comp_Loop, 
  Comp_Op, 
  Comp_Heap, 
  Comp_Field, 
  Comp_Call, 
  Comp_External, 
  Comp_Builtin. 
FEnd Comp.


Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
