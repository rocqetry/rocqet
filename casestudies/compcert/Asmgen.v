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
From NFPOP Require Import Op.

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
| Pnop : instruction. (**r nop instruction *)
                       
FDefinition code := list instruction.
MetaData function.
Record function : Type := mkfunction { fn_sig: signature; fn_code: self__Common.code }.
FEnd function.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

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

FEnd D.

(* Standard extension for vector operations *)
Family V.
FEnd V.

FEnd RV.

Trait Base.

(* C family languages: Csharpminor, Cminor, CminorSel *)

(* RISC-V *)
Family Asm extends RV.RV64I, RV.M, RV.D.
FEnd Asm.

From NFPOP Require Import Registers.      

From NFPOP Require Import Machregs.

From NFPOP Require Import Conventions1.
From NFPOP Require Import Locations.

Family Lfam.
FDefinition label := positive.

FInductive instruction: Type :=
| Lop : Op.operation -> list mreg -> mreg -> instruction
| Lcond : Op.condition -> list mreg -> label -> instruction
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

FEnd Lfam.

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

FEnd Mach.  

(* Mach -> Asm *)
Family Asmgen.
Family S extends Mach. FEnd S.

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

(*FRecursion transl_cond_op about Op.condition motive (fun (_ : Op.condition) => ireg -> list mreg -> Asm.code -> res Asm.code) by _rect.
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
Case Ccompuimm c n :=
(fun rd args k => 
  match args with 
  | a1 :: a2 :: nil => 
      do r1 <- ireg_of a1;
      OK (transl_condimm_int32u c rd r1 n k)
  | _ =>  Error(msg "Asmgen.transl_cond_op")
  end).
FEnd transl_cond_op. *)

From NFPOP Require Import Prelude.

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

(*FRecursion transl_op about Op.operation motive (fun (_ : Op.operation) => list mreg -> mreg -> Asm.code -> res Asm.code) by _rect.
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
(* [Omakelong], [Ohighlong]  should not occur *)
Case Omakelong := (fun args res k =>  Error(msg "Asmgen.transl_op")).
FEnd transl_op.*)

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

(*FRecursion transl_cbranch about Op.condition motive (fun (_ : Op.condition) => list mreg -> Asm.label -> Asm.code -> res Asm.code) by _rect.
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
Case Ccompuimm c n :=
(fun args lbl k => 
  match args with
  | a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq n Int.zero then
            transl_cbranch_int32u c r1 X0 lbl :: k
          else
            loadimm32 X31 n (transl_cbranch_int32u c r1 X31 lbl :: k))
  | _ => Error(msg "Asmgen.transl_cond_branch")
  end).  
FEnd transl_cbranch.*)

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
FEnd it1_is_parent.
      
(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)
(*MetaData transl_code.
Fixpoint transl_code (f: self__Base.S.function) (il: list self__Base.S.instruction) (it1p: bool) :=
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
Fixpoint transl_code_rec (f: self__Asmgen.S.function) (il: list self__Asmgen.S.instruction)
                         (it1p: bool) (k: self__Base.Asm.code -> res self__Base.Asm.code) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_code_rec f il' (self__Asmgen.it1_is_parent i1 it1p)
        (fun c1 => do c2 <- self__Asmgen.transl_instr i1 f it1p c1; k c2)
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
         storeind_ptr RA SP (S.fn_retaddr_ofs f) (cheat Asm.Pcfi_rel_offset (Ptrofs.to_int (S.fn_retaddr_ofs f)):: c))).

FDefinition transf_function : S.function -> res Asm.function := fun f =>
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z (Asm.fn_code tf))
  then Error (msg "code size exceeded")
  else OK tf.

FDefinition transf_fundef : S.fundef -> res Asm.fundef := fun f =>
  transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res Asm.program := fun p =>
  transform_partial_program transf_fundef p.     

FEnd Asmgen.

FEnd Base.

Trait Comp_Loops extends Base.

Family Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.
FEnd Lfam.

Trait Asmgen_jumptable extends Asmgen.
FRecursion transl_instr.
From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.
Case Ljumptable arg tbl :=
(fun f ep k =>
   do r <- ireg_of arg;
   OK (Asm.Pbtbl r tbl :: k)).
FEnd transl_instr.

FRecursion it1_is_parent.
Case _ := (fun before => false).
FEnd it1_is_parent.

FEnd Asmgen_jumptable.

Family Asmgen extends Asmgen_jumptable.
FEnd Asmgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.
FEnd Lfam.

Family Mach extends Lfam. FEnd Mach.

Family Asmgen.
Family S extends Mach. FEnd S.

Inherit indexed_memory_access.

From NFPOP Require Import Errors.
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

FEnd Asmgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.
FEnd Lfam.

Family Linear extends Lfam. FEnd Linear.

Family Asmgen.
Family S extends Mach. FEnd S.
From NFPOP Require Import Errors.
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

FEnd Asmgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

FEnd Comp_Switch.

Family Comp extends
  Comp_Heap,             
  Base,
  Comp_Switch,
  Comp_Loops,  
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin. 

Family Asmgen.
Final Family S := Mach.
FEnd Asmgen.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
