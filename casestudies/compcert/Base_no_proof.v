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

FEnd Clight.

(* C -> Clight *)
Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

Local Open Scope gensym_monad_scope.

MetaData makeseq_rec.
Fixpoint makeseq_rec (s: self__SimplExpr.T.stmt) (l: list self__SimplExpr.T.stmt) : self__SimplExpr.T.stmt :=
   match l with
   | nil => s
   | s' :: l' => makeseq_rec (self__SimplExpr.T.Sseq s s') l'
    end.
FEnd makeseq_rec.
      
FDefinition makeseq : list self__SimplExpr.T.stmt -> self__SimplExpr.T.stmt := fun l => 
  makeseq_rec self__SimplExpr.T.Sskip l.

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
Fixpoint do_set (sd: self__SimplExpr.set_destination) (a: self__SimplExpr.T.expr) : list self__SimplExpr.T.stmt :=
    match sd with
    | self__SimplExpr.SDbase tycast ty tmp => self__SimplExpr.T.Sset tmp (self__SimplExpr.T.Ecast a tycast) :: nil
    | self__SimplExpr.SDcons tycast ty tmp sd' => self__SimplExpr.T.Sset tmp (self__SimplExpr.T.Ecast a tycast) :: do_set sd' (self__SimplExpr.T.Etempvar tmp ty)
    end.
FEnd do_set.

FDefinition finish := fun (dst: destination) (sl: list T.stmt) (a: T.expr) => 
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
    
FDefinition dummy_expr := T.Econst_int Int.zero type_int32s.
      
FRecursion eval_simpl_expr about T.expr motive (fun (_ : T.expr) => option val) by _rect.          
Case Econst_float n ty := (Some(Vfloat n)).
Case Econst_int n ty := (Some(Vint n)).
Case Econst_single n ty := (Some(Vsingle n)).
Case Econst_long n ty := (Some(Vlong n)).
Case Ecast b ty := 
  (match eval_simpl_expr b with
    | None => None
    | Some v => Cop.sem_cast v (T.typeof b) ty Mem.empty
    end).
Case Etempvar id ty := None.
Case Esizeof ty' ty := None.
Case Ealignof ty' ty := None.
FEnd eval_simpl_expr.

FDefinition makeif : T.expr -> T.stmt -> T.stmt -> T.stmt :=
  fun a s1 s2 =>
    match eval_simpl_expr a with
    | Some v =>
        match Cop.bool_val v (T.typeof a) Mem.empty with
        | Some b => if b then s1 else s2
        | None => T.Sifthenelse a s1 s2
        end
    | None => T.Sifthenelse a s1 s2
    end.
      
FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => destination -> mon (list T.stmt * T.expr)) by _rect.
Case Evar id ty := (fun dst => ret (finish dst nil (T.Etempvar id ty))).
Case Eval v ty := 
  (fun dst => 
    match v with 
    | Vint n => ret (finish dst nil (T.Econst_int n ty)) 
    | Vlong n =>  ret (finish dst nil (T.Econst_long n ty))
    | Vfloat n => ret (finish dst nil (T.Econst_float n ty))
    | Vsingle n => ret (finish dst nil (T.Econst_single n ty))
    | _ => error (msg "SimplExpr.transl_expr: Eval") end).
Case Ecast r1 ty :=
  (fun dst => 
      match dst with
      | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
          do (sl1, a1) <- transl_expr r1 self__SimplExpr.For_val;
          ret (finish dst sl1 (T.Ecast a1 ty))
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
               T.Etempvar t ty)
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
               makeif a1 (T.Sset t (T.Econst_int Int.one ty)) (makeseq sl2) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq (do_set sd (T.Econst_int Int.one ty))) (makeseq sl2) :: nil,
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
               makeif a1 (makeseq sl2) (T.Sset t (T.Econst_int Int.zero ty)) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (T.Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      end).                          
Case Esizeof ty' ty := (fun dst => ret (finish dst nil (T.Esizeof ty' ty))).
Case Ealignof ty' ty := (fun dst => ret (finish dst nil (T.Ealignof ty' ty))).
Case Eparen e tycast ty := (fun dst => error (msg "SimplExpr.transl_expr: paren")).
FEnd transl_expr.

FDefinition transl_expression : S.expr -> mon (T.stmt * T.expr) := fun r =>
  do (sl, a) <- transl_expr r self__SimplExpr.For_val; ret (makeseq sl, a).

FDefinition transl_expr_stmt : S.expr -> mon T.stmt := fun r =>
  do (sl, a) <- transl_expr r self__SimplExpr.For_effects; ret (makeseq sl).

FDefinition transl_if : S.expr -> T.stmt -> T.stmt -> mon T.stmt  := fun r s1 s2 => 
  do (sl, a) <- transl_expr r self__SimplExpr.For_val;
  ret (makeseq (sl ++ makeif a s1 s2 :: nil)).

Closing Fact is_Sskip:
  forall s, {s = S.Sskip} + {s <> S.Sskip} by {  destruct s; ((left; reflexivity) || (right; congruence)) }.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => mon T.stmt) by _rect.
Case Sskip := (ret T.Sskip).
Case Sdo e := (transl_expr_stmt e).
Case Sseq s1 s2 := 
  (do ts1 <- transl_stmt s1;
   do ts2 <- transl_stmt s2;
   ret (T.Sseq ts1 ts2)). 
Case Sifthenelse e s1 s2 := 
  (do ts1 <- transl_stmt s1;
   do ts2 <- transl_stmt s2;
   do (s', a) <- transl_expression e;
    if is_Sskip s1 && is_Sskip s2 then
      ret (T.Sseq s' T.Sskip)
    else
      ret (T.Sseq s' (T.Sifthenelse a ts1 ts2))).
Case Sreturn e := 
  (match e with
    | None => ret (T.Sreturn None)
    | Some e =>
        do (s', a) <- transl_expression e;
        ret (T.Sseq s' (T.Sreturn (Some a)))
    end).
Case Slabel lbl s1 := 
  (do ts1 <- transl_stmt s1;
    ret (T.Slabel lbl ts1)).
Case Sgoto lbl := (ret (T.Sgoto lbl)).
FEnd transl_stmt.

FDefinition transl_function : S.function -> res T.function := fun f => 
  match transl_stmt (S.fn_body f) (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody g i =>
      OK (T.mkfunction
              (S.fn_return f)
              (S.fn_callconv f)
              (S.fn_params f)
              (S.fn_vars f)
              g.(gen_trail)
              tbody)
  end.

Local Open Scope error_monad_scope.

FDefinition transl_fundef : composite_env -> S.fundef -> res T.fundef := fun _ fd =>
    match fd with
    | Internal f =>
        do tf <- transl_function f; OK (Internal tf)
    | External ef targs tres cc =>
      OK (External ef targs tres cc)           
    end.
     
FDefinition transl_program : S.program -> res T.program := fun p =>     
  do p1 <- AST.transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
          
FEnd SimplExpr.

(* C family languages: Csharpminor, Cminor, CminorSel *)
Family Cfam.

FInductive expr : Type :=
| Evar : ident -> expr. (* reading a temporary variable *)            

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
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

FEnd Cfam.

(* constants *)
Family Constant.
FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant.
FEnd Constant.

Family Csharpminor extends Cfam.

FInductive expr : Type := Econst : Constant.constant -> expr. (* constants *)
       
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

FEnd Csharpminor.


(* Clight -> Csharpminor *)
Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

FDefinition make_intconst := fun (n: int) => T.Econst (Constant.Ointconst n).
FDefinition make_longconst := fun (f: int64) => T.Econst (Constant.Olongconst f).
FDefinition make_floatconst := fun (f: float) => T.Econst (Constant.Ofloatconst f).
FDefinition make_singleconst := fun (f: float32) => T.Econst (Constant.Osingleconst f).
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
FOpaque Definition make_cast : type -> type -> T.expr -> res T.expr :=
  fun _ _ e => OK e.
FOpaque Definition make_boolean : T.expr -> type -> T.expr :=
  fun e _ => e.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => composite_env -> res T.expr) by _rect.
Case Econst_int n ty := (fun ce => OK(make_intconst n)). 
Case Econst_float n ty := (fun ce => OK(make_floatconst n)).
Case Econst_single n ty := (fun ce => OK(make_singleconst n)).
Case Econst_long n ty := (fun ce => OK(make_longconst n)).
Case Etempvar id ty := (fun ce => OK(T.Evar id)). 
Case Esizeof ty' ty := (fun ce => do sz <- sizeof ce ty'; OK(make_ptrofsconst sz)).
Case Ealignof ty' ty := (fun ce => do al <- alignof ce ty'; OK(make_ptrofsconst al)).
Case Ecast b ty := (fun ce => do tb <- transl_expr b ce; make_cast (S.typeof b) ty tb).
FEnd transl_expr.
      
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => composite_env -> type -> nat -> nat -> res T.stmt) by _rect.
Case Sskip := (fun ce tyret nbrk ncnt => OK T.Sskip).   
Case Sset x b :=
(fun ce tyret nbrk ncnt => 
  do tb <- transl_expr b ce;
  OK (T.Sassign x tb)).
Case Sseq s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (T.Sseq ts1 ts2)).
Case Sifthenelse e s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do te <- transl_expr e ce;
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (T.Sifthenelse (make_boolean te (S.typeof e)) ts1 ts2)).
Case Sreturn e :=
(fun ce tyret nbrk ncnt =>
   match e with
   | None => OK (T.Sreturn None)
   | Some e => 
       do te <- transl_expr e ce;
       do te' <- make_cast (S.typeof e) tyret te;
       OK (T.Sreturn (Some te'))
   end).
Case Slabel lbl s :=
(fun ce tyret nbrk ncnt => 
  do ts <- transl_stmt s ce tyret nbrk ncnt;
  OK (T.Slabel lbl ts)).
Case Sgoto lbl := (fun ce tyret nbrk ncnt => OK (T.Sgoto lbl)).
FEnd transl_stmt.

(* Translation of functions *)
FDefinition transl_var := fun (ce: composite_env) (v: ident * type) =>
  do sz <- sizeof ce (snd v); OK (fst v, sz).
      
FDefinition signature_of_function := fun (f: S.function) =>
  {| sig_args := map typ_of_type (map snd (S.fn_params f));
    sig_res  := rettype_of_type (S.fn_return f);
    sig_cc   := S.fn_callconv f |}.
      
FDefinition transl_function : composite_env -> S.function -> res T.function :=
  fun (ce: composite_env) (f: S.function)  =>
  do tbody <- transl_stmt (S.fn_body f) ce (S.fn_return f) 1%nat 0%nat;
  do tvars <- mmap (transl_var ce) (S.fn_vars f);
  OK (T.mkfunction
        (signature_of_function f)
        (map fst (S.fn_params f))
        tvars
        (map fst (S.fn_temps f))
        tbody).      

FDefinition transl_fundef : composite_env -> ident -> S.fundef -> res T.fundef :=
  fun (ce: composite_env) (id: ident) (f: S.fundef) =>
  match f with
  | Internal g =>
      do tg <- transl_function ce g; OK(AST.Internal tg)
  | External ef args res cconv =>
      if signature_eq (ef_sig ef) (signature_of_type args res cconv)
      then OK(AST.External ef)
      else Error(msg "Cshmgen.transl_fundef: wrong external signature")
  end.

FDefinition transl_globvar := fun (id: ident) (ty: type) => OK tt.

FDefinition transl_program : S.program -> res T.program := fun p => 
  transform_partial_program2 (transl_fundef p.(prog_comp_env)) transl_globvar p.

FEnd Cshmgen.

Family Cminor extends Cfam.

FInductive expr : Type := Econst : Constant.constant -> expr.        
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

FEnd Cminor.

Family Op.

(* Operations *)
FInductive condition : Type :=
| Ccomp : comparison -> condition       (**r signed integer comparison *)
| Ccompimm : comparison -> int -> condition (**r signed integer comparison with a constant *)
| Ccompuimm : comparison -> int -> condition. (**r unsigned integer comparison with a constant *)

FInductive operation : Type :=
| Omove : operation                    (**r [rd = r1] *)
| Ointconst : int -> operation       (**r [rd] is set to the given integer constant *)
| Olongconst : int64 -> operation    (**r [rd] is set to the given integer constant *)
| Ofloatconst : float -> operation   (**r [rd] is set to the given float constant *)
| Osingleconst : float32 -> operation (**r [rd] is set to the given float constant *)
| Oaddrstack : ptrofs -> operation (**r [rd] is set to the stack pointer plus the given offset *)
| Omakelong : operation                (**r [rd = r1 << 32 | r2] *)                             
| Ocmp : condition -> operation.  (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

FRecursion negate_condition about condition motive (fun (_ : condition) => condition) by _rect.
Case Ccomp c := (Ccomp(negate_comparison c)).
Case Ccompimm c n := (Ccompimm (negate_comparison c) n).
Case Ccompuimm c n := (Ccompuimm (negate_comparison c) n).
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
Case Ccompuimm c n :=
(fun vl m =>
   match vl with 
   | v1 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n)
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
Case Omakelong := (fun delta => Omakelong).
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
Case Omakelong :=
(fun F V ge sp vl m =>
    match vl with 
    | v1 :: v2 :: nil =>  Some (Val.longofwords v1 v2)
    | _ => None end).  
FEnd eval_operation.

FEnd Op.

(* RISC-V *)
Family Asm extends RV.RV64I, RV.D.    
FEnd Asm.

Family CminorSel extends Cfam.
FInductive expr : Type :=
| Econdition : condexpr -> expr -> expr -> expr
| Eop : Op.operation -> exprlist -> expr
| Elet : expr -> expr -> expr
| Eletvar : nat -> expr
with exprlist : Type :=
| Enil: exprlist
| Econs: expr -> exprlist -> exprlist
with condexpr : Type :=
| CEcond : Op.condition -> exprlist -> condexpr
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

FEnd CminorSel.


(* A translation between C family languages *)
Family Cfamtransl.
Family S extends Cfam. FEnd S.
Family T extends Cfam. FEnd T.
   
FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => res T.expr) by _rect.
Case Evar id := (OK (T.Evar id)).
FEnd transl_expr.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => res T.stmt) by _rect.
Case Sskip := (OK (T.Sskip)).
Case Sassign id e := ( do te <- transl_expr e; OK (T.Sassign id te)).
Case Sseq s1 s2 :=
(do ts1 <- transl_stmt_s1; 
do ts2 <- transl_stmt_s2; 
OK (T.Sseq ts1 ts2)).
Case Sreturn e := 
(match e with
 | None => OK (T.Sreturn None)
 | Some e =>
      do te <- transl_expr e;
      OK (T.Sreturn (Some te))
 end).
Case Slabel lbl s := (do ts <- transl_stmt s; OK (T.Slabel lbl ts)).
Case Sgoto lbl := (OK (T.Sgoto lbl)).
FEnd transl_stmt.
      
FOpaque Definition transl_function : S.function -> res T.function :=
  cheat.

FDefinition transl_fundef : S.fundef -> res T.fundef := fun f =>
   transf_partial_fundef transl_function f.

FDefinition transl_program : S.program -> res T.program := fun p =>
  transform_partial_program transl_fundef p.

FEnd Cfamtransl.

(* Csharpminor -> Cminor *)
Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T. 

FDefinition compilenv := PTree.t Z.

FRecursion transl_expr.
Case Econst c := cheat. (* (OK (T.Econst c)).*)
FEnd transl_expr.
    
FRecursion transl_stmt. 
Case Sifthenelse e s1 s2 :=
 (do te <- transl_expr e;
  do ts1 <- transl_stmt s1;
  do ts2 <- transl_stmt s2;
  OK (T.Sifthenelse te ts1 ts2)).
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
fun (cenv: compilenv) (stacksize: Z) (f: S.function) =>
  do tbody <- transl_stmt (S.fn_body f) (* cenv*) (* nil*) ;
  OK (T.mkfunction
        (S.fn_sig f)
        (S.fn_params f)
        (S.fn_temps f)
        stacksize
        tbody).

(*equality thingy *)
FOverride Definition transl_function := fun (f: S.function) => cheat.
  (*let (cenv, stacksize) := build_compilenv f in
  if zle stacksize Ptrofs.max_unsigned
  then transl_funbody cenv stacksize f
  else Error(msg "Cminorgen: too many local variables, stack size exceeded"). *)

FEnd Cminorgen.

(* Cminor -> CminorSel *)
Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

Family SplitLong.

FDefinition makelong : T.expr -> T.expr -> T.expr := fun h l => 
  T.Eop Op.Omakelong (T.Econs h (T.Econs l T.Enil)).

FDefinition longconst : int64 -> T.expr := fun n =>
  makelong (T.Eop (Op.Ointconst (Int64.hiword n)) T.Enil)
           (T.Eop (Op.Ointconst (Int64.loword n)) T.Enil).
FEnd SplitLong.

FDefinition longconst : int64 -> T.expr := fun n =>
  if Archi.splitlong then SplitLong.longconst n else T.Eop (Op.Olongconst n) T.Enil.

FRecursion sel_constant about Constant.constant motive (fun (_ : Constant.constant) => T.expr) by _rect.
Case Ointconst n := (T.Eop (Op.Ointconst n) T.Enil).
Case Ofloatconst f := (T.Eop (Op.Ofloatconst f) T.Enil).
Case Osingleconst f := (T.Eop (Op.Osingleconst f) T.Enil).
Case Olongconst n := (longconst n).
FEnd sel_constant.

FRecursion transl_expr.
Case Econst cst := (OK (sel_constant cst)).
FEnd transl_expr.
       
FRecursion condexpr_of_expr_eop about
  Op.operation motive (fun (_ : Op.operation) => T.expr -> T.exprlist -> T.condexpr) by _rect.
Case Ocmp c := (fun _ args => T.CEcond c args).
Case _ := (fun e _ => T.CEcond (Op.Ccompuimm Cne Int.zero) (T.Econs e T.Enil)).
FEnd condexpr_of_expr_eop.
       
FRecursion condexpr_of_expr about T.expr motive (fun (_ : T.expr) => T.condexpr) by _rect.
Case Eop op args := (condexpr_of_expr_eop op (T.Eop op args) args).
Case Econdition a b c := (T.CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)).
Case Elet a b := (T.CElet a (condexpr_of_expr b)).
Case Eletvar n := (T.CEcond (Op.Ccompuimm Cne Int.zero) (T.Econs (T.Eletvar n) T.Enil)).
Case Evar i := (T.CEcond (Op.Ccompuimm Cne Int.zero) (T.Econs (T.Evar i) T.Enil)). 
FEnd condexpr_of_expr.
       
FRecursion transl_stmt.                            
Case Sifthenelse e ifso ifnot := (
   (* For simplicity, don't use the
      "if conversion heuristics" present in CompCert *)                      
     do ifso' <- transl_stmt ifso ;
     do ifnot' <- transl_stmt ifnot ;
     do te <- transl_expr e; 
     OK (T.Sifthenelse (condexpr_of_expr te) ifso' ifnot')).
FEnd transl_stmt.

FOverride Definition transl_function := fun f =>             
   do body' <- transl_stmt (S.fn_body f);
   OK (T.mkfunction
         (S.fn_sig f)
         (S.fn_params f)
         (S.fn_vars f)
         (S.fn_stackspace f)
         body').

FEnd Selection.

Family RTL.
FDefinition node := positive.

From NFPOP Require Import Registers.
      
FInductive instruction: Type :=
| Inop: node -> instruction
| Iop: Op.operation -> list reg -> reg -> node -> instruction          
| Icond: Op.condition -> list reg -> node -> node -> instruction
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

FEnd RTL.

From NFPOP Require Import RTLmonad.

(* CminorSel -> RTL *)
Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FDefinition res := fun (A : Type) => res A T.instruction.
FDefinition mon := fun (A : Type) => mon A T.instruction.
FDefinition state := state T.instruction.

FLemma init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty T.instruction)!pc = None.
FProofLemma. intros; right; apply PTree.gempty. Qed. CloseFLemma.

FDefinition init_state : state :=
  mkstate T.instruction 1%positive 1%positive (PTree.empty T.instruction) init_state_wf.

FLemma add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode T.instruction) in
  Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code T.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_instr_incr:
  forall s i,
  let n := s.(st_nextnode T.instruction) in
  state_incr T.instruction s (mkstate T.instruction s.(st_nextreg T.instruction)
                (Pos.succ n)
                (PTree.set n i s.(st_code T.instruction))
                (add_instr_wf s i)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition add_instr : T.instruction -> mon T.node := fun (i: T.instruction) =>
  fun s =>
    let n := s.(st_nextnode T.instruction) in
    OK n
       (mkstate T.instruction s.(st_nextreg T.instruction) (Pos.succ n) (PTree.set n i s.(st_code T.instruction))
                (add_instr_wf s i))
       (add_instr_incr s i).

FLemma reserve_instr_wf:
  forall s pc,
    Plt pc (Pos.succ s.(st_nextnode T.instruction)) \/ s.(st_code T.instruction)!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode T.instruction) in
  state_incr T.instruction s (mkstate T.instruction s.(st_nextreg T.instruction)
                (Pos.succ n)
                s.(st_code T.instruction)
                    (reserve_instr_wf s)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition reserve_instr : mon T.node :=
  fun (s: state) =>
  let n := s.(st_nextnode T.instruction) in
  OK n
     (mkstate T.instruction s.(st_nextreg T.instruction) (Pos.succ n) s.(st_code T.instruction) (reserve_instr_wf s))
     (reserve_instr_incr s).

FLemma update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode T.instruction) ->
  forall pc,
    Plt pc s.(st_nextnode T.instruction) \/ (PTree.set n i s.(st_code T.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode T.instruction)),
  s.(st_code T.instruction)!n = None ->
  state_incr T.instruction s
             (mkstate T.instruction s.(st_nextreg T.instruction) s.(st_nextnode T.instruction) (PTree.set n i s.(st_code T.instruction))
                     (update_instr_wf s n i LT)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma check_empty_node:
  forall (s: state) (n: T.node), { s.(st_code T.instruction)!n = None } + { True }.
FProofLemma.  intros. case (s.(st_code self__RTLgen.T.instruction)!n); intros. right; auto. left; auto. Qed. CloseFLemma.

FDefinition update_instr : T.node -> T.instruction -> mon unit := fun (n: T.node) (i: T.instruction) => 
  fun s =>
    match plt n s.(st_nextnode T.instruction), check_empty_node s n with
    | left L, left EMPTY =>
        OK tt
           (mkstate T.instruction s.(st_nextreg T.instruction) s.(st_nextnode T.instruction) (PTree.set n i s.(st_code T.instruction))
                    (update_instr_wf s n i L))
           (update_instr_incr s n i L EMPTY)
    | _, _ =>
        Error (Errors.msg "RTLgen.update_instr")
    end.

FLemma new_reg_incr:
  forall s,
  state_incr T.instruction s (mkstate T.instruction (Pos.succ s.(st_nextreg T.instruction))
                        s.(st_nextnode T.instruction) s.(st_code T.instruction) s.(st_wf T.instruction)).
FProofLemma. constructor; simpl. apply Ple_refl. apply Ple_succ. auto. Qed. CloseFLemma.

FDefinition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg T.instruction)
       (mkstate T.instruction (Pos.succ s.(st_nextreg T.instruction)) s.(st_nextnode T.instruction) s.(st_code T.instruction) s.(st_wf T.instruction))
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

FDefinition add_move : reg -> reg -> T.node -> mon T.node := fun (rs rd: reg) (nd: T.node) => 
  if Reg.eq rs rd
  then ret nd
  else add_instr (T.Iop Op.Omove (rs::nil) rd nd).

FRecursion alloc_reg about S.expr motive (fun (_ : S.expr) => mapping -> mon reg) by _rect.
Case Evar id := (fun map => find_var map id).
Case Eletvar n := (fun map => find_letvar map n).
Case Eop := (fun op args => fun map => new_reg).
Case Econdition c a0 a1 := (fun map => new_reg).
Case Elet a b := (fun map => new_reg).
FEnd alloc_reg.

FRecursion alloc_regs about S.exprlist motive (fun (_ : S.exprlist) => mapping -> mon (list reg)) by _rect.
Case Enil := (fun map => ret nil).
Case Econs a bl :=
(fun map =>
  do r <- alloc_reg a map;
  do rl <- alloc_regs bl map;
  ret (r :: rl)).
FEnd alloc_regs.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => mapping -> reg -> T.node -> mon T.node)
  with transl_exprlist about S.exprlist motive (fun (_ : S.exprlist) => mapping -> list reg -> T.node -> mon T.node)
  with transl_condexpr about S.condexpr motive (fun (_ : S.condexpr) => mapping  -> T.node -> T.node -> mon T.node) by _rect.
Case Evar v := (fun map rd nd => do r <- find_var map v; add_move r rd nd).
Case Elet b c :=
(fun map rd nd => 
   do r <- new_reg;
   do nc <- transl_expr c (add_letvar map r) rd nd;
   transl_expr b map r nc).
Case Eop op al :=
(fun map rd nd => 
    do rl <- alloc_regs al map;
    do no <- add_instr (T.Iop op rl rd nd);
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
   do nt <- add_instr (T.Icond c rl ntrue nfalse);
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
        
FDefinition labelmap : Type := PTree.t T.node.
        
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => mapping -> T.node -> list T.node -> labelmap -> T.node -> option reg -> mon T.node) by _rect.
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
        (handle_error (update_instr n (T.Inop ns))
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
FEnd transl_stmt.

FDefinition alloc_label : S.label -> labelmap -> mon labelmap :=
  fun (lbl: S.label) (map: labelmap) =>
  do n <- reserve_instr;
  ret (PTree.set lbl n map).   

FRecursion reserve_labels about S.stmt
  motive (fun (_ : S.stmt) => labelmap -> mon labelmap) by _rect.
Case Sseq s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Sifthenelse e s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Slabel lbl s1 := (fun lm => do lm' <- reserve_labels s1 lm; alloc_label lbl lm').
Case Sskip := (fun lm => ret lm).
Case Sassign i e := (fun lm => ret lm).
Case Sreturn a := (fun lm => ret lm).
Case Sgoto lbl := (fun lm => ret lm).
FEnd reserve_labels.

FDefinition ret_reg : signature -> reg -> option reg :=
  fun (sig: signature) (rd: reg) =>
  if rettype_eq sig.(AST.sig_res) AST.Tvoid then None else Some rd.

FDefinition transl_fun : S.function -> mon (T.node * list reg) :=
  fun (f: S.function) => 
  do ngoto <- reserve_labels (S.fn_body f) (PTree.empty T.node);
  do (rparams, map1) <- add_vars init_mapping (S.fn_params f);
  do (rvars, map2) <- add_vars map1 (S.fn_vars f);
  do rret <- new_reg;
  let orret := ret_reg (S.fn_sig f) rret in
  do nret <- add_instr (T.Ireturn orret);
  do nentry <- transl_stmt (S.fn_body f) map2 nret nil ngoto nret orret;
  ret (nentry, rparams).

FDefinition transl_function : S.function -> Errors.res T.function := 
    fun (f: S.function) => 
  match transl_fun f init_state with
  | Error msg => Errors.Error msg
  | OK (nentry, rparams) s i =>
      Errors.OK (T.mkfunction
                   (S.fn_sig f)
                   rparams
                   (S.fn_stackspace f)
                   s.(st_code T.instruction)
                   nentry)
  end.

FDefinition transl_fundef := transf_partial_fundef transl_function.

FDefinition transl_program : S.program -> Errors.res T.program := 
  fun (p: S.program) =>
     transform_partial_program transl_fundef p.                 
FEnd RTLgen.

From NFPOP Require Import Machregs.

From NFPOP Require Import Conventions1.
From NFPOP Require Import Locations.
(* Some Machreg functions will defined here *)
Family M.
FRecursion destroyed_by_op about Op.operation motive
  (fun (_ : Op.operation) => list mreg) by _rect.
(*Case Omove := nil.
Case Ointconst n := nil.
Case Olongconst n := nil.
Case Ofloatconst f := nil.
Case Osingleconst s := nil.
Case Oaddrstack addr := nil.
Case Ocmp c := nil.*)
Case _ := nil.
FEnd destroyed_by_op.

FDefinition destroyed_by_cond : Op.condition -> list mreg := fun cond => nil. 
FEnd M.


Family LTL.
FDefinition node := positive.

FInductive instruction: Type :=
| Lop : Op.operation -> list mreg -> mreg -> instruction
| Lgetstack : slot -> Z -> typ -> mreg -> instruction
| Lsetstack : mreg -> slot -> Z -> typ -> instruction 
| Lbranch : node -> instruction
| Lcond : Op.condition -> list mreg -> node -> node -> instruction
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

FEnd Mach.

(* LTL -> Linear *)
Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

From NFPOP Require Import Lattice.
From NFPOP Require Import Kildall.

(* Determination of the order of basic blocks *)

Module DS := Dataflow_Solver(LBoolean)(NodeSetForward).

FDefinition reachable_aux : S.function -> option (PMap.t bool) :=
  fun (f: S.function) =>
  DS.fixpoint
    (S.fn_code f) S.successors_block
    (fun pc r => r)
    (S.fn_entrypoint f) true.

FDefinition reachable : S.function -> PMap.t bool := fun f =>
  match reachable_aux f with
  | None => PMap.init true
  | Some rs => rs
  end.

MetaData enumerate_aux.
Parameter enumerate_aux: self__Linearize.S.function -> PMap.t bool -> list self__Linearize.S.node.
FEnd enumerate_aux.

Module Nodeset := FSetAVL.Make(OrderedPositive).

From NFPOP Require Import Errors.
Open Scope error_monad_scope.

MetaData nodeset_of_list.
Fixpoint nodeset_of_list (l: list self__Linearize.S.node) (s: Nodeset.t)
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
     (ok: bool) (pc: S.node) (bb: S.bblock) =>
  if reach!!pc then ok && Nodeset.mem pc s else ok.

FDefinition check_reachable := 
     fun (f: S.function) (reach: PMap.t bool) (s: Nodeset.t) =>
  PTree.fold (check_reachable_aux reach s) (S.fn_code f) true.

FDefinition enumerate : S.function -> res (list S.node) := fun f => 
  let reach := reachable f in
  let enum := enumerate_aux f reach in
  do s <- nodeset_of_list enum Nodeset.empty;
  if check_reachable f reach s
  then OK enum
  else Error (msg "Linearize: wrong enumeration").

FRecursion starts_with_label about T.instruction motive (fun (_ : T.instruction) => T.label -> bool) by _rect.
Case Llabel lbl' := (fun lbl => peq lbl lbl').
Case Lop op args res := (fun lbl => false).
Case Lgetstack sl ofs ty r := (fun lbl => false).
Case Lsetstack r sl ofs ty := (fun lbl => false).
Case Lcond cond args lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false).
Case Lgoto lbl' := (fun lbl => false).
FEnd starts_with_label.

MetaData starts_with.
Fixpoint starts_with (lbl: self__Linearize.T.label) (k: self__Linearize.T.code) {struct k} : bool :=
     match k with
     | i :: k' => if self__Linearize.starts_with_label i lbl then true else starts_with lbl k'
     | _ => false
     end.
FEnd starts_with.
              
FDefinition add_branch : T.label -> T.code -> T.code := fun (s: T.label) (k: T.code) =>
   if starts_with s k then k else T.Lgoto s :: k.

FRecursion translate_instr about S.instruction motive (fun (_ : S.instruction) => (T.code -> T.code) -> T.code -> T.code) by _rect.
Case Lop op args res := (fun f k => T.Lop op args res :: f k).
Case Lgetstack sl ofs ty r := (fun f k => T.Lgetstack sl ofs ty r :: f k).
Case Lsetstack r sl ofs ty := (fun f k => T.Lsetstack r sl ofs ty :: f k).
Case Lbranch s := (fun f k => add_branch s k).
Case Lcond cond args s1 s2 :=
(fun f k => if starts_with s1 k then T.Lcond (Op.negate_condition cond) args s2 :: add_branch s1 k else T.Lcond cond args s1 :: add_branch s2 k).
Case Lreturn := (fun f k => T.Lreturn :: f k).
FEnd translate_instr.
       
MetaData linearize_block.
Fixpoint linearize_block (b: self__Linearize.S.bblock) (k: self__Linearize.T.code) : self__Linearize.T.code :=
   match b with
   | nil => k
   | i :: b' => self__Linearize.translate_instr i (linearize_block b') k
   end.
FEnd linearize_block.

FDefinition linearize_node : S.function -> S.node -> T.code -> T.code :=
  fun (f: S.function) (pc: S.node) (k: T.code) =>
  match (S.fn_code f)!pc with
  | None => k
  | Some b => T.Llabel pc :: linearize_block b k
  end.

FDefinition linearize_body : S.function -> list S.node -> T.code :=
  fun (f: S.function) (enum: list S.node) =>
  list_fold_right (linearize_node f) enum nil.

FDefinition transf_function : S.function -> res T.function := fun f =>
  do enum <- enumerate f;
  OK (T.mkfunction
       (S.fn_sig f)
       (S.fn_stacksize f)
       (add_branch (S.fn_entrypoint f) (linearize_body f enum))).

FDefinition transf_fundef : S.fundef -> res T.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res T.program := fun p =>
  transform_partial_program transf_fundef p.

FEnd Linearize.
   
(* Linear -> Mach *)
Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

From NFPOP Require Import Bounds.
(* Fields in bounds that depend on late bound names *)

FRecursion record_regs_of_instr about S.instruction motive
  (fun (_ : S.instruction) => RegSet.t -> Regset.t) by _rect.
Case Lreturn := cheat. (* (fun u => u).*)
Case Lgetstack sl ofs ty r := cheat. (* (fun u => record_reg u r).*)
Case Lsetstack r sl ofs ty := cheat. (* (fun u => record_reg u r).*)
Case Lop op args res := cheat. (* (fun u => record_reg u res). *)
Case Llabel lbl := cheat. (* (fun u => u). *)
Case Lgoto lbl := cheat. (* (fun u => u). *)
Case Lcond cond args lbl := cheat. (* (fun u => u). *)
FEnd record_regs_of_instr.

FDefinition record_regs_of_function : S.function -> RegSet.t := fun f =>
  fold_left (fun u i => cheat (* record_regs_of_instr i u*)) (S.fn_code f) RegSet.empty.

FRecursion slots_of_instr about S.instruction motive
  (fun (_ : S.instruction) => list (slot * Z * typ)) by _rect.
Case Lreturn := nil.
Case Lgetstack sl ofs ty r := ((sl, ofs, ty) :: nil).
Case Lsetstack r sl ofs ty := ((sl, ofs, ty) :: nil).
Case Lop op args res := nil.
Case Llabel lbl := nil.
Case Lgoto lbl := nil.
Case Lcond cond args lbl := nil.
FEnd slots_of_instr.

FRecursion outgoing_space about S.instruction motive
  (fun (_ : S.instruction) => Z) by _rect.
Case Lreturn := 0.
Case Lgetstack sl ofs ty r := 0.
Case Lsetstack r sl ofs ty := 0.
Case Lop op args res := 0.
Case Llabel lbl := 0.
Case Lgoto lbl := 0.
Case Lcond cond args lbl := 0.
FEnd outgoing_space.

FDefinition max_over_instrs : (S.instruction -> Z) -> S.function -> Z := fun valu f =>
  max_over_list valu (S.fn_code f).

FDefinition max_over_slots_of_instr : (slot * Z * typ -> Z) -> S.instruction -> Z := fun valu i =>
  max_over_list valu (slots_of_instr i).

FDefinition max_over_slots_of_funct : (slot * Z * typ -> Z) -> S.function -> Z := fun valu f =>
  max_over_instrs (max_over_slots_of_instr valu) f.

MetaData function_bounds.
Program Definition function_bounds (f: self__Stacking.S.function) := {|
  used_callee_save := RegSet.elements (self__Stacking.record_regs_of_function f);
  bound_local := self__Stacking.max_over_slots_of_funct local_slot f;
  bound_outgoing := Z.max (self__Stacking.max_over_instrs self__Stacking.outgoing_space f) (self__Stacking.max_over_slots_of_funct outgoing_slot f);
  bound_stack_data := Z.max (self__Stacking.S.fn_stacksize f) 0
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

FDefinition transl_op := fun (fe: frame_env) (op: Op.operation) =>
    Op.shift_stack_operation op fe.(fe_stack_data).

MetaData save_callee_save_rec.
Fixpoint save_callee_save_rec (rl: list mreg) (ofs: Z) (k: self__Stacking.T.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      self__Stacking.T.Lsetstack r (Ptrofs.repr ofs1) ty :: save_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd save_callee_save_rec.

FDefinition save_callee_save := fun (fe: frame_env) (k: T.code) =>
  save_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

MetaData restore_callee_save_rec.
Fixpoint restore_callee_save_rec (rl: list mreg) (ofs: Z) (k: self__Stacking.T.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      self__Stacking.T.Lgetstack (Ptrofs.repr ofs1) ty r :: restore_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd restore_callee_save_rec.

FDefinition restore_callee_save := fun (fe: frame_env) (k: T.code) =>
  restore_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

FRecursion transl_instr about S.instruction motive (fun (_ : S.instruction) => frame_env -> T.code -> T.code) by _rect.
Case Lgetstack sl ofs ty r :=
(fun fe k => 
match sl with
| Local =>
    T.Lgetstack (Ptrofs.repr (offset_local fe ofs)) ty r :: k
| Incoming =>
    T.Lgetparam (Ptrofs.repr (offset_arg ofs)) ty r :: k
| Outgoing =>
    T.Lgetstack (Ptrofs.repr (offset_arg ofs)) ty r :: k
end).
Case Lsetstack r sl ofs ty :=
(fun fe k => 
  match sl with
  | Local =>
      T.Lsetstack r (Ptrofs.repr (offset_local fe ofs)) ty :: k
  | Incoming =>
      k
  | Outgoing =>
      T.Lsetstack r (Ptrofs.repr (offset_arg ofs)) ty :: k
  end).
Case Lop op args res := (fun fe k =>  T.Lop (transl_op fe op) args res :: k).
Case Llabel lbl := (fun fe k => T.Llabel lbl :: k).
Case Lgoto lbl := (fun fe k => T.Lgoto lbl :: k).
Case Lcond cond args lbl := (fun fe k => T.Lcond cond args lbl :: k).
Case Lreturn := (fun fe k =>  restore_callee_save fe (T.Lreturn :: k)).
FEnd transl_instr.

FDefinition transl_code : frame_env -> list S.instruction -> T.code := fun fe il =>     
  list_fold_right (fun i k => transl_instr i fe k) il nil.

FDefinition transl_body := fun (f: S.function) (fe: frame_env) =>
  save_callee_save fe (transl_code fe (S.fn_code f)).

Local Open Scope string_scope.

FDefinition transf_function : S.function -> res T.function := fun f =>
  let fe := make_env (function_bounds f) in
  (* Don't type check linear *)
  (*if negb (wt_function f) then
    Error (msg "Ill-formed S code")*)
  if zlt Ptrofs.max_unsigned fe.(fe_size) then
    Error (msg "Too many spilled variables, stack size exceeded")
  else
    OK (T.mkfunction
         (S.fn_sig f)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr))).

FDefinition transf_fundef : S.fundef -> res T.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res T.program := fun p =>
  transform_partial_program transf_fundef p.

FEnd Stacking.

(* Mach -> Asm *)
Family Asmgen.
Family S extends Mach. FEnd S.
Family T extends Asm. FEnd T.

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
  if Int.eq lo Int.zero then T.Pluiw r hi :: k
  else T.Pluiw r hi :: T.Paddiw r r lo :: k.

FDefinition loadimm32 := fun (r: ireg) (n: int) (k: T.code) =>
  match make_immed32 n with
  | self__Asmgen.Imm32_single imm => T.Paddiw r X0 imm :: k
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
  if Int64.eq lo Int64.zero then T.Pluil r hi :: k
  else T.Pluil r hi :: T.Paddil r r lo :: k.


FDefinition loadimm64 := fun (r: ireg) (n: int64) (k: T.code) =>
  match make_immed64 n with
  | self__Asmgen.Imm64_single imm => T.Paddil r X0 imm :: k
  | self__Asmgen.Imm64_pair hi lo => load_hilo64 r hi lo k
  | self__Asmgen.Imm64_large imm  => T.Ploadli r imm :: k
  end.

FDefinition opimm32 := 
fun (op: ireg -> ireg0 -> ireg0 -> T.instruction)
    (opimm: ireg -> ireg0 -> int -> T.instruction)
    (rd rs: ireg) (n: int) (k: T.code) =>
  match make_immed32 n with
  | self__Asmgen.Imm32_single imm => opimm rd rs imm :: k
  | self__Asmgen.Imm32_pair hi lo => load_hilo32 X31 hi lo (op rd rs X31 :: k)
  end.

FDefinition opimm64 := 
  fun (op: ireg -> ireg0 -> ireg0 -> T.instruction)
      (opimm: ireg -> ireg0 -> int64 -> T.instruction)
      (rd rs: ireg) (n: int64) (k: T.code) =>
  match make_immed64 n with
  | self__Asmgen.Imm64_single imm => opimm rd rs imm :: k
  | self__Asmgen.Imm64_pair hi lo => load_hilo64 X31 hi lo (op rd rs X31 :: k)
  | self__Asmgen.Imm64_large imm  => T.Ploadli X31 imm :: op rd rs X31 :: k
  end.

FDefinition addimm32 := opimm32 T.Paddw T.Paddiw.
FDefinition xorimm32 := opimm32 T.Pxorw T.Pxoriw.
FDefinition sltimm32 := opimm32 T.Psltw T.Psltiw.
FDefinition addimm64 := opimm64 T.Paddl T.Paddil.
FDefinition sltuimm32 := opimm32 T.Psltuw T.Psltiuw.

FDefinition addptrofs := fun (rd rs: ireg) (n: ptrofs) (k: T.code) =>
  if Ptrofs.eq_dec n Ptrofs.zero then
    T.Pmv rd rs :: k
  else
    if Archi.ptr64
    then addimm64 rd rs (Ptrofs.to_int64 n) k
    else addimm32 rd rs (Ptrofs.to_int n) k.

FDefinition transl_cond_int32s := fun (cmp: comparison) (rd: ireg) (r1 r2: ireg0) (k: T.code) =>
  match cmp with
  | Ceq => T.Pseqw rd r1 r2 :: k
  | Cne => T.Psnew rd r1 r2 :: k
  | Clt => T.Psltw rd r1 r2 :: k
  | Cle => T.Psltw rd r2 r1 :: T.Pxoriw rd rd Int.one :: k
  | Cgt => T.Psltw rd r2 r1 :: k
  | Cge => T.Psltw rd r1 r2 :: T.Pxoriw rd rd Int.one :: k
  end.

FDefinition transl_cond_int32u := fun (cmp: comparison) (rd: ireg) (r1 r2: ireg0) (k: T.code) =>
  match cmp with
  | Ceq => T.Pseqw rd r1 r2 :: k
  | Cne => T.Psnew rd r1 r2 :: k
  | Clt => T.Psltuw rd r1 r2 :: k
  | Cle => T.Psltuw rd r2 r1 :: T.Pxoriw rd rd Int.one :: k
  | Cgt => T.Psltuw rd r2 r1 :: k
  | Cge => T.Psltuw rd r1 r2 :: T.Pxoriw rd rd Int.one :: k
  end.

FDefinition transl_condimm_int32s := fun (cmp: comparison) (rd: ireg) (r1: ireg) (n: int) (k: T.code) => 
  if Int.eq n Int.zero then transl_cond_int32s cmp rd r1 X0 k else
  match cmp with
  | Ceq | Cne => xorimm32 rd r1 n (transl_cond_int32s cmp rd rd X0 k)
  | Clt => sltimm32 rd r1 n k
  | Cle => if Int.eq n (Int.repr Int.max_signed)
           then loadimm32 rd Int.one k
           else sltimm32 rd r1 (Int.add n Int.one) k
  | _   => loadimm32 X31 n (transl_cond_int32s cmp rd r1 X31 k)
  end.

FDefinition transl_condimm_int32u := fun (cmp: comparison) (rd: ireg) (r1: ireg) (n: int) (k: T.code) =>
  if Int.eq n Int.zero then transl_cond_int32u cmp rd r1 X0 k else
  match cmp with
  | Clt => sltuimm32 rd r1 n k
  | _   => loadimm32 X31 n (transl_cond_int32u cmp rd r1 X31 k)
  end.

FRecursion transl_cond_op about Op.condition motive (fun (_ : Op.condition) => ireg -> list mreg -> T.code -> res T.code) by _rect.
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
FEnd transl_cond_op.

From NFPOP Require Import Prelude.

FRecursion transl_op about Op.operation motive (fun (_ : Op.operation) => list mreg -> mreg -> T.code -> res T.code) by _rect.
Case Omove :=
(fun args res k =>
  match args with 
  | a1 :: nil =>
      match preg_of res, preg_of a1 with
      | IR r, IR a => OK (T.Pmv r a :: k)
      | FR r, FR a => OK (T.Pfmv r a :: k)
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
          then T.Pfcvtdw rd X0 :: k
          else cheat T.Ploadfi rd f :: k)
  | _ => Error(msg "Asmgen.transl_op")
  end).
Case Osingleconst f := 
(fun args res k => 
  match args with
  | nil => 
       do rd <- freg_of res;
      OK (if Float32.eq_dec f Float32.zero
          then T.Pfcvtsw rd X0 :: k
          else T.Ploadsi rd f :: k)
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
FEnd transl_op.

FDefinition transl_cbranch_int32s := fun (cmp: comparison) (r1 r2: ireg0) (lbl: T.label) =>
  match cmp with
  | Ceq => T.Pbeqw r1 r2 lbl
  | Cne => T.Pbnew r1 r2 lbl
  | Clt => T.Pbltw r1 r2 lbl
  | Cle => T.Pbgew r2 r1 lbl
  | Cgt => T.Pbltw r2 r1 lbl
  | Cge => T.Pbgew r1 r2 lbl
  end.

FDefinition transl_cbranch_int32u := fun (cmp: comparison) (r1 r2: ireg0) (lbl: T.label) =>
  match cmp with
  | Ceq => T.Pbeqw  r1 r2 lbl
  | Cne => T.Pbnew  r1 r2 lbl
  | Clt => T.Pbltuw r1 r2 lbl
  | Cle => T.Pbgeuw r2 r1 lbl
  | Cgt => T.Pbltuw r2 r1 lbl
  | Cge => T.Pbgeuw r1 r2 lbl
  end.

FRecursion transl_cbranch about Op.condition motive (fun (_ : Op.condition) => list mreg -> T.label -> T.code -> res T.code) by _rect.
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
FEnd transl_cbranch.

FDefinition indexed_memory_access :=
  fun (mk_instr: ireg -> T.offset -> T.instruction)
      (base: ireg) (ofs: ptrofs) (k: T.code) =>
  if Archi.ptr64 then
    match make_immed64 (Ptrofs.to_int64 ofs) with
    | self__Asmgen.Imm64_single imm =>
        mk_instr base (T.Ofsimm (Ptrofs.of_int64 imm)) :: k
    | self__Asmgen.Imm64_pair hi lo =>
        T.Pluil X31 hi :: T.Paddl X31 base X31 :: mk_instr X31 (T.Ofsimm (Ptrofs.of_int64 lo)) :: k
    | self__Asmgen.Imm64_large imm =>
        T.Ploadli X31 imm :: T.Paddl X31 base X31 :: mk_instr X31 (T.Ofsimm Ptrofs.zero) :: k
    end
  else
    match make_immed32 (Ptrofs.to_int ofs) with
    | self__Asmgen.Imm32_single imm =>
        mk_instr base (T.Ofsimm (Ptrofs.of_int imm)) :: k
    | self__Asmgen.Imm32_pair hi lo =>
        T.Pluiw X31 hi :: T.Paddw X31 base X31 :: mk_instr X31 (T.Ofsimm (Ptrofs.of_int lo)) :: k
    end.

FDefinition loadind := 
  fun (base: ireg) (ofs: ptrofs) (ty: typ) (dst: mreg) (k: T.code) =>
  match ty, preg_of dst with
  | AST.Tint,    IR rd => OK (indexed_memory_access (T.Plw rd) base ofs k)
  | AST.Tlong,   IR rd => OK (indexed_memory_access (T.Pld rd) base ofs k)
  | AST.Tsingle, FR rd => OK (indexed_memory_access (T.Pfls rd) base ofs k)
  | AST.Tfloat,  FR rd => OK (indexed_memory_access (T.Pfld rd) base ofs k)
  | AST.Tany32,  IR rd => OK (indexed_memory_access (T.Plw_a rd) base ofs k)
  | AST.Tany64,  IR rd => OK (indexed_memory_access (T.Pld_a rd) base ofs k)
  | AST.Tany64,  FR rd => OK (indexed_memory_access (T.Pfld_a rd) base ofs k)
  | _, _           => Error (msg "Asmgen.loadind")
  end.

FDefinition storeind := fun (src: mreg) (base: ireg) (ofs: ptrofs) (ty: typ) (k: T.code) => 
  match ty, preg_of src with
  | AST.Tint,    IR rd => OK (indexed_memory_access (T.Psw rd) base ofs k)
  | AST.Tlong,   IR rd => OK (indexed_memory_access (T.Psd rd) base ofs k)
  | AST.Tsingle, FR rd => OK (indexed_memory_access (T.Pfss rd) base ofs k)
  | AST.Tfloat,  FR rd => OK (indexed_memory_access (T.Pfsd rd) base ofs k)
  | AST.Tany32,  IR rd => OK (indexed_memory_access (T.Psw_a rd) base ofs k)
  | AST.Tany64,  IR rd => OK (indexed_memory_access (T.Psd_a rd) base ofs k)
  | AST.Tany64,  FR rd => OK (indexed_memory_access (T.Pfsd_a rd) base ofs k)
  | _, _           => Error (msg "Asmgen.storeind")
  end.

FDefinition loadind_ptr := fun (base: ireg) (ofs: ptrofs) (dst: ireg) (k: T.code) => 
  indexed_memory_access (if Archi.ptr64 then T.Pld dst else T.Plw dst) base ofs k.

FDefinition storeind_ptr := fun (src: ireg) (base: ireg) (ofs: ptrofs) (k: T.code) =>
  indexed_memory_access (if Archi.ptr64 then T.Psd src else T.Psw src) base ofs k.

FDefinition make_epilogue := fun (f: S.function) (k: T.code) =>
  loadind_ptr SP (S.fn_retaddr_ofs f) RA
    (cheat T.Pfreeframe (S.fn_stacksize f) (S.fn_link_ofs f) :: k).

FRecursion transl_instr about S.instruction motive (fun (_ : S.instruction) => S.function -> bool -> T.code -> res T.code) by _rect.
Case Lgetstack ofs ty dst := (fun f ep k => loadind SP ofs ty dst k).
Case Lsetstack src ofs ty := (fun f ep k =>  storeind src SP ofs ty k).
Case Lgetparam ofs ty dst := 
(fun f ep k => 
    do c <- loadind X30 ofs ty dst k;
      OK (if ep then c
                else loadind_ptr SP (S.fn_link_ofs f) X30 c)).
Case Lop op args res := (fun f ep k =>  transl_op op args res k).
Case Llabel lbl := (fun f ep k =>  OK (T.Plabel lbl :: k)).
Case Lgoto lbl := (fun f ep k => OK (T.Pj_l lbl :: k)).
Case Lcond cond args lbl := (fun f ep k => transl_cbranch cond args lbl k).
Case Lreturn := (fun f ep k => OK (make_epilogue f (T.Pj_r RA (S.fn_sig f) :: k))).
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
                         (it1p: bool) (k: self__Asmgen.T.code -> res self__Asmgen.T.code) :=
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
  OK (T.mkfunction (S.fn_sig f)
        (cheat T.Pallocframe (S.fn_stacksize f) (S.fn_link_ofs f) ::
         storeind_ptr RA SP (S.fn_retaddr_ofs f) (cheat T.Pcfi_rel_offset (Ptrofs.to_int (S.fn_retaddr_ofs f)):: c))).

FDefinition transf_function : S.function -> res T.function := fun f =>
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z (T.fn_code tf))
  then Error (msg "code size exceeded")
  else OK tf.

FDefinition transf_fundef : S.fundef -> res T.fundef := fun f =>
  transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res T.program := fun p =>
  transform_partial_program transf_fundef p.     

FEnd Asmgen.

FEnd Base.

Trait Comp_Loops extends Base.

Trait C_Swhile extends C.
FInductive stmt : Type :=  
  | Swhile : expr -> stmt -> stmt(* while loop *)  
  | Sbreak : stmt(* break stmt *)
  | Scontinue : stmt. (* continue statement *)  
FEnd C_Swhile.

Trait C_Sdowhile extends C.
FInductive stmt : Type :=  
| Sdowhile : expr -> stmt -> stmt. (* do loop *)
FEnd C_Sdowhile.

Trait C_Sfor extends C.
FInductive stmt : Type :=  
| Sfor: stmt -> expr -> stmt -> stmt -> stmt. (* for loop *)
FEnd C_Sfor.

Family C extends C_Swhile, C_Sdowhile, C_Sfor.
FEnd C.

Trait Clight_Sloop extends Clight.
FInductive stmt : Type := 
  | Sloop: stmt -> stmt -> stmt (* infinite loop *)
  | Sbreak : stmt (* break statement *)
  | Scontinue : stmt. (* continue statement *) 
FEnd Clight_Sloop.

Family Clight extends Clight_Sloop.
FEnd Clight.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Swhile extends SimplExpr.
Family S extends C_Swhile. FEnd S.

FRecursion transl_stmt.
Case Swhile e s1 :=
(do s' <- transl_if e T.Sskip T.Sbreak;
 do ts1 <- transl_stmt s1;
 ret (T.Sloop (T.Sseq s' ts1) T.Sskip)).
Case Sbreak := (ret T.Sbreak).                     
Case Scontinue := (ret T.Scontinue).
FEnd transl_stmt.

FEnd SimplExpr_Swhile.

Trait SimplExpr_Sdowhile extends SimplExpr.
Family S extends C_Sdowhile. FEnd S.

FRecursion transl_stmt.
Case Sdowhile e s1 :=
(do s' <- transl_if e T.Sskip T.Sbreak;
 do ts1 <- transl_stmt s1;
 ret (T.Sloop ts1 s')).  
FEnd transl_stmt.

FEnd SimplExpr_Sdowhile.

Trait SimplExpr_Sfor extends SimplExpr.
Family S extends C_Sfor. FEnd S.

FRecursion transl_stmt.
Case Sfor s1 e2 s3 s4 :=
(do ts1 <- transl_stmt s1;
 do s' <- transl_if e2 T.Sskip T.Sbreak;
 do ts3 <- transl_stmt s3;
 do ts4 <- transl_stmt s4;
 if is_Sskip s1 then
   ret (T.Sloop (T.Sseq s' ts4) ts3)
 else
   ret (T.Sseq ts1 (T.Sloop (T.Sseq s' ts4) ts3))).
FEnd transl_stmt.

FEnd SimplExpr_Sfor.

Family SimplExpr extends
  SimplExpr_Sfor,
  SimplExpr_Sdowhile,
  SimplExpr_Swhile.
FEnd SimplExpr.

Family Cfam.

FInductive stmt : Type :=
| Sloop: stmt -> stmt
| Sblock: stmt -> stmt
| Sexit: nat -> stmt.

FEnd Cfam.

From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.

Trait Cshmgen_Sloop extends Cshmgen.
Family S extends Clight_Sloop. FEnd S.

FRecursion transl_stmt.

Case Sloop s1 s2 :=
(fun ce tyret nbrk ncnt =>
  do ts1 <- transl_stmt s1 ce tyret 1%nat 0%nat;
  do ts2 <- transl_stmt s2 ce tyret 0%nat ((1 + ncnt)%nat);
  OK (T.Sblock (T.Sloop (T.Sseq (T.Sblock ts1) ts2)))).
Case Sbreak := (fun ce tyret nbrk ncnt => OK (T.Sexit nbrk)).
Case Scontinue := (fun ce tyret nbrk ncnt => OK (T.Sexit ncnt)).
FEnd transl_stmt.

FEnd Cshmgen_Sloop.

Family Cshmgen extends Cshmgen_Sloop.
FEnd Cshmgen.

Family Cfamtransl.

FRecursion transl_stmt.
Case Sloop body := (do ts <- transl_stmt body; OK (T.Sloop ts)).
Case Sblock body := (do ts <- transl_stmt body; OK (T.Sblock ts)).
Case Sexit n := (OK (T.Sexit n)).
FEnd transl_stmt.

FEnd Cfamtransl.

Trait RTL_jumptable extends RTL.
FInductive instruction: Type :=
| Ijumptable: reg -> list node -> instruction.  
FEnd RTL_jumptable.

Family RTL extends RTL_jumptable.
FEnd RTL.

From NFPOP Require Import RTLmonad.

Trait RTLgen_Sloop extends RTLgen.

Inherit labelmap.

FDefinition transl_exit : list T.node -> nat -> mon T.node := fun nexits n =>
  match nth_error nexits n with
  | None => error (Errors.msg "RTLgen: wrong exit")
  | Some ne => ret ne
  end.

FRecursion transl_stmt.
Case Sloop sbody :=
(fun map nd nexits ngoto nret rret =>
  do n1 <- reserve_instr;
  do n2 <- transl_stmt sbody map n1 nexits ngoto nret rret;
  do xx <- update_instr n1 (T.Inop n2);
  add_instr (T.Inop n2)).
Case Sblock sbody :=
(fun map nd nexits ngoto nret rret =>
   transl_stmt sbody map nd (nd :: nexits) ngoto nret rret).
Case Sexit n := (fun map nd nexits ngoto nret rret => transl_exit nexits n).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sloop s1 := (fun lm => reserve_labels s1 lm).
Case Sblock s1 := (fun lm => reserve_labels s1 lm).
Case Sexit n := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen_Sloop.

Family RTLgen extends RTLgen_Sloop.
FEnd RTLgen.

Trait LTL_jumptable extends LTL.
FInductive instruction: Type :=
| Ljumptable : mreg -> list node -> instruction.

FRecursion successors_instr.
Case Ljumptable a tbl := (fun rest => tbl).
FEnd successors_instr.
FEnd LTL_jumptable.

Family Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.
FEnd Lfam.

(* nanopassesn*)
Trait Linearize_jumptable extends Linearize.
Family S extends LTL_jumptable. FEnd S.

FRecursion starts_with_label.
Case _ := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Ljumptable args tbl := (fun f k => T.Ljumptable args tbl :: k).
FEnd translate_instr.

FEnd Linearize_jumptable.

Family Linearize extends Linearize_jumptable.
FEnd Linearize.

Trait Stacking_jumptable extends Stacking.

FRecursion record_regs_of_instr.
Case Ljumptable arg tbl := cheat.
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case Ljumptable arg tbl := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FRecursion transl_instr.
Case Ljumptable arg tbl := (fun fe k => T.Ljumptable arg tbl :: k).
FEnd transl_instr.
FEnd Stacking_jumptable.

Family Stacking extends Stacking_jumptable.
FEnd Stacking.

Trait Asmgen_jumptable extends Asmgen.
FRecursion transl_instr.
From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.
Case Ljumptable arg tbl :=
(fun f ep k =>
   do r <- ireg_of arg;
   OK (T.Pbtbl r tbl :: k)).
FEnd transl_instr.

FRecursion it1_is_parent.
Case _ := (fun before => false).
FEnd it1_is_parent.

FEnd Asmgen_jumptable.

Family Asmgen extends Asmgen_jumptable.
FEnd Asmgen.

FEnd Comp_Loops.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait C_Switch extends C.
FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt (* switch statement *)
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

FEnd C_Switch.

Family C extends C_Switch.
FEnd C.

Trait Clight_Switch extends Clight.
FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt (* switch statement *)
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
FEnd Clight_Switch.

Family Clight extends Clight_Switch.
FEnd Clight.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Switch extends SimplExpr.
Family S extends C_Switch. FEnd S.

FRecursion transl_stmt.
Case Sswitch e ls := 
(do (s', a) <- transl_expression e;
  (* do tls <- transl_lblstmt ls;*)
 ret (T.Sseq s' (T.Sswitch a cheat))).
FEnd transl_stmt.

FEnd SimplExpr_Switch.

Family SimplExpr extends SimplExpr_Switch.
FEnd SimplExpr.

Trait Csharpminor_Switch extends Csharpminor.
FInductive stmt : Type := 
| Sswitch: bool -> expr -> lbl_stmts -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
FEnd Csharpminor_Switch.

Family Csharpminor extends Csharpminor_Switch.
FEnd Csharpminor.

Trait Cshmgen_Switch extends Cshmgen.
Family S extends Clight_Switch. FEnd S.

From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.
FRecursion transl_stmt.
Case Sswitch a sl := 
(fun ce tyret nbrk ncnt =>
   do ta <- transl_expr a ce;
   (* do tsl <- transl_lbl_stmt ce tyret 0%nat (S ncnt) sl;*)   
    match classify_switch (S.typeof a) with
    | switch_case_i => OK (T.Sblock (T.Sswitch false ta cheat (*tsl*)))
    | switch_case_l => OK (T.Sblock (T.Sswitch true ta cheat (*tsl*) ))
    | switch_default => Error(msg "Cshmgen.transl_stmt(switch)")
    end).
FEnd transl_stmt.
FEnd Cshmgen_Switch.

Family Cshmgen extends Cshmgen_Switch.
FEnd Cshmgen.

Trait Cminor_Switch extends Cminor.
FInductive stmt : Type := 
| Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt.
FEnd Cminor_Switch.

Family Cminor extends Cminor_Switch.
FEnd Cminor.

Trait CminorSel_Switch extends CminorSel.

Inherit expr.

MetaData exitexpr.
Inductive exitexpr : Type :=
  | XEexit: nat -> exitexpr
  | XEjumptable: self__CminorSel_Switch.expr -> list nat -> exitexpr
  | XEcondition: self__CminorSel_Switch.condexpr -> exitexpr -> exitexpr -> exitexpr
  | XElet: self__CminorSel_Switch.expr -> exitexpr -> exitexpr.
FEnd exitexpr.

FInductive stmt : Type := 
| Sswitch: exitexpr -> stmt.
FEnd CminorSel_Switch.

Family CminorSel extends CminorSel_Switch.
FEnd CminorSel.

(*Trait Cminorgen_Switch extends Cminorgen.
Family S extends Csharpminor_Switch.*)

Family Cminorgen.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FDefinition exit_env := list bool.

FRecursion switch_table about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => nat -> list (Z * nat) * nat) by _rect.
Case LSnil := (fun k => (nil, k)).
Case LScons lbl stmt rem :=
(fun k =>
   match lbl with
   | None => let (tbl, dfl) := switch_table rem ((1 + k)%nat) in (tbl, k)
   | Some ni => let (tbl, dfl) := switch_table rem ((1 + k)%nat) in ((ni, k) :: tbl, dfl)
   end).
FEnd switch_table.

FRecursion switch_env about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => exit_env -> exit_env) by _rect.
Case LSnil := (fun e => e).
Case LScons a b ls' := (fun e => false :: switch_env ls' e).
FEnd switch_env.


FRecursion transl_stmt.
Case Sswitch long e ls :=
  (let (tbl, dfl) := switch_table ls O in
  do te <- transl_expr (*cenv*) e;
  cheat (*transl_lblstmt cenv*) (switch_env ls cheat (*xenv*)) ls (T.Sswitch long te tbl dfl)).
FEnd transl_stmt.

FEnd Cminorgen.

(*FEnd Cminorgen_Switch.

Family Cminorgen extends Cminorgen_Switch.
FEnd Cminorgen. *)

From NFPOP Require Import Switch.

Trait Selection_Switch extends Selection.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

MetaData compile_switch.
Parameter compile_switch: Z -> nat -> table -> comptree.
FEnd compile_switch.

Inherit condexpr_of_expr.

MetaData sel_switch.

Section SEL_SWITCH.
Variable make_cmp_eq: self__Selection_Switch.T.expr -> Z -> self__Selection_Switch.T.expr.
Variable make_cmp_ltu: self__Selection_Switch.T.expr -> Z -> self__Selection_Switch.T.expr.
Variable make_sub: self__Selection_Switch.T.expr -> Z -> self__Selection_Switch.T.expr.
Variable make_to_int: self__Selection_Switch.T.expr -> self__Selection_Switch.T.expr.

Fixpoint sel_switch  
  (arg: nat) (t: comptree): self__Selection_Switch.T.exitexpr :=
  match t with
  | CTaction act =>
      self__Selection_Switch.T.XEexit act
  | CTifeq key act t' =>
      self__Selection_Switch.T.XEcondition (self__Selection_Switch.condexpr_of_expr (make_cmp_eq (self__Selection_Switch.T.Eletvar arg) key))
                  (self__Selection_Switch.T.XEexit act)
                  (sel_switch arg t')
  | CTiflt key t1 t2 =>
      self__Selection_Switch.T.XEcondition (self__Selection_Switch.condexpr_of_expr (make_cmp_ltu (self__Selection_Switch.T.Eletvar arg) key))
                  (sel_switch arg t1)
                  (sel_switch arg t2)
  | CTjumptable ofs sz tbl t' =>
      self__Selection_Switch.T.XElet (make_sub (self__Selection_Switch.T.Eletvar arg) ofs)
        (self__Selection_Switch.T.XEcondition (self__Selection_Switch.condexpr_of_expr (make_cmp_ltu (self__Selection_Switch.T.Eletvar O) sz))
                     (self__Selection_Switch.T.XEjumptable (make_to_int (self__Selection_Switch.T.Eletvar 0%nat)) tbl)
                     (sel_switch ((1 + arg)%nat) t'))
  end.
End SEL_SWITCH.
FEnd sel_switch.

(*Nondetfunction compimm (default: comparison -> int -> condition)
                       (sem: comparison -> int -> int -> bool)
                       (c: comparison) (e1: expr) (n2: int) :=
  match c, e1 with
  | c, Eop (Ointconst n1) Enil =>
      Eop (Ointconst (if sem c n1 n2 then Int.one else Int.zero)) Enil
  | Ceq, Eop (Ocmp c) el =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp (negate_condition c)) el
      else if Int.eq_dec n2 Int.one then
        Eop (Ocmp c) el
      else
        Eop (Ointconst Int.zero) Enil
  | Cne, Eop (Ocmp c) el =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp c) el
      else if Int.eq_dec n2 Int.one then
        Eop (Ocmp (negate_condition c)) el
      else
        Eop (Ointconst Int.one) Enil
  | _, _ =>
       Eop (Ocmp (default c n2)) (e1 ::: Enil)
  end.

Nondetfunction comp (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      compimm Ccompimm Int.cmp (swap_comparison c) t2 n1
  | t1, Eop (Ointconst n2) Enil =>
      compimm Ccompimm Int.cmp c t1 n2
  | _, _ =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.

Nondetfunction compu (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      compimm Ccompuimm Int.cmpu (swap_comparison c) t2 n1
  | t1, Eop (Ointconst n2) Enil =>
      compimm Ccompuimm Int.cmpu c t1 n2
  | _, _ =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.

Nondetfunction sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil =>
      addimm (Int.neg n2) t1
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), t2 =>
      addimm n1 (Eop Osub (t1:::t2:::Enil))
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | _, _ => Eop Osub (e1:::e2:::Enil)
  end.

FDefinition sel_switch_int :=
  sel_switch
    (fun arg n => comp Ceq arg (Eop (Ointconst (Int.repr n)) Enil))
    (fun arg n => compu Clt arg (Eop (Ointconst (Int.repr n)) Enil))
    (fun arg ofs => sub arg (Eop (Ointconst (Int.repr ofs)) Enil))
    (fun arg => arg).

FDefinition sel_switch_long :=
  sel_switch
    (fun arg n => cmpl Ceq arg (longconst (Int64.repr n)))
    (fun arg n => cmplu Clt arg (longconst (Int64.repr n)))
    (fun arg ofs => subl arg (longconst (Int64.repr ofs)))
    lowlong.*)

FRecursion transl_stmt.
Case Sswitch t e cases dfl := cheat.
  (*(do te <- transl_expr e;
   let t := compile_switch Int64.modulus dfl cases in
   if validate_switch Int64.modulus dfl cases t
   then OK (T.Sswitch (T.XElet te (sel_switch_long O t)))
   else Error (msg "Selection: bad switch (long)")) *)
FEnd transl_stmt.
FEnd Selection_Switch.

Family Selection extends Selection_Switch.
FEnd Selection.

Trait RTLgen_Switch extends RTLgen.

Inherit labelmap.

From NFPOP Require Import RTLmonad.

Inherit transl_exit.

MetaData transl_jumptable.
Fixpoint transl_jumptable (nexits: list self__RTLgen_Switch.T.node) (tbl: list nat) : self__RTLgen_Switch.mon (list self__RTLgen_Switch.T.node) :=
  match tbl with
  | nil => ret nil
  | t1 :: tl =>
      do n1 <- self__RTLgen_Switch.transl_exit nexits t1;
      do nl <- transl_jumptable nexits tl;
      ret (n1 :: nl)
  end.
FEnd transl_jumptable.

MetaData transl_exitexpr.
Fixpoint transl_exitexpr (map: mapping) (a: self__RTLgen_Switch.S.exitexpr) (nexits: list self__RTLgen_Switch.T.node)
                         {struct a} : self__RTLgen_Switch.mon self__RTLgen_Switch.T.node :=
  match a with
  | self__RTLgen_Switch.S.XEexit n =>
      self__RTLgen_Switch.transl_exit nexits n
  | self__RTLgen_Switch.S.XEjumptable a tbl =>
      do r <- self__RTLgen_Switch.alloc_reg a map;
      do tbl' <- self__RTLgen_Switch.transl_jumptable nexits tbl;
      do n1 <- self__RTLgen_Switch.add_instr (self__RTLgen_Switch.T.Ijumptable r tbl');
         self__RTLgen_Switch.transl_expr a map r n1
  | self__RTLgen_Switch.S.XEcondition a b c =>
      do nc <- transl_exitexpr map c nexits;
      do nb <- transl_exitexpr map b nexits;
         self__RTLgen_Switch.transl_condexpr a map nb nc
  | self__RTLgen_Switch.S.XElet a b =>
      do r <- self__RTLgen_Switch.new_reg;
      do n1 <- transl_exitexpr (self__RTLgen_Switch.add_letvar map r) b nexits;
         self__RTLgen_Switch.transl_expr a map r n1
  end.
FEnd transl_exitexpr.

FRecursion transl_stmt.
Case Sswitch a := (fun map nd nexits ngoto nret rret => transl_exitexpr map a nexits).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sswitch a := (fun lm => ret lm).
FEnd reserve_labels.
FEnd RTLgen_Switch.

Family RTLgen extends RTLgen_Switch.
FEnd RTLgen.

FEnd Comp_Switch.

Trait Comp_Heap extends Base.

Trait C_Eaddrof extends C.
FInductive expr : Type :=
| Eaddrof : expr -> type -> expr. 

FRecursion typeof.
Case Eaddrof e ty := ty.
FEnd typeof.
FEnd C_Eaddrof.

Trait C_Ederef extends C.
FInductive expr : Type :=
| Ederef : expr -> type -> expr. 

FRecursion typeof.
Case Ederef e ty := ty.
FEnd typeof.
FEnd C_Ederef.

Trait C_Evalof extends C.
FInductive expr : Type :=
| Evalof : expr -> type -> expr. (* l-value used as a r-value *)

FRecursion typeof.
Case Evalof e ty := ty.
FEnd typeof.
FEnd C_Evalof.

Trait C_Eassign extends C.
FInductive expr : Type :=
| Eassign : expr -> expr -> type -> expr. (* assignment l = r *)

FRecursion typeof.
Case Eassign e1 e2 ty := ty.
FEnd typeof.
FEnd C_Eassign.

Family C extends 
  C_Eassign,
  C_Evalof,
  C_Ederef,
  C_Eaddrof.
FEnd C.

Trait Clight_Evar extends Clight.
FInductive expr : Type :=
| Evar: ident -> type -> expr.(* variable *)

FRecursion typeof.
Case Evar i t := t.
FEnd typeof.
FEnd Clight_Evar.

Trait Clight_Ederef extends Clight.
FInductive expr : Type :=
| Ederef: expr -> type -> expr. (* pointer dereference (unary *)

FRecursion typeof.
Case Ederef i t := t.
FEnd typeof.
FEnd Clight_Ederef.

Trait Clight_Eaddrof extends Clight.
FInductive expr : Type :=
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Eaddrof e t := t.
FEnd typeof.
FEnd Clight_Eaddrof.

Trait Clight_Sassign extends Clight.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)
FEnd Clight_Sassign.

Family Clight extends 
  Clight_Sassign, 
  Clight_Eaddrof,
  Clight_Ederef,
  Clight_Evar.
FEnd Clight.

Trait SimplExpr_Eassign extends SimplExpr.
Family S extends C_Eassign. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

From NFPOP Require Import Mon.
Local Open Scope gensym_monad_scope.

FRecursion is_bitfield_access about T.expr motive (fun (_ : T.expr) => mon bitfield) by _rect.
Case _ := (ret Full).
FEnd is_bitfield_access.

FDefinition chunk_for_volatile_type : type -> bitfield -> option memory_chunk := fun ty bf =>
  if type_is_volatile ty then
    match access_mode ty with
    | By_value chunk =>
        match bf with
        | Full => Some chunk
        | Bits _ _ _ _ => None
        end
    | _ => None
    end
  else None.

FDefinition make_assign : bitfield -> T.expr -> T.expr -> T.stmt := fun bf l r =>
  match chunk_for_volatile_type (T.typeof l) bf with
  | None =>
      T.Sassign l r
  | Some chunk =>
      let ty := T.typeof l in
      let typtr := Tpointer ty noattr in
      cheat
      (*cheat (*Sbuiltin*) None (EF_vstore chunk) (typtr :: (ty :: nil))
                    (T.Eaddrof l typtr :: r :: nil) *)
  end.


FDefinition make_normalize := fun (sz: intsize) (sg: signedness) (width: Z) (r: T.expr) => r.
(*  let intconst (n: Z) := Econst_int (Int.repr n) type_int32s in
  if intsize_eq sz IBool || signedness_eq sg Unsigned then
    let mask := two_p width - 1 in
    Ebinop Oand r (intconst mask) (typeof r)
  else
    let amount := Int.zwordsize - width in
    Ebinop Oshr
           (Ebinop Oshl r (intconst amount) type_int32s)
           (intconst amount)
           (typeof r).*)

FDefinition make_assign_value := fun (bf: bitfield) (r: T.expr) =>
  match bf with
  | Full => r
  | Bits sz sg pos width => make_normalize sz sg width r
  end.

FRecursion transl_expr.
Case Eassign l1 r2 ty := 
(fun dst => 
 do (sl1, a1) <- transl_expr l1 self__SimplExpr_Eassign.For_val;
 do (sl2, a2) <- transl_expr r2 self__SimplExpr_Eassign.For_val;
 do bf <- is_bitfield_access a1;
 let ty1 := S.typeof l1 in
 let ty2 := S.typeof r2 in
 match dst with
 | self__SimplExpr_Eassign.For_val | self__SimplExpr_Eassign.For_set _ =>
     do t <- gensym ty1;
     ret (finish dst
            (sl1 ++ sl2 ++ T.Sset t (T.Ecast a2 ty1) :: make_assign bf a1 (T.Etempvar t ty1) :: nil)
            (make_assign_value bf (T.Etempvar t ty1)))
 | self__SimplExpr_Eassign.For_effects =>
     ret (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil,
          dummy_expr)
 end).
FEnd transl_expr.
FEnd SimplExpr_Eassign.

Trait SimplExpr_Evalof extends Clight_Sassign.
Family S extends C_Evalof. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FDefinition make_set := fun (bf: bitfield) (id: ident) (l: T.expr) =>
  match chunk_for_volatile_type (T.typeof l) bf with
  | None => T.Sset id l
  | Some chunk => cheat
      (*let typtr := Tpointer (typeof l) noattr in
      Sbuiltin (Some id) (EF_vload chunk) (Tcons typtr Tnil) ((Eaddrof l typtr):: nil) *)
  end.

FDefinition transl_valof (ty: type) (l: expr) : mon (list T.stmt * T.expr) :=
  if type_is_volatile ty
  then do t <- gensym ty;
       do bf <- is_bitfield_access l;
       ret (make_set bf t l :: nil, Etempvar t ty)
  else ret (nil, l).

FRecursion transl_expr.
Case Evalof l ty := 
(fun dst => 
   do (sl1, a1) <- transl_expr For_val l;
   do (sl2, a2) <- transl_valof (S.typeof l) a1;
   ret (finish dst (sl1 ++ sl2) a2))

Family C extends 
  C_Evalof,
  C_Ederef,
  C_Eaddrof.
FEnd C.

(* Csharpminor/Cminor *)
Inductive expr : Type :=
| Eaddrof : ident -> expr(* taking the address of a variable *)
| Eload : memory_chunk -> expr -> expr.(* memory read *)
                               
Inductive stmt : Type :=
| Sstore : memory_chunk -> expr -> expr -> stmt.

(*CminorSel *)
Inductive expr : Type :=
| Eload : memory_chunk -> addressing -> exprlist -> expr
| Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt. 

(*RTL*)
Inductive instruction: Type :=
| Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
| Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction

(* LTL *)
Inductive instruction: Type :=
| Lload (chunk: memory_chunk) (addr: addressing) (args: list mreg) (dst: mreg)
| Lstore (chunk: memory_chunk) (addr: addressing) (args: list mreg) (src: mreg)

(* Linear/Mach*)
Inductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
FEnd Comp_Heap.

Trait Comp_Field extends Comp_Base.
FEnd Comp_Field.

Trait Comp_Call extends Comp_Base.
FEnd Comp_Call.

(* small extension *)

(* requires work with cshmgen, selection, operation semantics *)
Trait Comp_Op extends Comp_Base.

Trait C_Ops extends C.
FEnd C_Ops.

Family Clight_Ops extends Clight.
FEnd Clight_Ops.

(* extended with ops *)
Family Op.
FEnd Op.

Family Selection_Ops extends Selection.
FEnd Selection_Ops.


Trait Asmgen_Ops extends Asmgen.

FRecursion transl_op.
FEnd transl_op.

FEnd Asmgen_Ops

FEnd Comp_op.

(* small extension: Only C, Clight *)
(* Struct/Union *)

(* small extension *)

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
