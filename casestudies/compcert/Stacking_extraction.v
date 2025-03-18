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

Trait Base.


Local Open Scope error_monad_scope.

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

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

From Rocqet Require Import Mregisters.

FEnd Mach.
   
(* Linear -> Mach *)
Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

From Rocqet Require Import Bounds.
(* Fields in bounds that depend on late bound names *)

FRecursion record_regs_of_instr about S.instruction motive
  (fun (_ : S.instruction) => Bounds.RegSet.t -> Bounds.RegSet.t) by _rect.
Case Lreturn := (fun u => u).
Case Lgetstack sl ofs ty r := (fun u => record_reg u r).
Case Lsetstack r sl ofs ty := (fun u => record_reg u r).
Case Lop op args res := (fun u => record_reg u res).
Case Llabel lbl := (fun u => u). 
Case Lgoto lbl := (fun u => u).
Case Lcond cond args lbl := (fun u => u). 
FEnd record_regs_of_instr.

FDefinition record_regs_of_function : S.function -> Bounds.RegSet.t := fun f =>
  fold_left (fun u i => record_regs_of_instr i u) (S.fn_code f) Bounds.RegSet.empty.

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

From Rocqet Require Import Stacklayout.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

FDefinition offset_arg := fun (x: Z) => fe_ofs_arg + 4 * x.

FDefinition transl_op := fun (fe: frame_env) (op: Op.operation) =>
    Op.shift_stack_operation fe.(fe_stack_data) op.

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

FEnd Base.

Trait Comp_Loops extends Base.

Family Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.
FEnd Lfam.

Trait Stacking_jumptable extends Stacking.

FRecursion record_regs_of_instr.
Case Ljumptable arg tbl := (fun u => u).
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

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Linear.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction.
FEnd Linear.

Family Mach.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction.
FEnd Mach.

Family Stacking.

FRecursion record_regs_of_instr.
Case _ := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

MetaData transl_builtin_arg.
Fixpoint transl_builtin_arg (fe: frame_env) (a: builtin_arg loc) : builtin_arg mreg :=
  match a with
  | BA (R r) => BA r
  | BA (S Local ofs ty) =>
      BA_loadstack (chunk_of_type ty) (Ptrofs.repr (self__Stacking.offset_local fe ofs))
  | BA (S _ _ _) => BA_int Int.zero(* never happens *)
  | BA_int n => BA_int n
  | BA_long n => BA_long n
  | BA_float n => BA_float n
  | BA_single n => BA_single n
  | BA_loadstack chunk ofs =>
      BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr fe.(fe_stack_data)))
  | BA_addrstack ofs =>
      BA_addrstack (Ptrofs.add ofs (Ptrofs.repr fe.(fe_stack_data)))
  | BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
  | BA_addrglobal id ofs => BA_addrglobal id ofs
  | BA_splitlong hi lo =>
      BA_splitlong (transl_builtin_arg fe hi) (transl_builtin_arg fe lo)
  | BA_addptr a1 a2 =>
      BA_addptr (transl_builtin_arg fe a1) (transl_builtin_arg fe a2)
  end.
FEnd transl_builtin_arg.

FRecursion transl_instr.
Case Lbuiltin ef args dst := (fun fe k => T.Lbuiltin ef (map (transl_builtin_arg fe) args) dst :: k).
FEnd transl_instr.

FEnd Stacking.


FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.
FEnd Lfam.

Family Linear extends Lfam. FEnd Linear.
Family Mach extends Lfam. FEnd Mach.

Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

FRecursion record_regs_of_instr.
Case Lload chunk addr args dst := (fun u => record_reg u dst).
Case Lstore chunk addr args src := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FDefinition transl_addr := fun (fe: frame_env) (addr: addressing) =>
  shift_stack_addressing fe.(fe_stack_data) addr.

FRecursion transl_instr.
Case Lload chunk addr args dst :=
 (fun fe k => T.Lload chunk (transl_addr fe addr) args dst :: k).
Case Lstore chunk addr args src := 
 (fun fe k => T.Lstore chunk (transl_addr fe addr) args src :: k).
FEnd transl_instr.

FEnd Stacking.

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
Family Mach extends Lfam. FEnd Mach.

Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

FRecursion record_regs_of_instr.
Case _ := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FRecursion transl_instr.
Case Lcall sig ros :=
 (fun fe k => T.Lcall sig ros :: k).
Case Ltailcall sig ros :=
  (fun fe k => restore_callee_save fe (T.Ltailcall sig ros :: k)).
FEnd transl_instr.

FEnd Stacking.

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
  Comp_Builtin.

Family Stacking.
Final Family S := Linear.
Final Family T := Mach.
FEnd Stacking.

FEnd Comp.

Require Extraction.

Cd "extraction".

(* Go! *)
Separate Extraction Comp.Stacking.
