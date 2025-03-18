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

Require Import LfamBase.

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

Trait Base.

Family Linear extends Lfam.
FInductive instruction: Type :=
| Lgetstack: slot -> Z -> typ -> mreg -> instruction
| Lsetstack: mreg -> slot -> Z -> typ -> instruction.

Inherit code.

MetaData fn binds fn_sig, fn_code, fn_stacksize.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: self__Linear.code
}.
FEnd fn.

FOverride Definition function := fn.

Inherit genv.
FDefinition locset := Locmap.t.

MetaData stackframe binds Stackframe.
Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (rs: locset)(* location state in calling function *)
             (c: code),(* program point in calling function *)
      stackframe.
FEnd stackframe.

MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State:
      forall (stack: list stackframe)(* call stack *)
             (f: function)(* function currently executing *)
             (sp: val)(* stack pointer *)
             (c: code)(* current program point *)
             (rs: locset)(* location state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)(* call stack *)
             (f: fundef)(* function to call *)
             (rs: locset)(* location state at point of call *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)(* call stack *)
             (rs: locset)(* location state at point of return *)
             (m: mem),(* memory state *)
      state.
FEnd state.

FRecursion is_label.
Case Lgetstack s i t dst := (fun lbl => false).
Case Lsetstack d s i t := (fun lbl => false).
FEnd is_label.

(* meant to be in linear *)
FInduction is_label_correct about instruction
  motive (fun (instr: instruction) => forall lbl,
              if is_label instr lbl then instr = Llabel lbl else instr <> Llabel lbl).
FProof.
+ intros. fsimpl. apply cheat. (* fdiscriminate *)
+ intros. fsimpl. apply cheat. (* fdiscriminate *)
+ intros. fsimpl. case (peq lbl l); intro. (* finjective *) apply cheat. (* fdiscriminate*) apply cheat.
+ intros. apply cheat. (* fdiscriminate *)
+ intros. apply cheat. (* fdiscriminate *)
+ intros. fsimpl. apply cheat.
+ intros. fsimpl. apply cheat.
Qed. FEnd is_label_correct.

FDefinition undef_caller_save_regs : locset -> locset := fun ls => 
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then ls (R r) else Vundef
    | S Outgoing ofs ty => Vundef
    | S sl ofs ty => ls (S sl ofs ty)
    end.

FDefinition destroyed_by_getstack : slot -> list mreg := fun s => 
  match s with
  | Incoming => temp_for_parent_frame :: nil
  | _ => nil
  end.

FDefinition parent_locset := fun stack => 
  match stack with
  | nil => Locmap.init Vundef
  | self__Linear.Stackframe f sp ls c :: stack' => ls
  end.

FDefinition call_regs : locset -> locset := fun caller => 
  fun (l: loc) =>
    match l with
    | R r => caller (R r)
    | S Local ofs ty => Vundef
    | S Incoming ofs ty => caller (S Outgoing ofs ty)
    | S Outgoing ofs ty => Vundef
    end.

FDefinition return_regs : locset -> locset -> locset := fun caller callee => 
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then caller (R r) else callee (R r)
    | S Outgoing ofs ty => Vundef
    | S sl ofs ty => caller (S sl ofs ty)
    end.

Inherit find_label.

FDefinition reglist : locset -> list mreg -> list val := fun rs rl => 
  List.map (fun r => rs (R r)) rl.

MetaData undef_regs.
Fixpoint undef_regs (rl: list mreg) (rs: locset) : locset :=
  match rl with
  | nil => rs
  | r1 :: rl => Locmap.set (R r1) Vundef (undef_regs rl rs)
  end.
FEnd undef_regs.

FInductive step: genv -> state -> trace -> state -> Prop :=          
| exec_Llabel:
    forall ge s f sp lbl b rs m,
    step ge (State s f sp (Llabel lbl :: b) rs m)
      E0 (State s f sp b rs m)
| exec_Lgoto:
    forall ge s f sp lbl b rs m b',
      find_label lbl (self__Linear.fn_code f) = Some b' ->
      step ge (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)        
| exec_Lop:
    forall ge s f sp op args res b rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step ge (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b rs' m)      
| exec_Lcond_true:
    forall ge s f sp cond args lbl b rs m rs' b',
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl (self__Linear.fn_code f) = Some b' ->
      step ge (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' rs' m)      
| exec_Lcond_false:
    forall ge s f sp cond args lbl b rs m rs',
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step ge (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b rs' m)
| exec_return:
      forall ge s f sp rs0 c rs m,
      step ge (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m)
| exec_Lgetstack:
   forall ge s f sp sl ofs ty dst b rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      step ge (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
        E0 (State s f sp b rs' m)
| exec_Lsetstack:
   forall ge s f sp src sl ofs ty b rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      step ge (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
        E0 (State s f sp b rs' m)
| exec_function_internal:
    forall ge s f rs m rs' m' stk,
      Mem.alloc m 0 (self__Linear.fn_stacksize f) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step ge (Callstate s (AST.Internal f) rs m)
        E0 (State s f (Vptr stk Ptrofs.zero) (self__Linear.fn_code f) rs' m')
| exec_Lreturn:
      forall ge s f stk b rs m m',
      Mem.free m stk 0 (self__Linear.fn_stacksize f) = Some m' ->
      step ge (State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m').

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__Linear.funsig f = signature_main ->
    initial_state p (Callstate nil f (Locmap.init Vundef) m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall rs m retcode,
    Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
    final_state (Returnstate nil rs m) retcode.
FEnd final_state.

FEnd Linear.

FEnd Base.

Trait Comp_Loops extends Base.

Family Linear extends Lfam.

FInduction is_label_correct.
FProof.
+ intros. fsimpl. apply cheat. (* fdiscriminate *)
Qed. FEnd is_label_correct.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ljumptable:
      forall ge s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl (fn_code f) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step ge (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' rs' m).        
FEnd Linear.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Linear extends Lfam.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FInduction is_label_correct.
FProof.
+ intros. fsimpl. apply cheat. (* fdiscriminate *)
Qed. FEnd is_label_correct.

FDefinition undef_caller_save_regs : locset -> locset := fun ls =>
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then ls (R r) else Vundef
    | S Outgoing ofs ty => Vundef
    | S sl ofs ty => ls (S sl ofs ty)
    end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin:
      forall ge s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (State s f sp (Lbuiltin ef args res :: b) rs m)
        t (State s f sp b rs' m')
| exec_function_external:
      forall ge s ef args res rs1 rs2 m t m',
      args = map (fun p => Locmap.getpair p rs1) (loc_arguments (ef_sig ef)) ->
      external_call ef (Genv.to_senv ge) args m t res m' ->
      rs2 = Locmap.setpair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs1) ->
      step ge (Callstate s (AST.External ef) rs1 m)
         t (Returnstate s rs2 m').
FEnd Linear.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Linear extends Lfam.

FInduction is_label_correct.
FProof.
+ intros. fsimpl. apply cheat. (* fdiscriminate *)
+ intros. fsimpl. apply cheat. (* fdiscriminate *)  
Qed. FEnd is_label_correct.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lload:
      forall ge s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step ge (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b rs' m)
| exec_Lstore:
      forall ge s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step ge (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs' m').

FEnd Linear.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Linear extends Lfam.
FEnd Linear.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Linear extends Lfam.
Inherit locset.

FDefinition find_function := fun (ge: genv) (ros: mreg + ident) (rs: locset) =>
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

FInduction is_label_correct.
FProof.
+ intros. fsimpl. apply cheat. (* fdiscriminate *)
+ intros. fsimpl. apply cheat. (* fdiscriminate *)  
Qed. FEnd is_label_correct.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lcall:
      forall ge s f sp sig ros b rs m f',
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      step ge (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) f' rs m)
| exec_Ltailcall:
      forall ge s f stk sig ros b rs m rs' f' m',
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 (fn_stacksize f) = Some m' ->
      step ge (State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s f' rs' m').
FEnd Linear.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family Linear extends Lfam.
FEnd Linear.

FEnd Comp_Switch.

(*Family Comp extends
  Comp_Heap,             
  Base,
  Comp_Switch,
  Comp_Loops,  
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin.

FEnd Comp.*)

