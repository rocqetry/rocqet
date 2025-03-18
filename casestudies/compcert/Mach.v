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

Require Import Lfam.

Local Open Scope error_monad_scope.

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

Trait Base.

Family Mach extends Lfam.

FInductive instruction: Type :=
| Lgetstack: ptrofs -> typ -> mreg -> instruction
| Lgetparam: ptrofs -> typ -> mreg -> instruction
| Lsetstack: mreg -> ptrofs -> typ -> instruction.

Inherit code.
        
MetaData fn binds fn_sig, fn_code, fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_code: self__Mach.code;
  fn_stacksize: Z;
  fn_link_ofs: ptrofs;
  fn_retaddr_ofs: ptrofs 
}.
FEnd fn.

FOverride Definition function := fn.

Inherit genv.

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

FDefinition regset := Regmap.t val.

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

FRecursion is_label.
Case Lgetstack ptr t dst := (fun lbl => false).
Case Lsetstack ptr i dst := (fun lbl => false).
Case Lgetparam ptr i dst := (fun lbl => false).
FEnd is_label.

Inherit find_label.

FDefinition load_stack := fun (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) =>
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

FDefinition store_stack := fun (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) =>
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

MetaData undef_regs.
Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.
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
    forall ge s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      find_label lbl (self__Mach.fn_code f) = Some c' ->
      step ge (State s fb sp (Lgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)        
| exec_Lop:
    forall ge s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step ge (State s f sp (Lop op args res :: c) rs m)
        E0 (State s f sp c rs' m)        
| exec_Lcond_true:
    forall ge s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      find_label lbl (self__Mach.fn_code f) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step ge (State s fb sp (Lcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)        
| exec_Lcond_false:
    forall ge s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step ge (State s f sp (Lcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)        
| exec_return:
    forall ge s f sp ra c rs m,
      step ge (Returnstate (Stackframe f sp ra c :: s) rs m)
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
        E0 (Returnstate s rs m').

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
FEnd final_state.

FEnd Mach.

FEnd Base.

Trait Comp_Loops extends Base.

Family Mach extends Lfam.
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

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Mach.
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

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Mach extends Lfam.
FInductive step: genv -> state -> trace -> state -> Prop :=
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
FEnd Mach.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Mach.
FEnd Mach.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Mach extends Lfam.

Inherit genv.

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

(* To be provided by Asmgen *)
(* In CompCert, `return_address_offset` is a parameter to step *)
(* Here we (ab)use(?) the implicit self parameterization of family polymorphism to make it a parameter *)
FOpaque Definition return_address_offset: function -> code -> ptrofs -> Prop := cheat.

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
        E0 (Callstate s f' rs m').
FEnd Mach.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family Mach.
FEnd Mach.

FEnd Comp_Switch.

(*
Family Comp extends
  Comp_Heap,             
  Base,
  Comp_Switch,
  Comp_Loops,  
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin.

FEnd Comp.*)
