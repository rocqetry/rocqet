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

(*Require Import LfamBase.
Require Import Linear.
Require Import Mach.*)

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

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

FDefinition genv := Genv.t fundef unit.

FRecursion is_label about instruction motive (fun (_ : instruction) => label -> bool) by _rect.
Case Lop op arg dst := (fun lbl => false).
Case Lcond c args l := (fun lbl => false).
Case Llabel lbl' := (fun lbl => if peq lbl lbl' then true else false).
Case Lgoto lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false).
FEnd is_label.

MetaData find_label.
Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label i1 lbl then Some il else find_label lbl il
  end.
FEnd find_label.

FEnd Lfam.

(*Family Lfam.
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

FDefinition genv := Genv.t fundef unit.
(* regset/locset *)
FOpaque Definition storeset : Type := cheat.
(* function/block *)
FOpaque Definition func_ptr : Type := cheat.
FOpaque Definition call_func_ptr : Type := cheat.
(* return address / locset *)
FOpaque Definition stack_state : Type := cheat.

MetaData stackframe binds Stackframe.
Inductive stackframe : Type :=
| Stackframe:
    forall (f: self__Lfam.func_ptr)(* calling function *)
           (sp: val)(* stack pointer in calling function *)
           (ls: self__Lfam.stack_state)(* location state in calling function *)
           (bb: self__Lfam.code), (* program point in calling function *)
      stackframe.
FEnd stackframe.

MetaData state binds State, Callstate, Returnstate.
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
    step ge (State s f sp (Llabel lbl :: b) rs m)
      E0 (State s f sp b rs m)
| exec_Lgoto:
    forall ge s fb f sp lbl b rs m b',
    find_func_ptr ge fb = Some (AST.Internal f) ->
    find_label lbl (function_code f) = Some b' ->
    step ge (State s fb sp (Lgoto lbl :: b) rs m)
      E0 (State s fb sp b' rs m)
| exec_Lop:
    forall ge s f sp op args res b rs m v rs',
    eval_operation ge sp op (reglist rs args) m = Some v ->
    rs' = set_storeset res v (undef_regs (destroyed_by_op op) rs) ->
    step ge (State s f sp (Lop op args res :: b) rs m)
      E0 (State s f sp b rs' m)
| exec_Lcond_true:
    forall ge s (fb: func_ptr) (f: function) sp cond args lbl b rs m rs' b',
    eval_condition cond (reglist rs args) m = Some true ->
    rs' = undef_regs (destroyed_by_cond cond) rs ->
    find_func_ptr ge fb = Some (AST.Internal f) ->
    find_label lbl (function_code f) = Some b' ->
    step ge (State s fb sp (Lcond cond args lbl :: b) rs m)
      E0 (State s fb sp b' rs' m)
| exec_Lcond_false:
    forall ge s f sp cond args lbl b rs m rs',
    eval_condition cond (reglist rs args) m = Some false ->
    rs' = undef_regs (destroyed_by_cond cond) rs ->
    step ge (State s f sp (Lcond cond args lbl :: b) rs m)
      E0 (State s f sp b rs' m)
| exec_return:
      forall ge s f sp rs0 c rs m,
      step ge (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m).

FEnd Lfam.*)

Family Linear extends Lfam.
FInductive instruction: Type :=
| Lgetstack: slot -> Z -> typ -> mreg -> instruction
| Lsetstack: mreg -> slot -> Z -> typ -> instruction.

Inherit code.

MetaData fn binds fn_sig, fn_code, fn_stacksize.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_sig := fn_sig.

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
      find_label lbl (fn_code f) = Some b' ->
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
      find_label lbl (fn_code f) = Some b' ->
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
      Mem.alloc m 0 (fn_stacksize f) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step ge (Callstate s (AST.Internal f) rs m)
        E0 (State s f (Vptr stk Ptrofs.zero) (fn_code f) rs' m')
| exec_Lreturn:
      forall ge s f stk b rs m m',
      Mem.free m stk 0 (fn_stacksize f) = Some m' ->
      step ge (State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m').

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->
    initial_state p (Callstate nil f (Locmap.init Vundef) m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall rs m retcode,
    Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
    final_state (Returnstate nil rs m) retcode.
FEnd final_state.

FEnd Linear.

Family Mach extends Lfam.

FInductive instruction: Type :=
| Lgetstack: ptrofs -> typ -> mreg -> instruction
| Lgetparam: ptrofs -> typ -> mreg -> instruction
| Lsetstack: mreg -> ptrofs -> typ -> instruction.

Inherit code.

MetaData fn binds fn_sig, fn_code, fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_code: code;
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

MetaData undef_regs binds undef_regs_other.
Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite Regmap.gso. apply IHrl. intuition. intuition.
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
    forall ge s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      find_label lbl (fn_code f) = Some c' ->
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
      find_label lbl (fn_code f) = Some c' ->
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

(* Linear -> Mach *)
Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

(* Lineartyping *)
From Rocqet Require Import Conventions.

FDefinition slot_valid := fun funct (sl: slot) (ofs: Z) (ty: typ) =>
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (Locations.S Incoming ofs ty) (regs_of_rpairs (loc_parameters (S.fn_sig funct)))
  end
  && Zdivide_dec (typealign ty) ofs.

FDefinition slot_writable := fun (sl: slot) =>
  match sl with
  | Local => true
  | Outgoing => true
  | Incoming => false
  end.

FDefinition loc_valid := fun funct l =>
  match l with
  | R r => true
  | S Local ofs ty => slot_valid funct Local ofs ty
  | S _ _ _ => false
  end.

MetaData  wt_builtin_res.
Fixpoint wt_builtin_res (ty: typ) (res: builtin_res mreg) : bool :=
  match res with
  | BR r => subtype ty (mreg_type r)
  | BR_none => true
  | BR_splitlong hi lo => wt_builtin_res AST.Tint hi && wt_builtin_res AST.Tint lo
  end.
FEnd wt_builtin_res.

FRecursion wt_instr about S.instruction motive (fun (_ : S.instruction) => S.function -> bool) by _rect.
Case Lgetstack sl ofs ty r := (fun funct => subtype ty (mreg_type r) && slot_valid funct sl ofs ty).
Case Lsetstack r sl ofs ty := (fun funct => slot_valid funct sl ofs ty && slot_writable sl).
Case Lop op args res :=
  (fun funct =>
     match is_move_operation op args with
      | Some arg =>
          subtype (mreg_type arg) (mreg_type res)
      | None =>
          let (targs, tres) := type_of_operation op in
          subtype tres (mreg_type res)
     end).
Case _ := (fun _ => true).
FEnd wt_instr.

FDefinition wt_code := fun (f: S.function) (c: S.code) =>
   forallb (fun i => wt_instr i f) c.
FDefinition wt_function := fun (f: S.function) =>
  wt_code f (S.fn_code f).

FDefinition wt_locset : S.locset -> Prop := fun ls =>
  forall l, Val.has_type (ls l) (Loc.type l).

FLemma wt_setreg:
  forall ls r v,
  Val.has_type v (mreg_type r) -> wt_locset ls -> wt_locset (Locmap.set (R r) v ls).
FProofLemma.
  intros; red; intros.
  unfold Locmap.set.
  destruct (Loc.eq (R r) l).
  subst l; auto.
  destruct (Loc.diff_dec (R r) l). auto. red. auto.
Qed. CloseFLemma.

FLemma wt_setstack:
  forall ls sl ofs ty v,
  wt_locset ls -> wt_locset (Locmap.set (Locations.S sl ofs ty) v ls).
FProofLemma.
  intros; red; intros.
  unfold Locmap.set.
  destruct (Loc.eq (S sl ofs ty) l).
  subst l. simpl.
  generalize (Val.load_result_type (chunk_of_type ty) v).
  replace (type_of_chunk (chunk_of_type ty)) with ty. auto.
  destruct ty; reflexivity.
  destruct (Loc.diff_dec (S sl ofs ty) l). auto. red. auto.
Qed. CloseFLemma.

FLemma wt_undef_regs:
  forall rs ls, wt_locset ls -> wt_locset (S.undef_regs rs ls).
FProofLemma.
  induction rs; simpl; intros. auto. apply wt_setreg; auto. red; auto.
Qed. CloseFLemma.

FLemma wt_call_regs:
  forall ls, wt_locset ls -> wt_locset (S.call_regs ls).
FProofLemma.
  intros; red; intros. unfold S.call_regs. destruct l. auto.
  destruct sl.
  red; auto.
  change (Loc.type (Locations.S Incoming pos ty)) with (Loc.type (Locations.S Outgoing pos ty)). auto.
  red; auto.
Qed. CloseFLemma.

FLemma wt_return_regs:
  forall caller callee,
  wt_locset caller -> wt_locset callee -> wt_locset (S.return_regs caller callee).
FProofLemma.
  intros; red; intros.
  unfold S.return_regs. destruct l.
- destruct (is_callee_save r); auto.
- destruct sl; auto; red; auto.
Qed. CloseFLemma.

FLemma wt_undef_caller_save_regs:
  forall ls, wt_locset ls -> wt_locset (S.undef_caller_save_regs ls).
FProofLemma.
  intros; red; intros. unfold S.undef_caller_save_regs.
  destruct l.
  destruct (is_callee_save r); auto; simpl; auto.
  destruct sl; auto; red; auto.
Qed. CloseFLemma.

FLemma wt_init:
  wt_locset (Locmap.init Vundef).
FProofLemma.
  red; intros. unfold Locmap.init. red; auto.
Qed. CloseFLemma.

FLemma wt_setpair:
  forall sg v rs,
  Val.has_type v (proj_sig_res sg) ->
  wt_locset rs ->
  wt_locset (Locmap.setpair (loc_result sg) v rs).
FProofLemma.
  intros. generalize (loc_result_pair sg) (loc_result_type sg).
  destruct (loc_result sg); simpl Locmap.setpair.
- intros. apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- intros A B. decompose [and] A.
  apply wt_setreg. eapply Val.has_subtype; eauto. destruct v; exact I.
  apply wt_setreg. eapply Val.has_subtype; eauto. destruct v; exact I.
  auto.
Qed. CloseFLemma.

FLemma wt_setres:
  forall res ty v rs,
  wt_builtin_res ty res = true ->
  Val.has_type v ty ->
  wt_locset rs ->
  wt_locset (Locmap.setres res v rs).
FProofLemma.
  induction res; simpl; intros.
- apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- auto.
- InvBooleans. eapply IHres2; eauto. destruct v; exact I.
  eapply IHres1; eauto. destruct v; exact I.
Qed. CloseFLemma.

FLemma wt_find_label:
  forall f lbl c,
  wt_function f = true ->
  S.find_label lbl (S.fn_code f) = Some c ->
  wt_code f c = true.
FProofLemma.
  unfold wt_function; intros until c. generalize (S.fn_code f). induction c0; simpl; intros.
  discriminate.
  InvBooleans. destruct (S.is_label a lbl).
  congruence.
  auto.
Qed. CloseFLemma.

FDefinition agree_outgoing_arguments := fun (sg: signature) (ls pls: S.locset) =>
  forall ty ofs,
  In (Locations.S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
  ls (Locations.S Outgoing ofs ty) = pls (Locations.S Outgoing ofs ty).

FDefinition outgoing_undef : S.locset -> Prop := fun ls =>
  forall ty ofs, ls (Locations.S Outgoing ofs ty) = Vundef.

FDefinition wt_fundef := fun (fd: S.fundef) =>
  match fd with
  | AST.Internal f => wt_function f = true
  | AST.External ef => True
  end.

MetaData wt_callstack binds wt_callstack_nil, wt_callstack_cons.
Inductive wt_callstack: list S.stackframe -> Prop :=
  | wt_callstack_nil:
      wt_callstack nil
  | wt_callstack_cons: forall f sp rs c s
        (WTSTK: wt_callstack s)
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs),
      wt_callstack (S.Stackframe f sp rs c :: s).
FEnd wt_callstack.

FLemma wt_parent_locset:
  forall s, wt_callstack s -> wt_locset (S.parent_locset s).
FProofLemma.
  induction 1; simpl.
- apply wt_init.
- auto.
Qed. CloseFLemma.

MetaData wt_state.
Inductive wt_state: S.state -> Prop :=
  | wt_regular_state: forall s f sp c rs m
        (WTSTK: wt_callstack s )
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs),
      wt_state (S.State s f sp c rs m)
  | wt_call_state: forall s fd rs m
        (WTSTK: wt_callstack s)
        (WTFD: wt_fundef fd)
        (WTRS: wt_locset rs)
        (AGCS: agree_callee_save rs (S.parent_locset s))
        (AGARGS: agree_outgoing_arguments (S.funsig fd) rs (S.parent_locset s)),
      wt_state (S.Callstate s fd rs m)
  | wt_return_state: forall s rs m
        (WTSTK: wt_callstack s)
        (WTRS: wt_locset rs)
        (AGCS: agree_callee_save rs (S.parent_locset s))
        (UOUT: outgoing_undef rs),
      wt_state (S.Returnstate s rs m).
FEnd wt_state.

FLemma wt_state_getstack:
  forall s f sp sl ofs ty rd c rs m,
  wt_state (S.State s f sp (S.Lgetstack sl ofs ty rd :: c) rs m) ->
  slot_valid f sl ofs ty = true.
FProofLemma.
  intros. inv H. simpl in WTC; fsimpl in WTC; InvBooleans. auto.
Qed. CloseFLemma.

FLemma wt_state_setstack:
  forall s f sp sl ofs ty r c rs m,
  wt_state (S.State s f sp (S.Lsetstack r sl ofs ty :: c) rs m) ->
  slot_valid f sl ofs ty = true /\ slot_writable sl = true.
FProofLemma.
  intros. inv H. simpl in WTC; fsimpl in WTC; InvBooleans. intuition.
Qed. CloseFLemma.

FLemma wt_callstate_wt_regs:
  forall s f rs m,
  wt_state (S.Callstate s f rs m) ->
  forall r, Val.has_type (rs (R r)) (mreg_type r).
FProofLemma.
  intros. inv H. apply WTRS.
Qed. CloseFLemma.

FLemma wt_callstate_agree:
  forall s f rs m,
  wt_state (S.Callstate s f rs m) ->
  agree_callee_save rs (S.parent_locset s) /\ agree_outgoing_arguments (S.funsig f) rs (S.parent_locset s).
FProofLemma.
  intros. inv H; auto.
Qed. CloseFLemma.

FLemma wt_returnstate_agree:
  forall s rs m,
  wt_state (S.Returnstate s rs m) ->
  agree_callee_save rs (S.parent_locset s) /\ outgoing_undef rs.
FProofLemma.
  intros. inv H; auto.
Qed. CloseFLemma.

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

FLemma max_over_list_pos:
  forall (A: Type) (valu: A -> Z) (l: list A),
  max_over_list valu l >= 0.
FProofLemma.
  intros until valu. unfold max_over_list.
  assert (forall l z, fold_left (fun x y => Z.max x (valu y)) l z >= z).
  induction l; simpl; intros.
  lia. apply Zge_trans with (Z.max z (valu a)).
  auto. apply Z.le_ge. apply Z.le_max_l. auto.
Qed. CloseFLemma.

FLemma max_over_slots_of_funct_pos:
  forall (valu: slot * Z * typ -> Z) f, max_over_slots_of_funct valu f >= 0.
FProofLemma.
  intros. unfold max_over_slots_of_funct.
  unfold max_over_instrs. apply max_over_list_pos.
Qed. CloseFLemma.

FLemma fold_left_preserves:
  forall (A B: Type) (f: A -> B -> A) (P: A -> Prop),
  (forall a b, P a -> P (f a b)) ->
  forall l a, P a -> P (fold_left f l a).
FProofLemma.
  induction l; simpl; auto.
Qed. CloseFLemma.

FLemma fold_left_ensures:
  forall (A B: Type) (f: A -> B -> A) (P: A -> Prop) b0,
  (forall a b, P a -> P (f a b)) ->
  (forall a, P (f a b0)) ->
  forall l a, In b0 l -> P (fold_left f l a).
FProofLemma.
  induction l; simpl; intros. contradiction.
  destruct H1. subst a. apply fold_left_preserves; auto. apply IHl; auto.
Qed. CloseFLemma.

FDefinition only_callee_saves : RegSet.t -> Prop :=
  fun u => forall r, RegSet.In r u -> is_callee_save r = true.

FLemma record_reg_only: forall u r, only_callee_saves u -> only_callee_saves (record_reg u r).
FProofLemma.
  unfold only_callee_saves, record_reg; intros.
  destruct (is_callee_save r) eqn:CS; auto.
  destruct (mreg_eq r r0). congruence. apply H; eapply RegSet.add_3; eauto.
Qed. CloseFLemma.

FLemma record_regs_only: forall rl u, only_callee_saves u -> only_callee_saves (record_regs u rl).
FProofLemma.
  intros. unfold record_regs. apply fold_left_preserves; auto using record_reg_only.
Qed. CloseFLemma.

FInduction record_regs_of_instr_only
  about S.instruction
  motive (fun (i : S.instruction) =>
    forall u, only_callee_saves u -> only_callee_saves (record_regs_of_instr i u)).
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FLemma record_regs_of_function_only:
  forall f, only_callee_saves (record_regs_of_function f).
FProofLemma.
  intros. unfold record_regs_of_function.
  apply fold_left_preserves. intros. apply record_regs_of_instr_only. auto.
  red; intros. eelim RegSet.empty_1; eauto.
Qed. CloseFLemma.

MetaData function_bounds.
Program Definition function_bounds (f: S.function) := {|
  used_callee_save := RegSet.elements (record_regs_of_function f);
  bound_local := max_over_slots_of_funct local_slot f;
  bound_outgoing := Z.max (max_over_instrs outgoing_space f) (max_over_slots_of_funct outgoing_slot f);
  bound_stack_data := Z.max (S.fn_stacksize f) 0
|}.
Next Obligation.
  apply max_over_slots_of_funct_pos.
Qed.
Next Obligation.
  apply Z.le_ge. eapply Z.le_trans. 2: apply Z.le_max_r.
  apply Z.ge_le. apply max_over_slots_of_funct_pos.
Qed.
Next Obligation.
  apply Z.le_ge. apply Z.le_max_r.
Qed.
Next Obligation.
  generalize (RegSet.elements_3w (record_regs_of_function f)).
  generalize (RegSet.elements (record_regs_of_function f)).
  induction 1. constructor. constructor; auto.
  red; intros; elim H. apply InA_alt. exists x; auto.
Qed.
Next Obligation.
  apply (record_regs_of_function_only f). apply RegSet.elements_2.
  apply InA_alt. exists r; auto.
Qed.
FEnd function_bounds.

From Rocqet Require Import Stacklayout.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

FDefinition offset_arg := fun (x: Z) => fe_ofs_arg + 4 * x.

FDefinition transl_op := fun (fe: frame_env) (op: Op.operation) =>
    Op.shift_stack_operation fe.(fe_stack_data) op.

MetaData save_callee_save_rec.
Fixpoint save_callee_save_rec (rl: list mreg) (ofs: Z) (k: T.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      T.Lsetstack r (Ptrofs.repr ofs1) ty :: save_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd save_callee_save_rec.

FDefinition save_callee_save := fun (fe: frame_env) (k: T.code) =>
  save_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

MetaData restore_callee_save_rec.
Fixpoint restore_callee_save_rec (rl: list mreg) (ofs: Z) (k: T.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      T.Lgetstack (Ptrofs.repr ofs1) ty r :: restore_callee_save_rec rl (ofs1 + sz) k
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
  if negb (wt_function f) then
    Error (msg "Ill-formed Linear code")
  else if zlt Ptrofs.max_unsigned fe.(fe_size) then
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

From Rocqet Require Import Separation Conventions.
Local Open Scope sep_scope.


FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

MetaData agree_locs.
Record agree_locs (f: S.function) (ls ls0: S.locset) : Prop :=
  mk_agree_locs {
    agree_unused_reg:
      forall r,
        let b := function_bounds f in
        ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);
    agree_incoming:
       forall ofs ty,
       In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters f.(S.fn_sig))) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)
}.
FEnd agree_locs.

(*
Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
*)
MetaData match_stacks.
Inductive match_stacks (ge: S.genv) (tge: T.genv) (j: meminj):
       list S.stackframe -> list T.stackframe -> signature -> Prop :=
  | match_stacks_empty: forall sg,
      tailcall_possible sg ->
      match_stacks ge tge j nil nil sg
  | match_stacks_cons: forall f sp ls c cs fb sp' ra c' cs' sg trf
        (TAIL: is_tail c (S.fn_code f))
        (FINDF: Genv.find_funct_ptr tge fb = Some (AST.Internal trf))
        (TRF: transf_function f = OK trf)
        (TRC: transl_code (make_env (function_bounds f)) c = c')
        (INJ: j sp = Some(sp', (fe_stack_data (make_env (function_bounds f)))))
        (TY_RA: Val.has_type ra Tptr)
        (AGL: agree_locs f ls (S.parent_locset cs))
        (ARGS: forall ofs ty,
           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
           slot_within_bounds (function_bounds f) Outgoing ofs ty)
        (STK: match_stacks ge tge j cs cs' (S.fn_sig f)),
      match_stacks ge tge j
                   (S.Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs)
                   (T.Stackframe fb (Vptr sp' Ptrofs.zero) ra c' :: cs')
                   sg.
FEnd match_stacks.

FDefinition agree_regs := fun (j: meminj) (ls: S.locset) (rs: T.regset) =>
  forall r, Val.inject j (ls (R r)) (rs r).

FLemma size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
FProofLemma.
  destruct ty; reflexivity.
Qed. CloseFLemma.

FLemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
FProofLemma.
  destruct ty; auto.
Qed. CloseFLemma.

MetaData contains_locations.
Program Definition contains_locations (j: meminj) (sp: block) (pos bound: Z) (sl: slot) (ls: S.locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos /\ pos + 4 * bound <= Ptrofs.modulus /\
    Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
    exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v
           /\ Val.inject j (ls (S sl ofs ty)) v;
  m_footprint := fun b ofs =>
    b = sp /\ pos <= ofs < pos + 4 * bound
|}.
Next Obligation.
  intuition auto.
- red; intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exploit H4; eauto. intros (v & A & B). exists v; split; auto.
  eapply Mem.load_unchanged_on; eauto.
  simpl; intros. rewrite size_type_chunk, typesize_typesize in H8.
  split; auto. destruct bound, ofs; lia.
Qed.
Next Obligation.
  eauto with mem.
Qed.
FEnd contains_locations.

MetaData contains_callee_saves.
Fixpoint contains_callee_saves (j: meminj) (sp: block) (pos: Z) (rl: list mreg) (ls: S.locset) : massert :=
  match rl with
  | nil => pure True
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let pos1 := align pos sz in
      contains (chunk_of_type ty) sp pos1 (fun v => Val.inject j (ls (R r)) v)
      ** contains_callee_saves j sp (pos1 + sz) rl ls
  end.
FEnd contains_callee_saves.

(* Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b. *)
FDefinition frame_contents_1 := fun (f: S.function) (j: meminj) (sp: block) (ls ls0: S.locset) (parent retaddr: val) =>
     let b := function_bounds f in
     let fe := make_env b in
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** contains_locations j sp fe_ofs_arg b.(bound_outgoing) Outgoing ls
 ** hasvalue Mptr sp fe.(fe_ofs_link) parent
 ** hasvalue Mptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

FDefinition frame_contents := fun (f: S.function) (j: meminj) (sp: block) (ls ls0: S.locset) (parent retaddr: val) =>
  let b := function_bounds f in
  let fe := make_env b in
  mconj (frame_contents_1 f j sp ls ls0 parent retaddr)
        (range sp 0 fe.(fe_stack_data) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

MetaData stack_contents.
Fixpoint stack_contents (j: meminj) (cs: list S.stackframe) (cs': list T.stackframe) : massert :=
  match cs, cs' with
  | nil, nil => pure True
  | self__Stacking.S.Stackframe f _ ls c :: cs, T.Stackframe fb (Vptr sp' _) ra c' :: cs' =>
      frame_contents f j sp' ls (S.parent_locset cs) (T.parent_sp cs') (T.parent_ra cs')
      ** stack_contents j cs cs'
  | _, _ => pure False
  end.
FEnd stack_contents.

MetaData match_states.
Inductive match_states (ge: S.genv) (tge: T.genv): S.state -> T.state -> Prop :=
  | match_states_intro:
      forall cs f sp c ls m cs' fb sp' rs m' j tf
        (STACKS: match_stacks ge tge j cs cs' (S.fn_sig f))
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (AST.Internal tf))
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_locs f ls (S.parent_locset cs))
        (INJSP: j sp = Some(sp', fe_stack_data (make_env (function_bounds f))))
        (TAIL: is_tail c (S.fn_code f))
        (SEP: m' |= frame_contents f j sp' ls (S.parent_locset cs) (T.parent_sp cs') (T.parent_ra cs')
                 ** stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states ge tge (S.State cs f (Vptr sp Ptrofs.zero) c ls m)
                   (T.State cs' fb (Vptr sp' Ptrofs.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall cs f ls m cs' fb rs m' j tf
        (STACKS: match_stacks ge tge j cs cs' (S.funsig f))
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (AGREGS: agree_regs j ls rs)
        (SEP: m' |= stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states ge tge (S.Callstate cs f ls m)
                   (T.Callstate cs' fb rs m')
  | match_states_return:
      forall cs ls m cs' rs m' j sg
        (STACKS: match_stacks ge tge j cs cs' sg)
        (AGREGS: agree_regs j ls rs)
        (SEP: m' |= stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states ge tge (S.Returnstate cs ls m)
                  (T.Returnstate cs' rs m').
FEnd match_states.

FLemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr i fe (transl_code fe c).
FProofLemma.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed. CloseFLemma.

FRecursion instr_within_bounds about S.instruction motive (fun (_ : S.instruction) =>  bounds -> Prop) by _rect.
Case Lgetstack sl ofs ty r := (fun b => slot_within_bounds b sl ofs ty /\ mreg_within_bounds b r).
Case Lsetstack r sl ofs ty := (fun b => slot_within_bounds b sl ofs ty).
Case Lop op args res := (fun b => mreg_within_bounds b res).
(* Case Lload chunk addr args dst := (fun b => mreg_within_bounds b dst). *)
(* Case Lcall sig ros := (fun b => size_arguments sig <= bound_outgoing b).*)
(*Case Lbuiltin ef args res :=
     (forall r, In r (params_of_builtin_res res) \/ In r (destroyed_by_builtin ef) -> mreg_within_bounds r)
  /\ (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args args) -> slot_within_bounds sl ofs ty)
  | _ => True
  end.*)
Case _ := (fun b => True).
FEnd instr_within_bounds.

FDefinition function_within_bounds := fun (f: S.function) (b: bounds) =>
  forall instr, In instr (S.fn_code f) -> instr_within_bounds instr b.

FRecursion defined_by_instr about S.instruction motive (fun (_ : S.instruction) => mreg -> Prop) by _rect.
Case Lgetstack sl ofs ty r := (fun r' => r' = r).
Case Lop op args res := (fun r' => r' = res).
(*| Lload chunk addr args dst => r' = dst
| Lbuiltin ef args res => In r' (params_of_builtin_res res) \/ In r' (destroyed_by_builtin ef)*)
Case _ := (fun r' => False).
FEnd defined_by_instr.

FLemma record_reg_incr: forall u r r', RegSet.In r' u -> RegSet.In r' (record_reg u r).
FProofLemma.
  unfold record_reg; intros. destruct (is_callee_save r); auto. apply RegSet.add_2; auto.
Qed. CloseFLemma.

FLemma record_regs_incr: forall r' rl u, RegSet.In r' u -> RegSet.In r' (record_regs u rl).
FProofLemma.
  intros. unfold record_regs. apply fold_left_preserves; auto using record_reg_incr.
Qed. CloseFLemma.

FInduction record_regs_of_instr_incr about S.instruction
  motive (fun (i: S.instruction) => forall r' u, RegSet.In r' u -> RegSet.In r' (record_regs_of_instr i u)).
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FLemma record_reg_ok: forall u r, is_callee_save r = true -> RegSet.In r (record_reg u r).
FProofLemma.
  unfold record_reg; intros. rewrite H. apply RegSet.add_1; auto.
Qed. CloseFLemma.

FInduction record_regs_of_instr_ok about S.instruction
  motive (fun (i: S.instruction) =>
    forall r' u,
    defined_by_instr i r' -> is_callee_save r' = true -> RegSet.In r' (record_regs_of_instr i u)).
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
(* destruct H; auto using record_regs_incr, record_regs_ok.*)
Qed. FEnd record_regs_of_instr_ok.

FLemma record_regs_of_function_ok:
  forall f r i, In i (S.fn_code f) -> defined_by_instr i r -> is_callee_save r = true -> RegSet.In r (record_regs_of_function f).
FProofLemma.
  intros. unfold record_regs_of_function.
  eapply fold_left_ensures.
  + intros. simple apply record_regs_of_instr_incr. exact H2.
  + intro. simple apply record_regs_of_instr_ok. exact H0. exact H1.
  + exact H.
Qed. CloseFLemma.

FLemma mreg_is_within_bounds:
  forall f i, In i (S.fn_code f) ->
  forall r, defined_by_instr i r ->
  mreg_within_bounds (function_bounds f) r.
FProofLemma.
  intros. unfold mreg_within_bounds. intros.
  exploit record_regs_of_function_ok; eauto. intros.
  apply RegSet.elements_1 in H2. rewrite InA_alt in H2. destruct H2 as (r' & A & B).
  subst r'; auto.
Qed. CloseFLemma.

FLemma max_over_list_bound:
  forall (A: Type) (valu: A -> Z) (l: list A) (x: A),
  In x l -> valu x <= max_over_list valu l.
FProofLemma.
  intros until x. unfold max_over_list.
  assert (forall c z,
            let f := fold_left (fun x y => Z.max x (valu y)) c z in
            z <= f /\ (In x c -> valu x <= f)).
    induction c; simpl; intros.
    split. lia. tauto.
    elim (IHc (Z.max z (valu a))); intros.
    split. apply Z.le_trans with (Z.max z (valu a)). apply Z.le_max_l. auto.
    intro H1; elim H1; intro.
    subst a. apply Z.le_trans with (Z.max z (valu x)).
    apply Z.le_max_r. auto. auto.
  intro. elim (H l 0); intros. auto.
Qed. CloseFLemma.

FLemma max_over_instrs_bound:
  forall f (valu: S.instruction -> Z) i,
  In i (S.fn_code f) -> valu i <= max_over_instrs valu f.
FProofLemma.
  intros. unfold max_over_instrs. apply max_over_list_bound; auto.
Qed. CloseFLemma.

FLemma max_over_slots_of_funct_bound:
  forall f (valu: slot * Z * typ -> Z) i s,
  In i (S.fn_code f) -> In s (slots_of_instr i) ->
  valu s <= max_over_slots_of_funct valu f.
FProofLemma.
  intros. unfold max_over_slots_of_funct.
  apply Z.le_trans with (max_over_slots_of_instr valu i).
  unfold max_over_slots_of_instr. apply max_over_list_bound. auto.
  apply max_over_instrs_bound. auto.
Qed. CloseFLemma.

FLemma local_slot_bound:
  forall f i ofs ty,
  In i (S.fn_code f) -> In (Local, ofs, ty) (slots_of_instr i) ->
  ofs + typesize ty <= bound_local (function_bounds f).
FProofLemma.
  intros.
  unfold function_bounds, bound_local.
  change (ofs + typesize ty) with (local_slot (Local, ofs, ty)).
  eapply max_over_slots_of_funct_bound; eauto.
Qed. CloseFLemma.

FLemma outgoing_slot_bound:
  forall f i ofs ty,
  In i (S.fn_code f) -> In (Outgoing, ofs, ty) (slots_of_instr i) ->
  ofs + typesize ty <= bound_outgoing (function_bounds f).
FProofLemma.
  intros. change (ofs + typesize ty) with (outgoing_slot (Outgoing, ofs, ty)).
  unfold function_bounds, bound_outgoing.
  apply Zmax_bound_r. eapply max_over_slots_of_funct_bound; eauto.
Qed. CloseFLemma.

FLemma slot_is_within_bounds:
  forall f i, In i (S.fn_code f) ->
  forall sl ty ofs, In (sl, ofs, ty) (slots_of_instr i) ->
  slot_within_bounds (function_bounds f) sl ofs ty.
FProofLemma.
  intros. unfold slot_within_bounds.
  destruct sl.
  eapply local_slot_bound; eauto.
  auto.
  eapply outgoing_slot_bound; eauto.
Qed. CloseFLemma.

FInduction instr_is_within_bounds about S.instruction motive
  (fun (i: S.instruction) => forall f,
       In i (S.fn_code f) ->
       instr_within_bounds i (function_bounds f)).
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
simpl; do 4 fsimpl; simpl; intros; auto.
Qed. FEnd instr_is_within_bounds.

FLemma function_is_within_bounds: forall f,
  function_within_bounds f (function_bounds f).
FProofLemma.
  intros; red; intros. apply instr_is_within_bounds; auto.
Qed. CloseFLemma.

FLemma unfold_transf_function: forall f tf (TRANSF_F: transf_function f = OK tf),
  let b := function_bounds f in
  let fe := make_env b in
  tf = T.mkfunction
         (S.fn_sig f)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr)).
FProofLemma.
  intros.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. (*unfold fe. unfold b.*) congruence.
  intros; discriminate.
Qed. CloseFLemma.

(* Preservation of code labels *)
FLemma find_label_save_callee_save:
  forall lbl l ofs k,
  T.find_label lbl (save_callee_save_rec l ofs k) = T.find_label lbl k.
FProofLemma.
  induction l; simpl.
  - auto.
  - intros. fsimpl. auto.
Qed. CloseFLemma.

FLemma find_label_restore_callee_save:
  forall lbl l ofs k,
  T.find_label lbl (restore_callee_save_rec l ofs k) = T.find_label lbl k.
FProofLemma.
  induction l; simpl.
  - auto.
  - intros. fsimpl. auto.
Qed. CloseFLemma.

FInduction find_label_transl_code_instr
  about S.instruction
  motive (fun (a : S.instruction) =>
    forall fe lbl c (IHc: T.find_label lbl (transl_code fe c) = option_map (transl_code fe) (S.find_label lbl c)),
    T.find_label lbl (transl_code fe (a :: c)) =
      option_map (transl_code fe)
        (if S.is_label a lbl then Some c else S.find_label lbl c)).
FProof.
all: intros; rewrite transl_code_eq; do 2 fsimpl; simpl; fsimpl; auto.
- destruct (peq lbl l). reflexivity. auto.
- unfold restore_callee_save. rewrite find_label_restore_callee_save. simpl. fsimpl. auto.
- destruct s; simpl; fsimpl; auto.
- destruct s; simpl; fsimpl; auto.
Qed. FEnd find_label_transl_code_instr.

FLemma find_label_transl_code:
  forall fe lbl c,
  T.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (S.find_label lbl c).
FProofLemma.
  induction c; simpl; intros.
- auto.
- apply find_label_transl_code_instr; auto.
Qed. CloseFLemma.

FLemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  S.find_label lbl (S.fn_code f) = Some c ->
  T.find_label lbl (T.fn_code tf) =
    Some (transl_code (make_env (function_bounds f)) c).
FProofLemma.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body. unfold save_callee_save. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed. CloseFLemma.

FLemma find_label_tail:
  forall lbl c c',
  S.find_label lbl c = Some c' -> is_tail c' c.
FProofLemma.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (S.is_label a lbl); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed. CloseFLemma.

FLemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> Val.inject j (ls (R r)) (rs r).
FProofLemma.
  intros. auto.
Qed. CloseFLemma.
FLemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> Val.inject_list j (S.reglist ls rl) (rs##rl).
FProofLemma.
  induction rl; simpl; intros.
  auto. constructor; auto using agree_reg.
Qed. CloseFLemma.
MetaData _agree.
Hint Resolve agree_reg agree_reglist: stacking.
FEnd _agree.

FLemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
FProofLemma.
  intros; red; intros.
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0.
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed. CloseFLemma.

FLemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (S.undef_regs rl ls) (T.undef_regs rl rs).
FProofLemma.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto.
Qed. CloseFLemma.

FLemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (S.call_regs ls) rs.
FProofLemma.
  intros.
  unfold S.call_regs; intros; red; intros; auto.
Qed. CloseFLemma.

FLemma agree_locs_set_reg:
  forall f ls ls0 r v,
  let b := function_bounds f in
  agree_locs f ls ls0 ->
  mreg_within_bounds b r ->
  agree_locs f (Locmap.set (R r) v ls) ls0.
FProofLemma.
  intros. inv H; constructor; auto; intros. subst b.
  rewrite Locmap.gso. auto. red. simpl in H0. intuition congruence.
Qed. CloseFLemma.

FLemma agree_locs_undef_regs:
  forall f ls0 regs ls,
  let b := function_bounds f in
  agree_locs f ls ls0 ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_locs f (S.undef_regs regs ls) ls0.
FProofLemma.
  induction regs; simpl; intros.
  auto.
  apply agree_locs_set_reg; auto.
Qed. CloseFLemma.

FLemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
FProofLemma.
  intros; red; intros; eauto with stacking.
Qed. CloseFLemma.

FLemma caller_save_reg_within_bounds:
  forall f r,
  let b := function_bounds f in
  is_callee_save r = false -> mreg_within_bounds b r.
FProofLemma.
  intros; red; intros. congruence.
Qed. CloseFLemma.

FLemma agree_locs_undef_locs_1:
  forall f ls0 regs ls,
  agree_locs f ls ls0 ->
  (forall r, In r regs -> is_callee_save r = false) ->
  agree_locs f (S.undef_regs regs ls) ls0.
FProofLemma.
  intros. eapply agree_locs_undef_regs; eauto.
  intros. apply caller_save_reg_within_bounds. auto.
Qed. CloseFLemma.

FLemma agree_locs_undef_locs:
  forall f ls0 regs ls,
  agree_locs f ls ls0 ->
  existsb is_callee_save regs = false ->
  agree_locs f (S.undef_regs regs ls) ls0.
FProofLemma.
  intros. eapply agree_locs_undef_locs_1; eauto.
  intros. destruct (is_callee_save r) eqn:CS; auto.
  assert (existsb is_callee_save regs = true).
  { apply existsb_exists. exists r; auto. }
  congruence.
Qed. CloseFLemma.

FLemma symbols_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_symbol_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma destroyed_by_setstack_function_entry:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_function_entry.
FProofLemma.
Local Transparent destroyed_by_setstack destroyed_at_function_entry.
  unfold incl; destruct ty; simpl; tauto.
Qed. CloseFLemma.

FLemma transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
FProofLemma.
  intros; destruct op; reflexivity.
Qed. CloseFLemma.

FDefinition no_callee_saves := fun l =>
  existsb is_callee_save l = false.

MetaData ByCases.
Ltac ByCases :=
  reflexivity ||
  match goal with
  | |- no_callee_saves (match ?x with _ => _ end) => destruct x; ByCases
  | _ => idtac
  end.
FEnd ByCases.

FLemma destroyed_by_op_caller_save:
  forall op, no_callee_saves (destroyed_by_op op).
FProofLemma.
(*Local Transparent destroyed_by_op.*)
  intros; unfold destroyed_by_op ; ByCases.
Qed. CloseFLemma.

FLemma destroyed_by_cond_caller_save:
  forall cond, no_callee_saves (destroyed_by_cond cond).
FProofLemma.
(*Local Transparent destroyed_by_cond.*)
  intros; unfold destroyed_by_cond; ByCases.
Qed. CloseFLemma.

FLemma contains_locations_exten:
  forall ls ls' j sp pos bound sl,
  (forall ofs ty, Val.lessdef (ls' (Locations.S sl ofs ty)) (ls (Locations.S sl ofs ty))) ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j sp pos bound sl ls').
FProofLemma.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; split; auto.
  specialize (H ofs ty). inv H. congruence. auto.
Qed. CloseFLemma.

FLemma contains_callee_saves_exten:
  forall j sp ls ls' rl pos,
  (forall r, In r rl -> ls' (R r) = ls (R r)) ->
  massert_eqv (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j sp pos rl ls').
FProofLemma.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_2; auto. rewrite H by auto. reflexivity.
Qed. CloseFLemma.

FLemma frame_contents_exten:
  forall f ls ls0 ls' ls0' j sp parent retaddr P m,
  let b := function_bounds f in
  (forall ofs ty, Val.lessdef (ls' (Locations.S Local ofs ty)) (ls (Locations.S Local ofs ty))) ->
  (forall ofs ty, Val.lessdef (ls' (Locations.S Outgoing ofs ty)) (ls (Locations.S Outgoing ofs ty))) ->
  (forall r, In r b.(used_callee_save) -> ls0' (R r) = ls0 (R r)) ->
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents f j sp ls' ls0' parent retaddr ** P.
FProofLemma.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- ! (contains_locations_exten ls ls') by auto.
  erewrite <- (contains_callee_saves_exten _ _ ls0 ls0') by eauto.
  assumption.
Qed. CloseFLemma.

FLemma frame_set_reg:
  forall f r v j sp ls ls0 parent retaddr m P,
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents f j sp (Locmap.set (R r) v ls) ls0 parent retaddr ** P.
FProofLemma.
  intros. apply frame_contents_exten with ls ls0; auto.
Qed. CloseFLemma.

FLemma frame_undef_regs:
  forall f j sp ls ls0 parent retaddr m P rl,
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents f j sp (S.undef_regs rl ls) ls0 parent retaddr ** P.
FProofLemma.
(*Local Opaque sepconj.*)
  induction rl; simpl; intros.
- auto.
- apply frame_set_reg; auto.
Qed. CloseFLemma.

Local Opaque Z.add Z.mul Z.divide.
FLemma get_location:
  forall m j sp pos bound sl ls ofs ty,
  m |= contains_locations j sp pos bound sl ls ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  exists v,
     T.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) = Some v
  /\ Val.inject j (ls (Locations.S sl ofs ty)) v.
FProofLemma.
  intros. destruct H as (D & E & F & G & H).
  exploit H; eauto. intros (v & U & V). exists v; split; auto.
  unfold T.load_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; auto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). lia.
Qed. CloseFLemma.

FLemma frame_get_outgoing:
  forall f ofs ty j sp ls ls0 parent retaddr m P,
  let b := function_bounds f in
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  exists v,
     T.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) = Some v
  /\ Val.inject j (ls (Locations.S Outgoing ofs ty)) v.
FProofLemma.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick2 in H.
  eapply get_location; eauto.
Qed. CloseFLemma.

FLemma frame_get_local:
  forall f ofs ty j sp ls ls0 parent retaddr m P,
  let b := function_bounds f in
  let fe := make_env b in
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  exists v,
     T.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) = Some v
  /\ Val.inject j (ls (Locations.S Local ofs ty)) v.
FProofLemma.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_proj1 in H.
  eapply get_location; eauto.
Qed. CloseFLemma.

FLemma agree_locs_return:
  forall f ls ls0 ls',
  agree_locs f ls ls0 ->
  agree_callee_save ls' ls ->
  agree_locs f ls' ls0.
FProofLemma.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite <- agree_incoming0 by auto. apply H0. congruence.
Qed. CloseFLemma.

FLemma slot_outgoing_argument_valid:
  forall f ofs ty sg,
  In (Locations.S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> slot_valid f Outgoing ofs ty = true.
FProofLemma.
  intros. exploit loc_arguments_acceptable_2; eauto. intros [A B].
  unfold slot_valid. unfold proj_sumbool.
  rewrite zle_true by lia.
  rewrite pred_dec_true by auto.
  auto.
Qed. CloseFLemma.

FLemma contains_get_stack:
  forall spec m ty sp ofs,
  m |= contains (chunk_of_type ty) sp ofs spec ->
  exists v, T.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v /\ spec v.
FProofLemma.
  intros. unfold T.load_stack.
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply loadv_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed. CloseFLemma.

FLemma hasvalue_get_stack:
  forall ty m sp ofs v,
  m |= hasvalue (chunk_of_type ty) sp ofs v ->
  T.load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v.
FProofLemma.
  intros. exploit contains_get_stack; eauto. intros (v' & A & B). congruence.
Qed. CloseFLemma.

FLemma frame_get_parent:
  forall f j sp ls ls0 parent retaddr m P,
  let fe := make_env (function_bounds f) in
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  T.load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_link)) = Some parent.
FProofLemma.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick3 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed. CloseFLemma.

FLemma align_type_chunk:
  forall ty, align_chunk (chunk_of_type ty) = 4 * Locations.typealign ty.
FProofLemma.
  destruct ty; reflexivity.
Qed. CloseFLemma.

FLemma valid_access_location:
  forall m sp pos bound ofs ty p,
  (8 | pos) ->
  Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Mem.valid_access m (chunk_of_type ty) sp (pos + 4 * ofs) p.
FProofLemma.
  intros; split.
- red; intros. apply Mem.perm_implies with Freeable; auto with mem.
  apply H0. rewrite size_type_chunk, typesize_typesize in H4. lia.
- rewrite align_type_chunk. apply Z.divide_add_r.
  apply Z.divide_trans with 8; auto.
  exists (8 / (4 * typealign ty)); destruct ty; reflexivity.
  apply Z.mul_divide_mono_l. auto.
Qed. CloseFLemma.

FLemma set_location:
  forall m j sp pos bound sl ls P ofs ty v v',
  m |= contains_locations j sp pos bound sl ls ** P ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Val.inject j v v' ->
  exists m',
     T.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) v' = Some m'
  /\ m' |= contains_locations j sp pos bound sl (Locmap.set (Locations.S sl ofs ty) v ls) ** P.
FProofLemma.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & G & H).
  edestruct Mem.valid_access_store as [m' STORE].
  eapply valid_access_location; eauto.
  assert (PERM: Mem.range_perm m' sp pos (pos + 4 * bound) Cur Freeable).
  { red; intros; eauto with mem. }
  exists m'; split.
- unfold T.store_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; eauto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). lia.
- simpl. intuition auto.
+ unfold Locmap.set.
  destruct (Loc.eq (Locations.S sl ofs ty) (Locations.S sl ofs0 ty0)); [|destruct (Loc.diff_dec (Locations.S sl ofs ty) (Locations.S sl ofs0 ty0))].
* (* same location *)
  inv e. rename ofs0 into ofs. rename ty0 into ty.
  exists (Val.load_result (chunk_of_type ty) v'); split.
  eapply Mem.load_store_similar_2; eauto. lia.
  apply Val.load_result_inject; auto.
* (* different locations *)
  exploit H; eauto. intros (v0 & X & Y). exists v0; split; auto.
  rewrite <- X; eapply Mem.load_store_other; eauto.
  destruct d. congruence. right. rewrite ! size_type_chunk, ! typesize_typesize. lia.
* (* overlapping locations *)
  destruct (Mem.valid_access_load m' (chunk_of_type ty0) sp (pos + 4 * ofs0)) as [v'' LOAD].
  apply Mem.valid_access_implies with Writable; auto with mem.
  eapply valid_access_location; eauto.
  exists v''; auto.
+ apply (m_invar P) with m; auto.
  eapply Mem.store_unchanged_on; eauto.
  intros i; rewrite size_type_chunk, typesize_typesize. intros; red; intros.
  eelim C; eauto. simpl. split; auto. lia.
Qed. CloseFLemma.

FLemma frame_set_local:
  forall f ofs ty v v' j sp ls ls0 parent retaddr m P,
  let b := function_bounds f in
  let fe := make_env b in
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     T.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) v' = Some m'
  /\ m' |= frame_contents f j sp (Locmap.set (Locations.S Local ofs ty) v ls) ls0 parent retaddr ** P.
FProofLemma.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc; intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0.
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  { intros. unfold T.store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc; exact B.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed. CloseFLemma.

FLemma frame_set_outgoing:
  forall f ofs ty v v' j sp ls ls0 parent retaddr m P,
  let b := function_bounds f in
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     T.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) v' = Some m'
  /\ m' |= frame_contents f j sp (Locmap.set (Locations.S Outgoing ofs ty) v ls) ls0 parent retaddr ** P.
FProofLemma.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc, sep_swap. intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0.
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  { intros. unfold T.store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc, sep_swap; eauto.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed. CloseFLemma.

FLemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (Locations.S sl ofs ty) v ls) rs.
FProofLemma.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed. CloseFLemma.

FLemma agree_locs_set_slot:
  forall f ls ls0 sl ofs ty v,
  agree_locs f ls ls0 ->
  slot_writable sl = true ->
  agree_locs f (Locmap.set (Locations.S sl ofs ty) v ls) ls0.
FProofLemma.
  intros. destruct H; constructor; intros.
- rewrite Locmap.gso; auto. red; auto.
- rewrite Locmap.gso; auto. red. left. destruct sl; discriminate.
Qed. CloseFLemma.

FLemma destroyed_by_setstack_caller_save:
  forall ty, no_callee_saves (destroyed_by_setstack ty).
FProofLemma.
  unfold no_callee_saves; destruct ty; reflexivity.
Qed. CloseFLemma.

FLemma contains_set_stack:
  forall (spec: val -> Prop) v spec1 m ty sp ofs P,
  m |= contains (chunk_of_type ty) sp ofs spec1 ** P ->
  spec (Val.load_result (chunk_of_type ty) v) ->
  exists m',
      T.store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) v = Some m'
  /\ m' |= contains (chunk_of_type ty) sp ofs spec ** P.
FProofLemma.
  intros. unfold T.store_stack.
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply storev_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed. CloseFLemma.

FLemma load_result_inject:
  forall j ty v v',
  Val.inject j v v' -> Val.has_type v ty -> Val.inject j v (Val.load_result (chunk_of_type ty) v').
FProofLemma.
  intros until v'; unfold Val.has_type, Val.load_result; destruct Archi.ptr64;
  destruct 1; intros; auto; destruct ty; simpl;
  try contradiction; try discriminate; econstructor; eauto.
Qed. CloseFLemma.

FLemma save_callee_save_rec_correct:
  forall tge j cs fb sp ls,
  (forall ty r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef) ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  forall k l pos rs m P,
  (forall r, In r l -> is_callee_save r = true) ->
  m |= range sp pos (size_callee_save_area_rec l pos) ** P ->
  agree_regs j ls rs ->
  exists rs', exists m',
     star T.step tge
        (T.State cs fb (Vptr sp Ptrofs.zero) (save_callee_save_rec l pos k) rs m)
     E0 (T.State cs fb (Vptr sp Ptrofs.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp pos l ls ** P
  /\ (forall ofs k p, Mem.perm m sp ofs k p -> Mem.perm m' sp ofs k p)
  /\ agree_regs j ls rs'.
FProofLemma.
  intros * ls_temp_undef wt_ls.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl contains_callee_saves; intros until P; intros CS SEP AG.
- exists rs, m.
  split. apply star_refl.
  split. rewrite sep_pure; split; auto. eapply sep_drop; eauto.
  split. auto.
  auto.
- simpl size_callee_save_area_rec in SEP.
  set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (pos1 := align pos sz) in *.
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (SZREC: pos1 + sz <= size_callee_save_area_rec l (pos1 + sz)) by (apply size_callee_save_area_rec_incr).
  assert (POS1: pos <= pos1) by (apply align_le; auto).
  assert (AL1: (align_chunk (chunk_of_type ty) | pos1)).
  { unfold pos1. apply Z.divide_trans with sz.
    unfold sz; rewrite <- size_type_chunk. apply align_size_chunk_divides.
    apply align_divides; auto. }
  apply range_drop_left with (mid := pos1) in SEP; [ | lia ].
  apply range_split with (mid := pos1 + sz) in SEP; [ | lia ].
  unfold sz at 1 in SEP. rewrite <- size_type_chunk in SEP.
  apply range_contains in SEP; auto.
  exploit (contains_set_stack (fun v' => Val.inject j (ls (R r)) v') (rs r)).
  eexact SEP.
  apply load_result_inject; [auto|apply wt_ls].
  clear SEP; intros (m1 & STORE & SEP).
  set (rs1 := T.undef_regs (destroyed_by_setstack ty) rs).
  assert (AG1: agree_regs j ls rs1).
  { red; intros. unfold rs1. destruct (In_dec mreg_eq r0 (destroyed_by_setstack ty)).
    erewrite ls_temp_undef by eauto. auto.
    rewrite T.undef_regs_other by auto. apply AG. }
  rewrite sep_swap in SEP.
  simpl in CS. exploit (IHl (pos1 + sz) rs1 m1); eauto.
  intros (rs2 & m2 & A & B & C & D).
  exists rs2, m2.
  split. eapply star_left; eauto. fconstructor. traceEq.
  split. rewrite sep_assoc, sep_swap. exact B.
  split. intros. apply C. unfold T.store_stack in STORE; simpl in STORE. eapply Mem.perm_store_1; eauto.
  auto.
Qed. CloseFLemma.

FLemma LTL_undef_regs_same:
  forall r rl ls, In r rl -> S.undef_regs rl ls (R r) = Vundef.
FProofLemma.
  induction rl; simpl; intros. contradiction.
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto.
  destruct (Loc.diff_dec (R a) (R r)); auto.
  apply IHrl. intuition congruence.
Qed. CloseFLemma.

FLemma LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> S.undef_regs rl ls (R r) = ls (R r).
FProofLemma.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition.
Qed. CloseFLemma.

FLemma LTL_undef_regs_slot:
  forall sl ofs ty rl ls, S.undef_regs rl ls (Locations.S sl ofs ty) = ls (Locations.S sl ofs ty).
FProofLemma.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto.
Qed. CloseFLemma.

FLemma undef_regs_type:
  forall ty l rl ls,
  Val.has_type (ls l) ty -> Val.has_type (S.undef_regs rl ls l) ty.
FProofLemma.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l). red; auto.
  destruct (Loc.diff_dec (R a) l); auto. red; auto.
Qed. CloseFLemma.

FLemma save_callee_save_correct:
  forall f tge j ls ls0 rs sp cs fb k m P,
  let b := function_bounds f in
  let fe := make_env b in
  m |= range sp fe.(fe_ofs_callee_save) (size_callee_save_area b fe.(fe_ofs_callee_save)) ** P ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  agree_callee_save ls ls0 ->
  agree_regs j ls rs ->
  forall ls1 rs1,
  ls1 = S.undef_regs destroyed_at_function_entry (S.call_regs ls) ->
  rs1 = T.undef_regs destroyed_at_function_entry rs ->
  exists rs', exists m',
     star T.step tge
        (T.State cs fb (Vptr sp Ptrofs.zero) (save_callee_save fe k) rs1 m)
     E0 (T.State cs fb (Vptr sp Ptrofs.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 ** P
  /\ (forall ofs k p, Mem.perm m sp ofs k p -> Mem.perm m' sp ofs k p)
  /\ agree_regs j ls1 rs'.
FProofLemma.
  intros until P; intros SEP TY AGCS AG; intros ls1 rs1 Heqls1 Heqrs1.
  set (b := function_bounds f) in *.
  exploit (save_callee_save_rec_correct tge j cs fb sp ls1).
- intros. rewrite Heqls1. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
- intros. rewrite Heqls1. apply undef_regs_type. apply TY.
- exact b.(used_callee_save_prop).
- eexact SEP.
- instantiate (1 := rs1). rewrite Heqls1, Heqrs1. apply agree_regs_undef_regs. apply agree_regs_call_regs. auto.
- clear SEP. intros (rs' & m' & EXEC & SEP & PERMS & AG').
  exists rs', m'.
  split. eexact EXEC.
  split. rewrite (contains_callee_saves_exten j sp ls0 ls1). exact SEP.
  intros. apply b.(used_callee_save_prop) in H.
    rewrite Heqls1. rewrite LTL_undef_regs_others. unfold S.call_regs.
    apply AGCS; auto.
    red; intros.
    assert (existsb is_callee_save destroyed_at_function_entry = false).
    { assert (no_callee_saves destroyed_at_function_entry) by (red; reflexivity); auto. }
    assert (existsb is_callee_save destroyed_at_function_entry = true).
    { apply existsb_exists. exists r; auto. }
    congruence.
  split. exact PERMS. exact AG'.
Qed. CloseFLemma.

FLemma size_no_overflow:
  forall f tf,
  transf_function f = OK tf ->
  (make_env (function_bounds f)).(fe_size) <= Ptrofs.max_unsigned.
FProofLemma.
  intros f tf. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. lia.
  intros; discriminate.
Qed. CloseFLemma.

FLemma initial_locations:
  forall j sp pos bound P sl ls m,
  m |= range sp pos (pos + 4 * bound) ** P ->
  (8 | pos) ->
  (forall ofs ty, ls (Locations.S sl ofs ty) = Vundef) ->
  m |= contains_locations j sp pos bound sl ls ** P.
FProofLemma.
  intros. destruct H as (A & B & C). destruct A as (D & E & F). split.
- simpl; intuition auto. red; intros; eauto with mem.
  destruct (Mem.valid_access_load m (chunk_of_type ty) sp (pos + 4 * ofs)) as [v LOAD].
  eapply valid_access_location; eauto.
  red; intros; eauto with mem.
  exists v; split; auto. rewrite H1; auto.
- split; assumption.
Qed. CloseFLemma.

FLemma function_prologue_correct:
  forall f tf (ge: S.genv) tge j ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k P,
  transf_function f = OK tf ->
  let b := function_bounds f in
  let fe := make_env b in
  agree_regs j ls rs ->
  agree_callee_save ls ls0 ->
  agree_outgoing_arguments (S.fn_sig f) ls ls0 ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  ls1 = S.undef_regs destroyed_at_function_entry (S.call_regs ls) ->
  rs1 = T.undef_regs destroyed_at_function_entry rs ->
  Mem.alloc m1 0 (S.fn_stacksize f) = (m2, sp) ->
  Val.has_type parent Tptr -> Val.has_type ra Tptr ->
  m1' |= minjection j m1 ** globalenv_inject ge j ** P ->
  exists j', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5',
     Mem.alloc m1' 0 (T.fn_stacksize tf) = (m2', sp')
  /\ T.store_stack m2' (Vptr sp' Ptrofs.zero) Tptr (T.fn_link_ofs tf) parent = Some m3'
  /\ T.store_stack m3' (Vptr sp' Ptrofs.zero) Tptr (T.fn_retaddr_ofs tf) ra = Some m4'
  /\ star T.step tge
         (T.State cs fb (Vptr sp' Ptrofs.zero) (save_callee_save fe k) rs1 m4')
      E0 (T.State cs fb (Vptr sp' Ptrofs.zero) k rs' m5')
  /\ agree_regs j' ls1 rs'
  /\ agree_locs f ls1 ls0
  /\ m5' |= frame_contents f j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject ge j' ** P
  /\ j' sp = Some(sp', fe.(fe_stack_data))
  /\ inject_incr j j'.
FProofLemma.
  intros until P; intros TRANSF_F AGREGS AGCS AGARGS WTREGS LS1 RS1 ALLOC TYPAR TYRA SEP.
  rewrite (unfold_transf_function f tf).
  unfold T.fn_stacksize, T.fn_link_ofs, T.fn_retaddr_ofs.
  set (b := function_bounds f) in *.
  set (fe := make_env b) in *.
  (* Stack layout info *)
  generalize (frame_env_range b) (frame_env_aligned b). replace (make_env b) with fe by auto.
  intros LAYOUT1 LAYOUT2. hnf in LAYOUT1, LAYOUT2.
  (* Allocation step *)
  destruct (Mem.alloc m1' 0 (fe_size fe)) as [m2' sp'] eqn:ALLOC'.
  exploit alloc_parallel_rule_2.
  eexact SEP. eexact ALLOC. eexact ALLOC'.
  instantiate (1 := fe_stack_data fe). tauto.
  reflexivity.
  instantiate (1 := fe_stack_data fe + bound_stack_data b). rewrite Z.max_comm. reflexivity.
  generalize (bound_stack_data_pos b) (size_no_overflow f tf TRANSF_F). split; auto. lia.
  tauto.
  tauto.
  clear SEP. intros (j' & SEP & INCR & SAME).
  (* Remember the freeable permissions using a mconj *)
  assert (SEPCONJ:
    m2' |= mconj (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
                 (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
           ** minjection j' m2 ** globalenv_inject ge j' ** P).
  { apply mconj_intro; rewrite sep_assoc; assumption. }
  (* Dividing up the frame *)
  apply (frame_env_separated b) in SEP. replace (make_env b) with fe in SEP by auto.
  (* Store of parent *)
  rewrite sep_swap3 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = parent) parent (fun _ => True) m2' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m3' & STORE_PARENT & SEP).
  rewrite sep_swap3 in SEP.
  (* Store of return address *)
  rewrite sep_swap4 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = ra) ra (fun _ => True) m3' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m4' & STORE_RETADDR & SEP).
  rewrite sep_swap4 in SEP.
  (* Saving callee-save registers *)
  rewrite sep_swap5 in SEP.
  exploit (save_callee_save_correct f tge j' ls ls0 rs); eauto.
  apply agree_regs_inject_incr with j; auto.
  replace (S.undef_regs destroyed_at_function_entry (S.call_regs ls)) with ls1 by auto.
  replace (T.undef_regs destroyed_at_function_entry rs) with rs1 by auto.
  clear SEP; intros (rs2 & m5' & SAVE_CS & SEP & PERMS & AGREGS').
  rewrite sep_swap5 in SEP.
  (* Materializing the Local and Outgoing locations *)
  exploit (initial_locations j'). eexact SEP. tauto.
  instantiate (1 := Local). instantiate (1 := ls1).
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  exploit (initial_locations j'). eexact SEP. tauto.
  instantiate (1 := Outgoing). instantiate (1 := ls1).
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  (* Now we frame this *)
  assert (SEPFINAL: m5' |= frame_contents f j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject ge j' ** P).
  { eapply frame_mconj. eexact SEPCONJ.
    rewrite chunk_of_Tptr in SEP.
    unfold frame_contents_1; rewrite ! sep_assoc. exact SEP.
    assert (forall ofs k p, Mem.perm m2' sp' ofs k p -> Mem.perm m5' sp' ofs k p).
    { intros. apply PERMS.
      unfold T.store_stack in STORE_PARENT, STORE_RETADDR.
      simpl in STORE_PARENT, STORE_RETADDR.
      eauto using Mem.perm_store_1. }
    eapply sep_preserved. eapply sep_proj1. eapply mconj_proj2. eexact SEPCONJ.
    intros; apply range_preserved with m2'; auto.
    intros; apply range_preserved with m2'; auto.
  }
  clear SEP SEPCONJ.
(* Conclusions *)
  exists j', rs2, m2', sp', m3', m4', m5'.
  split. auto.
  split. exact STORE_PARENT.
  split. exact STORE_RETADDR.
  split. eexact SAVE_CS.
  split. exact AGREGS'.
  split. rewrite LS1. apply agree_locs_undef_locs; [|reflexivity].
    constructor; intros. unfold S.call_regs. apply AGCS.
    unfold mreg_within_bounds in H; tauto.
    unfold S.call_regs. apply AGARGS. apply incoming_slot_in_parameters; auto.
  split. exact SEPFINAL.
  split. exact SAME. exact INCR.
  exact TRANSF_F.
Qed. CloseFLemma.

FDefinition agree_unused : S.function -> meminj -> S.locset -> T.regset -> Prop :=
  fun f j ls0 rs =>
  forall r, ~(mreg_within_bounds (function_bounds f) r) -> Val.inject j (ls0 (R r)) (rs r).

FLemma restore_callee_save_rec_correct:
  forall f tge j cs fb sp ls0 m l ofs rs k,
  let b := function_bounds f in
  m |= contains_callee_saves j sp ofs l ls0 ->
  agree_unused f j ls0 rs ->
  (forall r, In r l -> mreg_within_bounds b r) ->
  exists rs',
    star T.step tge
      (T.State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save_rec l ofs k) rs m)
   E0 (T.State cs fb (Vptr sp Ptrofs.zero) k rs' m)
  /\ (forall r, In r l -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused f j ls0 rs'.
FProofLemma.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl contains_callee_saves; intros.
- (* base case *)
  exists rs. intuition auto. apply star_refl.
- (* inductive case *)
  set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (ofs1 := align ofs sz).
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (OFSLE: ofs <= ofs1) by (apply align_le; auto).
  remember (function_bounds f) as b. simpl in H1.
  assert (BOUND: mreg_within_bounds b r) by eauto.
  exploit contains_get_stack.
    eapply sep_proj1; eassumption.
  intros (v & LOAD & SPEC).
  exploit (IHl (ofs1 + sz) (rs#r <- v)).
    eapply sep_proj2; eassumption.
    red; intros. rewrite Regmap.gso. auto. rewrite <- Heqb in H2. intuition congruence.
    eauto.
  intros (rs' & A & B & C & D).
  exists rs'.
  split. eapply star_step; eauto.
    fconstructor. traceEq.
  simpl.
  split. intros.
    destruct (In_dec mreg_eq r0 l). auto.
    assert (r = r0) by tauto. subst r0.
    rewrite C by auto. rewrite Regmap.gss. exact SPEC.
  split. intros.
    rewrite C by tauto. apply Regmap.gso. intuition auto.
  exact D.
Qed. CloseFLemma.

FLemma restore_callee_save_correct:
  forall f tge m j sp ls ls0 pa ra P rs k cs fb,
  let b := function_bounds f in
  let fe := make_env b in
  m |= frame_contents f j sp ls ls0 pa ra ** P ->
  agree_unused f j ls0 rs ->
  exists rs',
    star T.step tge
       (T.State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save fe k) rs m)
    E0 (T.State cs fb (Vptr sp Ptrofs.zero) k rs' m)
  /\ (forall r,
        is_callee_save r = true -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r,
        is_callee_save r = false -> rs' r = rs r).
FProofLemma.
  intros.
  unfold frame_contents, frame_contents_1 in H.
  apply mconj_proj1 in H. rewrite ! sep_assoc in H. apply sep_pick5 in H.
  exploit restore_callee_save_rec_correct; eauto.
  intros; unfold mreg_within_bounds; auto.
  intros (rs' & A & B & C & D).
  exists rs'.
  split. eexact A.
  split; intros.
  destruct (In_dec mreg_eq r (used_callee_save (function_bounds f))).
  apply B; auto.
  rewrite C by auto. apply H0. unfold mreg_within_bounds; tauto.
  apply C. red; intros. apply (used_callee_save_prop (function_bounds f)) in H2. congruence.
Qed. CloseFLemma.

FLemma function_epilogue_correct:
  forall f tf tge m' j sp' ls ls0 pa ra P m rs sp m1 k cs fb,
  transf_function f = OK tf ->
  let b := function_bounds f in
  let fe := make_env b in
  m' |= frame_contents f j sp' ls ls0 pa ra ** minjection j m ** P ->
  agree_regs j ls rs ->
  agree_locs f ls ls0 ->
  j sp = Some(sp', fe.(fe_stack_data)) ->
  Mem.free m sp 0 (S.fn_stacksize f) = Some m1 ->
  exists rs1, exists m1',
     T.load_stack m' (Vptr sp' Ptrofs.zero) Tptr (T.fn_link_ofs tf) = Some pa
  /\ T.load_stack m' (Vptr sp' Ptrofs.zero) Tptr (T.fn_retaddr_ofs tf) = Some ra
  /\ Mem.free m' sp' 0 (T.fn_stacksize tf) = Some m1'
  /\ star T.step tge
       (T.State cs fb (Vptr sp' Ptrofs.zero) (restore_callee_save fe k) rs m')
    E0 (T.State cs fb (Vptr sp' Ptrofs.zero) k rs1 m')
  /\ agree_regs j (S.return_regs ls0 ls) rs1
  /\ agree_callee_save (S.return_regs ls0 ls) ls0
  /\ m1' |= minjection j m1 ** P.
FProofLemma.
  intros until fb; intros TRANSF_F SEP AGR AGL INJ FREE.
  (* Can free *)
  exploit free_parallel_rule.
    rewrite <- sep_assoc. eapply mconj_proj2. eexact SEP.
    eexact FREE.
    eexact INJ.
    auto. rewrite Z.max_comm; reflexivity.
  intros (m1' & FREE' & SEP').
  (* Reloading the callee-save registers *)
  exploit restore_callee_save_correct.
    eexact SEP.
    instantiate (1 := rs).
    red; intros. destruct AGL. rewrite <- agree_unused_reg0 by auto. apply AGR.
  intros (rs' & LOAD_CS & CS & NCS).
  (* Reloading the back link and return address *)
  unfold frame_contents in SEP; apply mconj_proj1 in SEP.
  unfold frame_contents_1 in SEP; rewrite ! sep_assoc in SEP.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick3; eexact SEP. intros LOAD_LINK.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick4; eexact SEP. intros LOAD_RETADDR.
  clear SEP.
  (* Conclusions *)
  rewrite (unfold_transf_function f tf); simpl.
  exists rs', m1'.
  split. assumption.
  split. assumption.
  split. assumption.
  split. eassumption.
  split. red; unfold S.return_regs; intros.
    destruct (is_callee_save r) eqn:C.
    apply CS; auto.
    rewrite NCS by auto. apply AGR.
  split. red; unfold S.return_regs; intros.
    destruct l. rewrite H; auto. destruct sl; auto; contradiction.
  assumption.
  exact TRANSF_F.
Qed. CloseFLemma.

FLemma match_stacks_type_sp:
  forall ge tge j cs cs' sg,
  match_stacks ge tge j cs cs' sg ->
  Val.has_type (T.parent_sp cs') Tptr.
FProofLemma.
  induction 1; unfold T.parent_sp. apply Val.Vnullptr_has_type. apply Val.Vptr_has_type.
Qed. CloseFLemma.

FLemma match_stacks_type_retaddr:
  forall ge tge j cs cs' sg,
  match_stacks ge tge j cs cs' sg ->
  Val.has_type (T.parent_ra cs') Tptr.
FProofLemma.
  induction 1; unfold T.parent_ra. apply Val.Vnullptr_has_type. auto.
Qed. CloseFLemma.

FLemma contains_locations_incr:
  forall j j' sp pos bound sl ls,
  inject_incr j j' ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j' sp pos bound sl ls).
FProofLemma.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; eauto.
Qed. CloseFLemma.

FLemma contains_callee_saves_incr:
  forall j j' sp ls,
  inject_incr j j' ->
  forall rl pos,
  massert_imp (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j' sp pos rl ls).
FProofLemma.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_1; auto. apply contains_imp. eauto.
Qed. CloseFLemma.

FLemma frame_contents_incr:
  forall f j sp ls ls0 parent retaddr m P j',
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  inject_incr j j' ->
  m |= frame_contents f j' sp ls ls0 parent retaddr ** P.
FProofLemma.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- (contains_locations_incr j j') by auto.
  rewrite <- (contains_locations_incr j j') by auto.
  rewrite <- (contains_callee_saves_incr j j') by auto.
  assumption.
Qed. CloseFLemma.

FLemma stack_contents_change_meminj:
  forall m j j', inject_incr j j' ->
  forall cs cs' P,
  m |= stack_contents j cs cs' ** P ->
  m |= stack_contents j' cs cs' ** P.
FProofLemma.
Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; simpl; intros; auto.
  destruct sp0; auto.
  rewrite sep_assoc in *.
  apply frame_contents_incr with (j := j); auto.
  rewrite sep_swap. apply IHcs. rewrite sep_swap. assumption.
Qed. CloseFLemma.

FLemma match_stacks_change_meminj:
  forall ge tge j j', inject_incr j j' ->
  forall cs cs' sg,
  match_stacks ge tge j cs cs' sg ->
  match_stacks ge tge j' cs cs' sg.
FProofLemma.
  induction 2; intros.
- constructor; auto.
- econstructor; eauto.
Qed. CloseFLemma.

FLemma function_ptr_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_funct_ptr_transf_partial TRANSL).
Qed. CloseFLemma.

(* This should be in Conventions1 *)
FLemma loc_arguments_main:
  loc_arguments signature_main = nil.
FProofLemma.
  reflexivity.
Qed. CloseFLemma.

FInduction transf_step_correct about S.step motive
  (fun ge s1 t s2 (_ : S.step ge s1 t s2) =>
     forall tge prog tprog (TRANSF: match_prog prog tprog),
     ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
     forall (WTS: wt_state s1) s1' (MS: match_states ge tge s1 s1'),
     exists s2', plus T.step tge s1' t s2' /\ match_states ge tge s2 s2').
FProof.
all: intros;
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND); fsimpl in *.
(* Llabel *)
+ econstructor; split.
  apply plus_one; apply T.exec_Llabel.
  econstructor; eauto with coqlib.

(* Lgoto *)
+ econstructor; split.
  apply plus_one; eapply T.exec_Lgoto; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto.
  eapply find_label_tail; eauto.

(* Lop *)
+  assert (exists v',
          eval_operation (Genv.globalenv prog) (Vptr sp' Ptrofs.zero) (transl_op (make_env (function_bounds f)) op) rs0##args m' = Some v'
       /\ Val.inject j v v').
  eapply eval_operation_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  eapply agree_reglist; eauto.
  apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. exact SEP.
  destruct H as [v' [A B]].
  econstructor; split.
  apply plus_one. fconstructor.
  instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved.
  exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl). eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  rewrite transl_destroyed_by_op. apply agree_regs_undef_regs; auto.
  apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_op_caller_save.
  fsimpl in BOUND. assumption.
  apply frame_set_reg. apply frame_undef_regs. exact SEP.

(* Lcond true *)
+ econstructor; split.
  apply plus_one. eapply T.exec_Lcond_true; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
  eapply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  auto.
  eapply find_label_tail; eauto.
  apply frame_undef_regs; auto.

(* Lcond false *)
+ econstructor; split.
  apply plus_one. eapply T.exec_Lcond_false; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  auto. eauto with coqlib.
  apply frame_undef_regs; auto.

(* return *)
+ inv STACKS. exploit wt_returnstate_agree; eauto. intros [AGCS OUTU].
  simpl in AGCS. unfold stack_contents in SEP. fold stack_contents in SEP. (* simpl in SEP.*) rewrite sep_assoc in SEP.
  econstructor; split.
  apply plus_one. apply T.exec_return.
  econstructor; eauto.
  apply agree_locs_return with rs0; auto.
  apply frame_contents_exten with rs0 (S.parent_locset s); auto.
  intros; apply Val.lessdef_same; apply AGCS; red; congruence.
  intros; rewrite (OUTU ty ofs); auto.

(* Lgetstack *)
+ fsimpl in BOUND. destruct BOUND as [BOUND1 BOUND2].
  exploit wt_state_getstack; eauto. intros SV.
  unfold S.destroyed_by_getstack; destruct sl.
- (* Lgetstack, local *)
  exploit frame_get_local; eauto. intros (v & A & B).
  econstructor; split.
  apply plus_one. apply T.exec_Lgetstack. exact A.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_locs_set_reg; auto.
- (* Lgetstack, incoming *)
  unfold slot_valid in SV. InvBooleans.
  exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  inversion STACKS; clear STACKS.
  elim (H1 _ IN_ARGS).
  subst s cs'.
  exploit frame_get_outgoing.
  apply sep_proj2 in SEP. unfold stack_contents in SEP. fold stack_contents in SEP.
  (*simpl in SEP.*) rewrite sep_assoc in SEP. eexact SEP.
  eapply ARGS; eauto.
  eapply slot_outgoing_argument_valid; eauto.
  intros (v & A & B).
  econstructor; split.
  apply plus_one. eapply T.exec_Lgetparam; eauto.
  rewrite (unfold_transf_function _ _ TRANSL). unfold T.fn_link_ofs.
  eapply frame_get_parent. eexact SEP.
  econstructor; eauto with coqlib. econstructor; eauto.
  apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto.
  erewrite agree_incoming by eauto. exact B.
  apply agree_locs_set_reg; auto. apply agree_locs_undef_locs; auto.
- (* Lgetstack, outgoing *)
  exploit frame_get_outgoing; eauto. intros (v & A & B).
  econstructor; split.
  apply plus_one. apply T.exec_Lgetstack. exact A.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_locs_set_reg; auto.

(* Lsetstack *)
+ exploit wt_state_setstack; eauto. intros (SV & SW).
  set (ofs' := match sl with
               | Local => offset_local (make_env (function_bounds f)) ofs
               | Incoming => 0 (* dummy *)
               | Outgoing => offset_arg ofs
               end).
  eapply frame_undef_regs in SEP.
  instantiate (1 := destroyed_by_setstack ty) in SEP.
  assert (A: exists m'',
              T.store_stack m' (Vptr sp' Ptrofs.zero) ty (Ptrofs.repr ofs') (rs0 src) = Some m''
           /\ m'' |= frame_contents f j sp' (Locmap.set (S sl ofs ty) (rs (R src))
                                               (S.undef_regs (destroyed_by_setstack ty) rs))
                                            (S.parent_locset s) (T.parent_sp cs') (T.parent_ra cs')
                  ** stack_contents j s cs' ** minjection j m ** globalenv_inject (Genv.globalenv prog) j).
  { unfold ofs'; destruct sl; try discriminate.
    eapply frame_set_local; eauto. fsimpl in BOUND. exact BOUND.
    eapply frame_set_outgoing; eauto. fsimpl in BOUND. exact BOUND. }
  clear SEP; destruct A as (m'' & STORE & SEP).
  econstructor; split.
  apply plus_one. destruct sl; try discriminate.
  fconstructor. (* eexact STORE. eauto.*)
  fconstructor. (* eexact STORE. eauto.*)
  econstructor. eauto. eauto. eauto.
  apply agree_regs_set_slot. apply agree_regs_undef_regs. auto.
  apply agree_locs_set_slot. apply agree_locs_undef_locs. auto. apply destroyed_by_setstack_caller_save. auto.
  eauto. eauto with coqlib. eauto.

(* internal function *)
+ revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  destruct (transf_function f) as [tfn|] eqn:TRANSL; simpl; try congruence.
  intros EQ; inversion EQ; clear EQ; subst tf.
  rewrite sep_comm, sep_assoc in SEP.
  exploit wt_callstate_agree; eauto. intros [AGCS AGARGS].
  exploit function_prologue_correct; eauto.
  red; intros; eapply wt_callstate_wt_regs; eauto.
  eapply match_stacks_type_sp; eauto.
  eapply match_stacks_type_retaddr; eauto.
  clear SEP;
  intros (j' & rs' & m2' & sp' & m3' & m4' & m5' & A & B & C & D & E & F & SEP & J & K).
  rewrite (sep_comm (globalenv_inject (Genv.globalenv prog) j')) in SEP.
  rewrite (sep_swap (minjection j' m')) in SEP.
  econstructor; split.
  eapply plus_left. fconstructor; eauto.
  rewrite (unfold_transf_function _ _ TRANSL). unfold T.fn_code. unfold transl_body.
  eexact D. traceEq.
  eapply match_states_intro with (j := j'); eauto with coqlib.
  eapply match_stacks_change_meminj; eauto.
  rewrite sep_swap in SEP. rewrite sep_swap. eapply stack_contents_change_meminj; eauto.

(* Lreturn *)
+ rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  intros (rs' & m1' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply plus_right. eexact D. fconstructor; eauto. traceEq.
  econstructor; eauto.
  rewrite sep_swap; exact G.
Qed. FEnd transf_step_correct.

FLemma transf_initial_states:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall st1, S.initial_state prog st1 ->
  exists st2, T.initial_state tprog st2 /\ match_states ge tge st1 st2.
FProofLemma.
  intros. inv H2.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial H); eauto.
  rewrite (match_program_main H).
  rewrite symbols_preserved with (prog:=prog) (tprog:=tprog) (ge:=(Genv.globalenv prog)). eauto. apply H. auto. auto.
  set (j := Mem.flat_inj (Mem.nextblock m0)).
  eapply match_states_call with (j := j); eauto.
  constructor. red; intros. rewrite H6, loc_arguments_main in H0. contradiction.
  red; simpl; auto. unfold stack_contents.
  (*simpl.*) rewrite sep_pure. split; auto. split;[|split].
  eapply Genv.initmem_inject; eauto.
  simpl. exists (Mem.nextblock m0); split. apply Ple_refl.
  unfold j, Mem.flat_inj; constructor; intros.
    apply pred_dec_true; auto.
    destruct (plt b1 (Mem.nextblock m0)); congruence.
    change (Mem.valid_block m0 b0). eapply Genv.find_symbol_not_fresh; eauto.
    change (Mem.valid_block m0 b0). eapply Genv.find_funct_ptr_not_fresh; eauto.
    change (Mem.valid_block m0 b0). eapply Genv.find_var_info_not_fresh; eauto.
  red; simpl; tauto.
Qed. CloseFLemma.

FLemma transf_final_states:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall st1 st2 r,
  match_states ge tge st1 st2 -> S.final_state st1 r -> T.final_state st2 r.
FProofLemma.
  intros. inv H3. inv H2. inv STACKS.
  assert (R: exists r, loc_result signature_main = AST.One r).
  { destruct (loc_result signature_main) as [r1 | r1 r2] eqn:LR.
  - exists r1; auto.
  - generalize (loc_result_type signature_main). rewrite LR. discriminate.
  }
  destruct R as [rres EQ]. rewrite EQ in H4. simpl in H4.
  generalize (AGREGS rres). rewrite H4. intros A; inv A.
  econstructor; eauto.
Qed. CloseFLemma.

FEnd Stacking.

FEnd Base.

Trait Comp_Loops extends Base.

Family Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

Family Linear extends Lfam.
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

Trait Stacking_jumptable extends Stacking.

FRecursion wt_instr.
Case Ljumptable arg tbl := (fun funct => true).
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case Ljumptable arg tbl := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case Ljumptable arg tbl := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FRecursion transl_instr.
Case Ljumptable arg tbl := (fun fe k => T.Ljumptable arg tbl :: k).
FEnd transl_instr.
FEnd Stacking_jumptable.

Family Stacking extends Stacking_jumptable.

FRecursion instr_within_bounds.
Case _ := (fun b => True).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case _ := (fun r' => False).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
Qed. FEnd record_regs_of_instr_ok.


FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
simpl; do 4 fsimpl; simpl; intros; auto.
Qed. FEnd instr_is_within_bounds.

Inherit no_callee_saves.

FLemma destroyed_by_jumptable_caller_save:
  no_callee_saves destroyed_by_jumptable.
FProofLemma.
  red; reflexivity.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros; try inv MS; try rewrite transl_code_eq; try (generalize (function_is_within_bounds f _ (is_tail_in TAIL)); intro BOUND; simpl in BOUND); fsimpl in *.
(* Ljumptable *)
+  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite e. intro IJ; inv IJ; auto. }
  econstructor; split.
  apply plus_one; eapply T.exec_Ljumptable; eauto.
  apply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_jumptable_caller_save.
  auto. eapply find_label_tail; eauto.
  apply frame_undef_regs; auto.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Linear.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin:
      forall ge s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (State s f sp (Lbuiltin ef args res :: b) rs m)
        t (State s f sp b rs' m').
FEnd Linear.

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

Family Stacking.

FRecursion wt_instr.
Case Lbuiltin ef args res := (fun funct =>
      wt_builtin_res (proj_sig_res (ef_sig ef)) res
      && forallb (loc_valid funct) (params_of_builtin_args args)).
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case _ := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

MetaData transl_builtin_arg.
Fixpoint transl_builtin_arg (fe: frame_env) (a: builtin_arg loc) : builtin_arg mreg :=
  match a with
  | BA (R r) => BA r
  | BA (S Local ofs ty) =>
      BA_loadstack (chunk_of_type ty) (Ptrofs.repr (offset_local fe ofs))
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

FRecursion instr_within_bounds.
Case Lbuiltin ef args res := (fun b =>
       (forall r, In r (params_of_builtin_res res) \/ In r (destroyed_by_builtin ef) -> mreg_within_bounds b r)
       /\ (forall sl ofs ty, In (Locations.S sl ofs ty) (params_of_builtin_args args) -> slot_within_bounds b sl ofs ty)).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case Lbuiltin ef args res := (fun r' => In r' (params_of_builtin_res res) \/ In r' (destroyed_by_builtin ef)).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

Inherit record_reg_ok.

FLemma record_regs_ok: forall r rl u, In r rl -> is_callee_save r = true -> RegSet.In r (record_regs u rl).
FProofLemma.
  intros. unfold record_regs. eapply fold_left_ensures; eauto using record_reg_incr, record_reg_ok.
Qed. CloseFLemma.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
(* TODO: I think this is easy *)
apply cheat.
(* + destruct H; auto using record_regs_incr, record_regs_ok.*)
(*+ destruct H. eapply record_regs_ok in H0.
  assert (A : RegSet.In r' u).
  apply record_regs_incr. auto using record_regs_incr, record_regs_ok.   *)
Qed. FEnd record_regs_of_instr_ok.

MetaData slots_of_locs.
Fixpoint slots_of_locs (l: list loc) : list (slot * Z * typ) :=
  match l with
  | nil => nil
  | S sl ofs ty :: l' => (sl, ofs, ty) :: slots_of_locs l'
  | R r :: l' => slots_of_locs l'
  end.
FEnd slots_of_locs.

FLemma slots_of_locs_charact:
  forall sl ofs ty l, In (sl, ofs, ty) (slots_of_locs l) <-> In (Locations.S sl ofs ty) l.
FProofLemma.
  induction l; simpl; intros.
  tauto.
  destruct a; simpl; intuition congruence.
Qed. CloseFLemma.

FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
  simpl; do 4 fsimpl; simpl; intros; auto.
 split; intros.
  apply H1; auto.
  (* apply H0. rewrite slots_of_locs_charact; auto.*)
  (* TODO: this shouldn't be too hard *)
  apply cheat.
Qed. FEnd instr_is_within_bounds.

Inherit frame_get_local.

FLemma transl_builtin_arg_correct:
  forall (ge: S.genv) (f: S.function)
         (tf: T.function),
  let b := function_bounds f in
  let fe := make_env b in
  forall (TRANSF_F: transf_function f = OK tf)
  (j: meminj)
  (m m': mem)
  (ls ls0: S.locset)
  (rs: regset)
  (sp sp': block)
  (parent retaddr: val)
  (INJ: j sp = Some(sp', fe.(fe_stack_data)))
  (AGR: agree_regs j ls rs)
  (SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject ge j) a v,
  eval_builtin_arg ge ls (Vptr sp Ptrofs.zero) m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (Locations.S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg ge rs (Vptr sp' Ptrofs.zero) m' (transl_builtin_arg fe a) v'
  /\ Val.inject j v v'.
FProofLemma.
  intros until retaddr. intros INJ AGR SEP. assert (SYMB: forall id ofs, Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address ge id ofs)).
  { assert (G: meminj_preserves_globals ge j).
    { eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eexact SEP. }
    intros; unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) eqn:FS; auto.
    destruct G. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
(* Local Opaque fe.*)
  induction 1; (*simpl;*) intros VALID BOUNDS.
- simpl in VALID. assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + simpl. exists (rs r); auto with barg.
  + simpl in BOUNDS. exploit frame_get_local; eauto. intros (v & A & B).
    exists v; split; auto. constructor; auto.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. set (ofs' := Ptrofs.add ofs (Ptrofs.repr (fe_stack_data (make_env (function_bounds f))))).
  apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  instantiate (1 := Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs').
  simpl. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; split; eauto with barg.
  unfold Val.offset_ptr. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
- simpl in BOUNDS. simpl in VALID. simpl. apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; split; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_inject; auto.
- simpl in BOUNDS. simpl in VALID. simpl. destruct IHeval_builtin_arg1 as (v1' & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); auto using in_or_app.
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed. CloseFLemma.

FLemma transl_builtin_args_correct:
  forall (ge: S.genv) (f: S.function)
         (tf: T.function),
  let b := function_bounds f in
  let fe := make_env b in
  forall (TRANSF_F: transf_function f = OK tf)
  (j: meminj)
  (m m': mem)
  (ls ls0: S.locset)
  (rs: regset)
  (sp sp': block)
  (parent retaddr: val)
  (INJ: j sp = Some(sp', fe.(fe_stack_data)))
  (AGR: agree_regs j ls rs)
  (SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject ge j) al vl,
  eval_builtin_args ge ls (Vptr sp Ptrofs.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (Locations.S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args ge rs (Vptr sp' Ptrofs.zero) m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.inject_list j vl vl'.
FProofLemma.
  intros until retaddr. intros INJ AGR SEP. induction 1; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed. CloseFLemma.

FLemma wt_state_builtin:
  forall s f sp ef args res c rs m,
  wt_state (S.State s f sp (S.Lbuiltin ef args res :: c) rs m) ->
  forallb (loc_valid f) (params_of_builtin_args args) = true.
FProofLemma.
  intros. inv H. simpl in WTC. fsimpl in WTC; InvBooleans. auto.
Qed. CloseFLemma.

FLemma senv_preserved: forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.senv_match TRANSL).
Qed. CloseFLemma.

FLemma agree_regs_set_res:
  forall j res v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setres res v ls) (T.set_res res v' rs).
FProofLemma.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed. CloseFLemma.

FLemma agree_locs_set_res:
  forall f ls0 res v ls,
  let b := function_bounds f in
  let fe := make_env b in
  agree_locs f ls ls0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_locs f (Locmap.setres res v ls) ls0.
FProofLemma.
  induction res; simpl; intros.
- eapply agree_locs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed. CloseFLemma.

FLemma frame_set_res:
  forall f j sp ls0 parent retaddr m P res v ls,
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents f j sp (Locmap.setres res v ls) ls0 parent retaddr ** P.
FProofLemma.
  induction res; (*simpl;*) intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros;
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND); fsimpl in *.
(* Lbuiltin *)
+ fsimpl in BOUND. destruct BOUND as [BND1 BND2].
  exploit transl_builtin_args_correct.
    eauto. eauto. exact AGREGS. rewrite sep_swap in SEP; apply sep_proj2 in SEP; eexact SEP.
    eauto. rewrite <- forallb_forall. eapply wt_state_builtin; eauto.
    exact BND2.
  intros [vargs' [P Q]].
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  exploit external_call_parallel_rule; eauto.
  clear SEP; intros (j' & res' & m1' & EC & RES & SEP & INCR & ISEP).
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  econstructor; split.
  apply plus_one. fconstructor; eauto.
  eapply eval_builtin_args_preserved with (ge1 := (Genv.globalenv prog)); eauto. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  eapply external_call_symbols_preserved; eauto. apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  eapply match_states_intro with (j := j'); eauto with coqlib.
  eapply match_stacks_change_meminj; eauto.
  apply agree_regs_set_res; auto. apply agree_regs_undef_regs; auto. eapply agree_regs_inject_incr; eauto.
  apply agree_locs_set_res; auto. apply agree_locs_undef_regs; auto.
  apply frame_set_res. apply frame_undef_regs. apply frame_contents_incr with j; auto.
  rewrite sep_swap2. apply stack_contents_change_meminj with j; auto. rewrite sep_swap2.
  exact SEP.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

Family Linear extends Lfam.
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

Family Stacking.

FRecursion wt_instr.
Case Lload chunk addr args dst :=
  (fun funct => subtype (type_of_chunk chunk) (mreg_type dst)).
Case Lstore chunk addr args src := (fun funct => true).
FEnd wt_instr.

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

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FDefinition transl_addr := fun (fe: frame_env) (addr: addressing) =>
  shift_stack_addressing fe.(fe_stack_data) addr.

FDefinition simplify_load := fun chunk =>
  match chunk with
  | Mbool => Mint8unsigned
  | _ => chunk
  end.

FDefinition simplify_store := fun chunk =>
  match chunk with
  | Mbool => Mint8unsigned
  | Mint8signed => Mint8unsigned
  | Mint16signed => Mint16unsigned
  | _ => chunk
  end.

FRecursion transl_instr.
Case Lload chunk addr args dst :=
 (fun fe k => T.Lload (simplify_load chunk) (transl_addr fe addr) args dst :: k).
Case Lstore chunk addr args src :=
 (fun fe k => T.Lstore (simplify_store chunk) (transl_addr fe addr) args src :: k).
FEnd transl_instr.

FRecursion instr_within_bounds.
Case Lload chunk addr args dst := (fun b => mreg_within_bounds b dst).
Case _ := (fun b => True).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case Lload chunk addr args dst := (fun r' => r' = dst).
Case _ := (fun r' => False).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
Qed. FEnd record_regs_of_instr_ok.

FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
simpl; do 4 fsimpl; simpl; intros; auto.
Qed. FEnd instr_is_within_bounds.

FLemma simplify_load_correct: forall chunk m a v,
  Mem.loadv chunk m a = Some v ->
  exists v', Mem.loadv (simplify_load chunk) m a = Some v' /\ Val.lessdef v v'.
FProofLemma.
  intros. destruct a; simpl in *; try discriminate.
  destruct chunk; simpl; try (exists v; auto; fail).
  rewrite Mem.load_bool_int8_unsigned in H.
  destruct (Mem.load Mint8unsigned m b (Ptrofs.unsigned i)) as [v'|]; simpl in H; inv H.
  exists v'; auto using Val.norm_bool_is_lessdef.
Qed. CloseFLemma.

FLemma simplify_store_correct: forall chunk m a v m',
  Mem.storev chunk m a v = Some m' ->
  Mem.storev (simplify_store chunk) m a v = Some m'.
FProofLemma.
  intros. destruct a; simpl in *; try discriminate. rewrite <- H. symmetry.
  destruct chunk; simpl; auto.
- apply Mem.store_bool_unsigned_8.
- apply Mem.store_signed_unsigned_8.
- apply Mem.store_signed_unsigned_16.
Qed. CloseFLemma.

FLemma simplify_load_destroyed: forall chunk addr,
  destroyed_by_load (simplify_load chunk) addr = destroyed_by_load chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

FLemma simplify_store_destroyed: forall chunk addr,
  destroyed_by_store (simplify_store chunk) addr = destroyed_by_store chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

Inherit no_callee_saves.
Inherit ByCases.

FLemma destroyed_by_load_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_load chunk addr).
FProofLemma.
Local Transparent destroyed_by_load.
  intros; unfold destroyed_by_load; ByCases.
Qed. CloseFLemma.

FLemma transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

FLemma transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

FLemma destroyed_by_store_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_store chunk addr).
FProofLemma.
Local Transparent destroyed_by_store.
  intros; unfold destroyed_by_store; ByCases.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros; try inv MS; try rewrite transl_code_eq; try (generalize (function_is_within_bounds f _ (is_tail_in TAIL)); intro BOUND; simpl in BOUND); fsimpl in *.
(* Lload *)
+ assert (exists a',
          eval_addressing (Genv.globalenv prog) (Vptr sp' Ptrofs.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ Val.inject j a a').
  eapply eval_addressing_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  eapply agree_reglist; eauto.
  destruct H as [a' [A B]].
  exploit loadv_parallel_rule.
  apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. eexact SEP.
  eauto. eauto.
  intros [v' [C D]].
  exploit simplify_load_correct; eauto.
  intros [v'' [E F]].
  assert (G: Val.inject j v v'').
  { inv F; auto. inv D; auto. }
  econstructor; split.
  apply plus_one. eapply T.exec_Lload. (* fconstructor. *)
  instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  eexact E. eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg. rewrite transl_destroyed_by_load, simplify_load_destroyed. apply agree_regs_undef_regs; auto. auto.
  apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_load_caller_save. fsimpl in BOUND. auto.

(* Lstore *)
+ assert (exists a',
          eval_addressing (Genv.globalenv prog) (Vptr sp' Ptrofs.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ Val.inject j a a').
  eapply eval_addressing_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  eapply agree_reglist; eauto.
  destruct H as [a' [A B]].
  rewrite sep_swap3 in SEP.
  exploit storev_parallel_rule. eexact SEP. eauto. eauto. apply AGREGS.
  clear SEP; intros (m1' & C & SEP).
  rewrite sep_swap3 in SEP.
  econstructor; split.
  apply plus_one. eapply T.exec_Lstore.
  instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  apply simplify_store_correct. eexact C. eauto.
  econstructor. eauto. eauto. eauto.
  rewrite transl_destroyed_by_store, simplify_store_destroyed. apply agree_regs_undef_regs; auto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
  auto. eauto with coqlib.
  eapply frame_undef_regs; eauto.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap. FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

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

Family Stacking.

FRecursion wt_instr.
Case _ := (fun funct => true).
(*Case Lcall sig ros := (fun funct => ).
Case Ltailcall sig ros := (fun funct => ).*)
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case _ := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FRecursion transl_instr.
Case Lcall sig ros :=
 (fun fe k => T.Lcall sig ros :: k).
Case Ltailcall sig ros :=
  (fun fe k => restore_callee_save fe (T.Ltailcall sig ros :: k)).
FEnd transl_instr.

FRecursion instr_within_bounds.
Case Lcall sig ros := (fun b => size_arguments sig <= bound_outgoing b).
Case _ := (fun b => True).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case _ := (fun r' => False).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
Qed. FEnd record_regs_of_instr_ok.

FLemma size_arguments_bound:
  forall f sig ros,
  In (S.Lcall sig ros) (S.fn_code f) ->
  size_arguments sig <= bound_outgoing (function_bounds f).
FProofLemma.
(* TODO *)
apply cheat.
(* intros. change (size_arguments sig) with (outgoing_space (S.Lcall sig ros)).
  unfold function_bounds, bound_outgoing.
  apply Zmax_bound_l. apply max_over_instrs_bound; auto.*)
Qed. CloseFLemma.

FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
  simpl; do 4 fsimpl; simpl; intros; auto.
eapply size_arguments_bound; eauto.
Qed. FEnd instr_is_within_bounds.

Inherit function_ptr_translated.

FLemma find_function_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall j ls rs m ros f,
  agree_regs j ls rs ->
  m |= globalenv_inject ge j ->
  S.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     T.find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
FProofLemma.
  intros until f; intros AG [bound [_ [?????]]] FF.
  destruct ros; simpl in FF.
- exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF.
  rewrite Genv.find_funct_find_funct_ptr in FF.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  rewrite DOMAIN in H5. inv H5. simpl. auto. eapply FUNCTIONS; eauto.
- destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl. subst. (* rewrite H1.*)
  rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) H eq_refl eq_refl).  auto.
Qed. CloseFLemma.

FOpaque Definition return_address_offset_exists:
  forall f sg ros c,
    is_tail (T.Lcall sg ros :: c) (T.fn_code f) ->
  exists ofs, T.return_address_offset f c ofs := cheat.

FLemma is_tail_save_callee_save:
  forall l ofs k,
  is_tail k (save_callee_save_rec l ofs k).
FProofLemma.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto.
Qed. CloseFLemma.

FLemma is_tail_restore_callee_save:
  forall l ofs k,
  is_tail k (restore_callee_save_rec l ofs k).
FProofLemma.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto.
Qed. CloseFLemma.

FInduction is_tail_transl_instr about S.instruction motive
  (fun (i : S.instruction) =>
     forall fe k, is_tail k (transl_instr i fe k)).
FProof.
all: intros; fsimpl; auto with coqlib.
+ unfold restore_callee_save. eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
+ unfold restore_callee_save. eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
+ destruct s; auto with coqlib.
+ destruct s; auto with coqlib.
Qed. FEnd is_tail_transl_instr.

FLemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
FProofLemma.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq.
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed. CloseFLemma.

FLemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (S.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (T.fn_code tf).
FProofLemma.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body, save_callee_save.
  eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed. CloseFLemma.

FLemma match_stacks_change_sig:
  forall ge tge sg1 j cs cs' sg,
  match_stacks ge tge j cs cs' sg ->
  tailcall_possible sg1 ->
  match_stacks ge tge j cs cs' sg1.
FProofLemma.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto. intros. elim (H0 _ H1).
Qed. CloseFLemma.

(* This should be in Conventions? *)
FLemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 -> tailcall_possible sg.
FProofLemma.
  intros; red; intros. exploit loc_arguments_acceptable_2; eauto.
  unfold loc_argument_acceptable.
  destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
  generalize (loc_arguments_bounded _ _ _ H0).
  generalize (typesize_pos ty). lia.
Qed. CloseFLemma.

FLemma wt_state_tailcall:
  forall s f sp sg ros c rs m,
  wt_state (S.State s f sp (S.Ltailcall sg ros :: c) rs m) ->
  size_arguments sg = 0.
FProofLemma.
  intros. inv H. simpl in WTC. fsimpl in WTC. apply cheat. (* why? InvBooleans. auto.*)
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros; try inv MS; try rewrite transl_code_eq; try (generalize (function_is_within_bounds f _ (is_tail_in TAIL)); intro BOUND; simpl in BOUND); fsimpl in *.
(* Lcall *)
+ exploit find_function_translated; eauto.
    eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. fsimpl in IST. eexact IST. intros [ra D].
  econstructor; split.
  apply plus_one. fconstructor; eauto.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  apply Val.Vptr_has_type.
  do 2 fsimpl in IST. fsimpl in BOUND.
  intros; red.
    apply Z.le_trans with (size_arguments (S.funsig f')). auto.
    apply loc_arguments_bounded; auto. auto.
    unfold stack_contents. fold stack_contents.
  rewrite sep_assoc. exact SEP.

(* Ltailcall*)
+ rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  clear SEP. intros (rs1 & m1' & P & Q & R & S & T & U & SEP).
  rewrite sep_swap in SEP.
  exploit find_function_translated; eauto.
    eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  econstructor; split.
  eapply plus_right. eexact S. fconstructor; eauto. traceEq.
  econstructor; eauto.
  apply match_stacks_change_sig with (S.fn_sig f); auto.
  apply zero_size_arguments_tailcall_possible. eapply wt_state_tailcall; eauto.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops. FEnd Comp_Switch.

Family Comp extends
  Comp_Heap,
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Field,
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin.

Family Stacking.
Final Family S := Linear.
Final Family T := Mach.
FEnd Stacking.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction Comp.Stacking.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
