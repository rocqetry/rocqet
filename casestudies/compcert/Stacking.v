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

Trait Base.


Local Open Scope error_monad_scope.

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

FOverride Definition storeset := Locmap.t.
FOverride Definition func_ptr := function.
FOverride Definition call_func_ptr := fundef.
FOverride Definition stack_state := storeset.

FRecursion is_label.
Case Lgetstack s i t dst := (fun lbl => false).
Case Lsetstack d s i t := (fun lbl => false).
FEnd is_label.

FDefinition locset := Locmap.t.
FDefinition reglist' : locset -> list mreg -> list val := fun rs rl => 
  List.map (fun r => rs (R r)) rl.
MetaData undef_regs'.
Fixpoint undef_regs' (rl: list mreg) (rs: locset) : locset :=
  match rl with
  | nil => rs
  | r1 :: rl => Locmap.set (R r1) Vundef (undef_regs' rl rs)
  end.
FEnd undef_regs'.

FOverride Definition reglist := reglist'.
FOverride Definition undef_regs := undef_regs'.
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

FInductive step: genv -> state -> trace -> state -> Prop :=
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
    Mem.alloc m 0 (function_stacksize f) = (m', stk) ->
    rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
    step ge (Callstate s (AST.Internal f) rs m)
      E0 (State s f (Vptr stk Ptrofs.zero) (function_code f) rs' m')
| exec_Lreturn:
      forall ge s f stk b rs m m',
      Mem.free m stk 0 (function_stacksize f) = Some m' ->
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
FEnd final_state.

FEnd Mach.
   
(* Linear -> Mach *)
Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

From NFPOP Require Import Bounds.
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

From NFPOP Require Import Stacklayout.

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

FDefinition agree_regs := fun (j: meminj) (ls: S.storeset) (rs: T.storeset) =>
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
  split; auto. apply cheat. (*lia.  *)
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

FInduction transf_step_correct about S.step motive
  (fun ge s1 t s2 (_ : S.step ge s1 t s2) =>
     forall tge prog tprog (TRANSF: match_prog prog tprog),
     ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
     forall (*(WTS: wt_state s1)*) s1' (MS: match_states ge tge s1 s1'),
     exists s2', plus T.step tge s1' t s2' /\ match_states ge tge s2 s2').
FProof.
(* Llabel *)
+ apply cheat.
(* Lgoto *)
+ apply cheat.
(* Lop *)   
+ apply cheat.
(* Lcond true *)  
+ apply cheat.
(* Lcond false *)  
+ apply cheat.
(* return *)  
+ apply cheat.
(* Lgetstack *)  
+ apply cheat.
(* Lsetstack *)  
+ apply cheat.
(* internal function *)  
+ apply cheat.
(* Lreturn *)  
+ apply cheat.
Qed. FEnd transf_step_correct.

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
