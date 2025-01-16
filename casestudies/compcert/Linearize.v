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

Trait Base.

From Rocqet Require Import Registers.     

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.


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

MetaData function binds fn_sig, fn_stacksize, fn_code, fn_entrypoint.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.
FEnd function.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => self__LTL.fn_sig f
  | AST.External ef => ef_sig ef
  end.

FDefinition genv := Genv.t fundef unit.
FDefinition locset := Locmap.t.

MetaData stackframe binds Stackframe.
Inductive stackframe : Type :=
  | Stackframe:
      forall (f: function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (ls: locset)(* location state in calling function *)
             (bb: bblock),(* continuation in calling function *)
        stackframe.
FEnd stackframe.

MetaData state binds State, Block, Callstate, Returnstate.
Inductive state : Type :=
  | State:
      forall (stack: list stackframe)(* call stack *)
             (f: function)(* function currently executing *)
             (sp: val)(* stack pointer *)
             (pc: node)(* current program point *)
             (ls: locset)(* location state *)
             (m: mem),(* memory state *)
      state
  | Block:
      forall (stack: list stackframe)(* call stack *)
             (f: function)(* function currently executing *)
             (sp: val)(* stack pointer *)
             (bb: bblock)(* current basic block *)
             (ls: locset)(* location state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)(* call stack *)
             (f: fundef)(* function to call *)
             (ls: locset)(* location state of caller *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)(* call stack *)
             (ls: locset)(* location state of callee *)
             (m: mem),(* memory state *)
        state.
FEnd state.

FDefinition reglist : locset -> list mreg -> list val := fun rs rl => 
  List.map (fun r => rs (R r)) rl.

MetaData undef_regs.
Fixpoint undef_regs (rl: list mreg) (rs: locset) : locset :=
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
    (fn_code f)!pc = Some bb ->
    step ge (State s f sp pc rs m)
      E0 (Block s f sp bb rs m)      
| exec_Lop: forall ge s f sp op args res bb rs m v rs',
    eval_operation ge sp op (reglist rs args) m = Some v ->
    rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
    step ge (Block s f sp (Lop op args res :: bb) rs m)
      E0 (Block s f sp bb rs' m)      
| exec_Lgetstack: forall ge s f sp sl ofs ty dst bb rs m rs',
    rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
    step ge (Block s f sp (Lgetstack sl ofs ty dst :: bb) rs m)
      E0 (Block s f sp bb rs' m)      
| exec_Lsetstack: forall ge s f sp src sl ofs ty bb rs m rs',
    rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
    step ge (Block s f sp (Lsetstack src sl ofs ty :: bb) rs m)
      E0 (Block s f sp bb rs' m)      
| exec_Lbranch: forall ge s f sp pc bb rs m,
    step ge (Block s f sp (Lbranch pc :: bb) rs m)
      E0 (State s f sp pc rs m)     
| exec_Lcond: forall ge s f sp cond args pc1 pc2 bb rs b pc rs' m,
    eval_condition cond (reglist rs args) m = Some b ->
    pc = (if b then pc1 else pc2) ->
    rs' = undef_regs (destroyed_by_cond cond) rs ->
    step ge (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs m)
      E0 (State s f sp pc rs' m)
| exec_Lreturn: forall ge s f sp bb rs m m',
    Mem.free m sp 0 (fn_stacksize f) = Some m' ->
    step ge (Block s f (Vptr sp Ptrofs.zero) (Lreturn :: bb) rs m)
      E0 (Returnstate s (return_regs (parent_locset s) rs) m')
| exec_return: forall ge f sp rs1 bb s rs m,
    step ge (Returnstate (Stackframe f sp rs1 bb :: s) rs m)
      E0 (Block s f sp bb rs m)
 | exec_function_internal: forall ge s f rs m m' sp rs',
      Mem.alloc m 0 (fn_stacksize f) = (m', sp) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step ge (Callstate s (AST.Internal f) rs m)
        E0 (State s f (Vptr sp Ptrofs.zero) (fn_entrypoint f) rs' m').

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

FRecursion successors_instr about instruction motive (fun (_ : instruction) =>  list node -> list node) by _rect.
Case Lop op args dst := (fun rest => rest).
Case Lgetstack a b c d := (fun rest => rest). 
Case Lsetstack a b c d := (fun rest => rest).
Case Lbranch s := (fun _  => s :: nil).
Case Lcond cond args s1 s2 := (fun _ => s1 :: s2 :: nil).
Case Lreturn := (fun rest => nil).
FEnd successors_instr.

MetaData successors_block.
Fixpoint successors_block (b: bblock) : list node :=
  match b with
  | nil => nil(* should never happen *)
  | op :: b' => successors_instr op (successors_block b')
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
    forall (f: func_ptr)(* calling function *)
           (sp: val)(* stack pointer in calling function *)
           (ls: stack_state)(* location state in calling function *)
           (bb: code), (* program point in calling function *)
      stackframe.
FEnd stackframe.

MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
| State:
    forall (stack: list stackframe)(* call stack *)
           (f: func_ptr)(* function currently executing *)
           (sp: val)(* stack pointer *)
           (c: code)(* current program point *)
           (rs: storeset)(* location state *)
           (m: mem),(* memory state *)
    state
| Callstate:
    forall (stack: list stackframe)(* call stack *)
           (f: call_func_ptr)(* function to call *)
           (rs: storeset)(* location state at point of call *)
           (m: mem),(* memory state *)
    state
| Returnstate:
    forall (stack: list stackframe)(* call stack *)
           (rs: storeset)(* location state at point of return *)
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
Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label i1 lbl then Some il else find_label lbl il
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

MetaData fn binds fn_sig, fn_code, fn_stacksize.
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
FEnd final_state.

FEnd Linear.

(* LTL -> Linear *)
Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

From Rocqet Require Import Lattice.
From Rocqet Require Import Kildall.

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

From Rocqet Require Import Errors.
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

(* correctness *)

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

(*
Variable prog: LTL.program.
Variable tprog: Linear.program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
*)

MetaData match_stackframes.
Inductive match_stackframes: S.stackframe -> T.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp bb ls tf c,
      transf_function f = OK tf ->
      (forall pc, In pc (S.successors_block bb) -> (reachable f)!!pc = true) ->
      is_tail c tf.(T.fn_code) ->
      match_stackframes
        (S.Stackframe f sp ls bb)
        (T.Stackframe tf sp ls (linearize_block bb c)).
FEnd match_stackframes.

FInductive match_states: S.state -> T.state -> Prop :=
  | match_states_add_branch:
      forall s f sp pc ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (TAIL: is_tail c (T.fn_code tf)),
      match_states (S.State s f sp pc ls m)
                   (T.State ts tf sp (add_branch pc c) ls m)
  | match_states_cond_taken:
      forall s f sp pc ls m tf ts cond args c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (JUMP: eval_condition cond (S.reglist ls args) m = Some true),
      match_states (S.State s f sp pc (S.undef_regs (destroyed_by_cond cond) ls) m)
                   (T.State ts tf sp (T.Lcond cond args pc :: c) ls m)
  | match_states_block:
      forall s f sp bb ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: forall pc, In pc (S.successors_block bb) -> (reachable f)!!pc = true)
        (TAIL: is_tail c (T.fn_code tf)),
      match_states (S.Block s f sp bb ls m)
                   (T.State ts tf sp (linearize_block bb c) ls m)
  | match_states_call:
      forall s f ls m tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (S.Callstate s f ls m)
                   (T.Callstate ts tf ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (S.Returnstate s ls m)
                   (T.Returnstate ts ls m).

FDefinition measure := fun (S0: S.state) =>
  match S0 with
  | self__Linearize.S.State s f sp pc ls m => 0%nat
  | self__Linearize.S.Block s f sp bb ls m => 1%nat
  | _ => 0%nat
  end.

FInduction transf_step_correct about S.step
  motive (fun ge s1 t s2 (_ : S.step ge s1 t s2) =>    
    forall prog tprog tge (TRANSF: match_prog prog tprog) s1' (MS: match_states s1 s1'),
    ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
    (exists s2', plus T.step tge s1' t s2' /\ match_states s2 s2')
    \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat).
FProof.
(* start of block, at an [add_branch] *)
+ apply cheat.
 (* Lop *)  
+ apply cheat.
(* Lgetstack *)  
+ apply cheat.
(* Lsetstack *)  
+ apply cheat.
(* Lbranch *)  
+ apply cheat.
(* Lcond *)  
+ apply cheat.
(* Lreturn *)  
+ apply cheat.
(* return *)  
+ apply cheat.
(* internal functions *)  
+ apply cheat.  
Qed. FEnd transf_step_correct.

FEnd Linearize.  

FEnd Base.

Trait Comp_Loops extends Base.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Trait LTL_jumptable extends LTL.
FInductive instruction: Type :=
| Ljumptable : mreg -> list node -> instruction.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ljumptable: forall ge s f sp arg tbl bb rs m n pc rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step ge (Block s f sp (Ljumptable arg tbl :: bb) rs m)
        E0 (State s f sp pc rs' m).
  
FRecursion successors_instr.
Case Ljumptable a tbl := (fun rest => tbl).
FEnd successors_instr.
FEnd LTL_jumptable.

Family LTL extends LTL_jumptable.
FEnd LTL.

Family Linear.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

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

Family Linearize.

FRecursion starts_with_label.
Case Ljumptable a b  := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Ljumptable args tbl := (fun f k => T.Ljumptable args tbl :: k).
FEnd translate_instr.

FInduction transf_step_correct.
FProof.
(* Ljumptable *)
+ apply cheat.
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family LTL.
FInductive instruction: Type :=
| Lbuiltin : external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction.   

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin: forall ge s f sp ef args res bb rs m vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (Block s f sp (Lbuiltin ef args res :: bb) rs m)
        t (Block s f sp bb rs' m').

FRecursion successors_instr.
Case Lbuiltin a b c := (fun rest => rest).
FEnd successors_instr.

FEnd LTL.

Family Linear.
FInductive instruction: Type :=
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

Family Linearize.

FRecursion starts_with_label.
Case _ := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lbuiltin ef args res := (fun f k => T.Lbuiltin ef args res ::f k).
FEnd translate_instr.

FInduction transf_step_correct.
FProof.
(* Lbuiltin *)
+ apply cheat.
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family LTL.
FInductive instruction: Type :=
| Lload : memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore : memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lload: forall ge s f sp chunk addr args dst bb rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step ge (Block s f sp (Lload chunk addr args dst :: bb) rs m)
        E0 (Block s f sp bb rs' m)
| exec_Lstore: forall ge s f sp chunk addr args src bb rs m a rs' m',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step ge (Block s f sp (Lstore chunk addr args src :: bb) rs m)
        E0 (Block s f sp bb rs' m').

FRecursion successors_instr.
Case _ := (fun rest => rest).
FEnd successors_instr.

FEnd LTL.

Family Lfam.
(*FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.*)
FEnd Lfam.

Family Linear extends Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

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

Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

FRecursion starts_with_label.
Case Lstore a b c d := (fun lbl => false).
Case Lload a b c d := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lstore chunk addr args src := (fun f k => T.Lstore chunk addr args src :: f k).
Case Lload chunk addr args dst := (fun f k => T.Lload chunk addr args dst :: f k).
FEnd translate_instr.

FInduction transf_step_correct.
FProof.
(* Lload *)
+ apply cheat.
(* Lstore *)  
+ apply cheat.  
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap. FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family LTL.
FInductive instruction: Type :=
| Lcall : signature -> mreg + ident -> instruction
| Ltailcall : signature -> mreg + ident -> instruction. 

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
| exec_Lcall: forall ge s f sp sig ros bb rs m fd,
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      step ge (Block s f sp (Lcall sig ros :: bb) rs m)
        E0 (Callstate (Stackframe f sp rs bb :: s) fd rs m)
| exec_Ltailcall: forall ge s f sp sig ros bb rs m fd rs' m',
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 (fn_stacksize f) = Some m' ->
      step ge (Block s f (Vptr sp Ptrofs.zero) (Ltailcall sig ros :: bb) rs m)
        E0 (Callstate s fd rs' m').

FRecursion successors_instr.
Case _ := (fun rest => rest).
FEnd successors_instr.

FEnd LTL.

Family Lfam.
(*FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.*)
FEnd Lfam.   

Family Linear extends Lfam.
FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FDefinition find_function := fun (ge: genv) (ros: mreg + ident) (rs: storeset) =>
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

FDefinition return_regs := fun (caller callee: storeset) =>
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then caller (R r) else callee (R r)
    | S Outgoing ofs ty => Vundef
    | S sl ofs ty => caller (S sl ofs ty)
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


Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

FRecursion starts_with_label.
Case Lcall a b := (fun lbl => false).
Case Ltailcall a b := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lcall sig ros := 
  (fun f k => T.Lcall sig ros :: f k).
Case Ltailcall sig ros := 
 (fun f k => T.Ltailcall sig ros :: k).
FEnd translate_instr.

FInduction transf_step_correct.
FProof.
(* Lcall *)
+ apply cheat.
(* Ltailcall *)
+ apply cheat.
Qed. FEnd transf_step_correct.
  
FEnd Linearize.

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

Family Linearize.
Final Family S := LTL.
Final Family T := Linear.
FEnd Linearize.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
