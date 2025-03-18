From Rocqet Require Import Loader.
From Rocqet Require Import LibTactics.

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

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family LTL.
FInductive instruction: Type :=
| Lbuiltin : external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction.   

Inherit locset.

FDefinition undef_caller_save_regs : locset -> locset := fun ls =>
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then ls (R r) else Vundef
    | S Outgoing ofs ty => Vundef
    | S sl ofs ty => ls (S sl ofs ty)
    end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin: forall ge s f sp ef args res bb rs m vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (Block s f sp (Lbuiltin ef args res :: bb) rs m)
        t (Block s f sp bb rs' m')
| exec_function_external: forall ge s ef t args res rs m rs' m',
      args = map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)) ->
      external_call ef (Genv.to_senv ge) args m t res m' ->
      rs' = Locmap.setpair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
      step ge (Callstate s (AST.External ef) rs m)
         t (Returnstate s rs' m').

FRecursion successors_instr.
Case Lbuiltin a b c := (fun rest => rest).
FEnd successors_instr.

FEnd LTL.

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

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family LTL.
FEnd LTL.

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

FEnd Comp. *)
