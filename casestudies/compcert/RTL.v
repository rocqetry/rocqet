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

Family RTL.
FDefinition node := positive.

From Rocqet Require Import Registers.
      
FInductive instruction: Type :=
| Inop: node -> instruction
| Iop: operation -> list reg -> reg -> node -> instruction          
| Icond: condition -> list reg -> node -> node -> instruction
| Ireturn: option reg -> instruction.

FDefinition code: Type := PTree.t instruction.

MetaData function binds fn_sig, fn_params, fn_stacksize, fn_code, fn_entrypoint.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.
FEnd function.

FDefinition fundef := AST.fundef function.

FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => fn_sig f
  | AST.External ef => ef_sig ef
  end.

(* operational semantics *)             
FDefinition genv := Genv.t fundef unit.
FDefinition regset := Regmap.t val.

MetaData init_regs.
Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.
FEnd init_regs.

MetaData stackframe binds Stackframe.
Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)(* where to store the result *)
             (f: function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (pc: node)(* program point in calling function *)
             (rs: regset),(* register state in calling function *)
      stackframe.
FEnd stackframe.

MetaData state binds State, Callstate, Returnstate.
Inductive state : Type :=
  | State:
      forall (stack: list stackframe)(* call stack *)
             (f: function)(* current function *)
             (sp: val)(* stack pointer *)
             (pc: node)(* current program point in c *)
             (rs: regset)(* register state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)(* call stack *)
             (f: fundef)(* function to call *)
             (args: list val)(* arguments to the call *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)(* call stack *)
             (v: val)(* return value for the call *)
             (m: mem),(* memory state *)
      state.           
FEnd state.
           
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Inop:
    forall ge s f sp pc rs m pc',
    (self__RTL.fn_code f)!pc = Some(Inop pc') ->
    step ge (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Iop:
    forall ge s f sp pc rs m op args res pc' v,
    (self__RTL.fn_code f)!pc = Some(Iop op args res pc') ->
    eval_operation ge sp op rs##args m = Some v ->
    step ge (State s f sp pc rs m)
      E0 (State s f sp pc' (rs#res <- v) m)
| exec_Icond:
    forall ge s f sp pc rs m cond args ifso ifnot b pc',
    (self__RTL.fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
    eval_condition cond rs##args m = Some b ->
    pc' = (if b then ifso else ifnot) ->
    step ge (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Ireturn:
    forall ge s f stk pc rs m or m',
    (self__RTL.fn_code f)!pc = Some(Ireturn or) ->
    Mem.free m stk 0 (fn_stacksize f) = Some m' ->
    step ge (State s f (Vptr stk Ptrofs.zero) pc rs m)
      E0 (Returnstate s (regmap_optget or Vundef rs) m')
| exec_function_internal:
    forall ge s f args m m' stk,
    Mem.alloc m 0 (fn_stacksize f) = (m', stk) ->
    step ge (Callstate s (AST.Internal f) args m)
      E0 (State s
                f
                (Vptr stk Ptrofs.zero)
                (fn_entrypoint f)
                (init_regs args (fn_params f))
                m')      
| exec_return:
    forall ge res f sp pc rs s vres m,
    step ge (Returnstate (Stackframe res f sp pc rs :: s) vres m)
      E0 (State s f sp pc (rs#res <- vres) m).

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->
    initial_state p (Callstate nil f nil m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
   | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.
FEnd final_state.

FEnd RTL.

FEnd Base.

Trait Comp_Loops extends Base.

Trait RTL_jumptable extends RTL.
FInductive instruction: Type :=
| Ijumptable: reg -> list node -> instruction.  

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ijumptable:
   forall ge s f sp pc rs m arg tbl n pc',
   (fn_code f)!pc = Some(Ijumptable arg tbl) ->
   rs#arg = Vint n ->
   list_nth_z tbl (Int.unsigned n) = Some pc' ->
   step ge (State s f sp pc rs m)
     E0 (State s f sp pc' rs m).

FEnd RTL_jumptable.

Family RTL extends RTL_jumptable.
FEnd RTL.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family RTL.
FInductive instruction: Type :=
| Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ibuiltin:
      forall ge s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args (Genv.to_senv ge) (fun r => rs#r) sp m args vargs ->
      external_call ef (Genv.to_senv ge) vargs m t vres m' ->
      step ge (State s f sp pc rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m').
  
FEnd RTL.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family RTL.
FInductive instruction: Type :=
| Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
| Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Iload:
      forall ge s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step ge (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
| exec_Istore:
      forall ge s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step ge (State s f sp pc rs m)
        E0 (State s f sp pc' rs m').
  
FEnd RTL.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.
FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family RTL.
FInductive instruction: Type :=
| Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
| Itailcall: signature -> reg + ident -> list reg -> instruction.

Inherit genv.
Inherit regset.

FDefinition find_function :
       genv -> reg + ident -> regset -> option fundef := fun ge ros rs =>
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Icall:
   forall ge s f sp pc rs m sig ros args res pc' fd,
   (fn_code f)!pc = Some(Icall sig ros args res pc') ->
   find_function ge ros rs = Some fd ->
   funsig fd = sig ->
   step ge (State s f sp pc rs m)
     E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
| exec_Itailcall:
   forall ge s f stk pc rs m sig ros args fd m',
   (fn_code f)!pc = Some(Itailcall sig ros args) ->
   find_function ge ros rs = Some fd ->
   funsig fd = sig ->
   Mem.free m stk 0 (fn_stacksize f) = Some m' ->
   step ge (State s f (Vptr stk Ptrofs.zero) pc rs m)
     E0 (Callstate s fd rs##args m')
| exec_function_external:
      forall ge s ef args res t m m',
        external_call ef (Genv.to_senv ge) args m t res m' ->
      step ge (Callstate s (AST.External ef) args m)
         t (Returnstate s res m')
| exec_return:
      forall ge res f sp pc rs s vres m,
      step ge (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

FEnd RTL.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.
FEnd Comp_Switch.

(*Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin. 

Family RTLgen.
Final Family S := CminorSel.
Final Family T := RTL.
FEnd RTLgen.

FEnd Comp.*)

Require Extraction.
Cd "extraction".
Separate Extraction Comp.RTLgen.
           
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
