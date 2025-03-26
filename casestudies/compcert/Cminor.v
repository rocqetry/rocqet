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

Require Import CfamBase.

Trait Base.

Family Cminor extends Cfam.

FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant (* long integer constant *)
| Oaddrsymbol: ident -> ptrofs -> constant (* address of the symbol plus the offset *)
| Oaddrstack: ptrofs -> constant. (* stack pointer plus the given offset *)

FInductive expr : Type :=
| Econst : constant -> expr (* constants *)
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)

FInductive stmt : Type :=
| Sifthenelse: expr -> stmt -> stmt -> stmt.
        
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

(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FOverride Definition fenv := block.
   
FOverride Definition free_fenv := fun m sp f =>
  Mem.free m sp 0 f.(self__Cminor.fn_stackspace).
          
FOverride Definition alloc_fenv := fun sp m f sp' m' => 
   Mem.alloc m 0 f.(self__Cminor.fn_stackspace) = (m', sp).

FRecursion eval_constant about constant motive (fun (_ : constant) => genv -> fenv -> option val) by _rect.
Case Ointconst n := (fun ge sp => Some (Vint n)). 
Case Ofloatconst n := (fun ge sp => Some (Vfloat n)).
Case Osingleconst n := (fun ge sp => Some (Vsingle n)).
Case Olongconst n := (fun ge sp => Some (Vlong n)).
Case Oaddrstack ofs := (fun ge sp => Some (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs)).
Case Oaddrsymbol s ofs := (fun ge sp => Some (Genv.symbol_address ge s ofs)).
FEnd eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
  | eval_Econst: forall ge lenv e le m cst v,
      eval_constant cst ge e = Some v ->
      eval_expr ge e le m lenv (Econst cst) v
  | eval_Eunop: forall ge lenv e le m op a1 v1 v,
      eval_expr ge e le m lenv a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr ge e le m lenv (Eunop op a1) v
  | eval_Ebinop: forall ge lenv e le m op a1 a2 v1 v2 v,
      eval_expr ge e le m lenv a1 v1 ->
      eval_expr ge e le m lenv a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr ge e le m lenv (Ebinop op a1 a2) v.              

FRecursion find_label.
Case Sifthenelse a s1 s2 := 
(fun lbl k => 
   match find_label s1 lbl k with
   | Some sk => Some sk
   | None => find_label s2 lbl k
   end).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Cminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Cminor.State f (if b then s1 else s2) k sp e m)
| step_internal_function: forall ge f vargs k m m' sp e,
      Val.has_argtype_list vargs (self__Cminor.fn_sig f).(sig_args) ->
      Mem.alloc m 0 (self__Cminor.fn_stackspace f) = (m', sp) ->
      set_locals (self__Cminor.fn_vars f) (set_params vargs (self__Cminor.fn_params f)) = e ->
      step ge (Callstate (AST.Internal f) vargs k m)
        E0 (State f (self__Cminor.fn_body f) k sp e m').
FEnd Cminor.

FEnd Base.

(* very small, just merge into base compiler *)
(* Trait Comp_Float extends Base.

Family Cminor.

FInductive constant : Type :=
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant. (* single-precision floating-point constant *)       

FRecursion eval_constant.
Case Ofloatconst n := (fun ge sp => Some (Vfloat n)).
Case Osingleconst n := (fun ge sp => Some (Vsingle n)).
FEnd eval_constant.

FEnd Cminor.

FEnd Comp_Float. *)

Trait Comp_Loops extends Base.

Family Cminor extends Cfam. FEnd Cminor.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

From Rocqet Require Import Switch.

Family Cminor extends Cfam.

FInductive stmt : Type :=
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f islong a cases default k sp e m v n lenv,
   eval_expr ge sp e m lenv a v ->
   switch_argument islong v n ->
   step ge (State f (Sswitch islong a cases default) k sp e m)
     E0 (State f (Sexit (switch_target n default cases)) k sp e m).  

FEnd Cminor.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base.

Family Cminor extends Cfam.

FInductive stmt : Type :=
| Sbuiltin : option ident -> external_function -> list expr -> stmt.

Inherit eval_expr.

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> fenv -> env -> mem -> letenv -> list expr -> list val -> Prop :=
  | eval_Enil: forall ge lenv e le m,
      eval_exprlist ge le e m lenv nil nil
  | eval_Econs: forall ge le e m lenv a1 al v1 vl,
      eval_expr ge le e m lenv a1 v1 -> eval_exprlist ge le e m lenv al vl ->
      eval_exprlist ge le e m lenv (a1 :: al) (v1 :: vl).
FEnd eval_exprlist.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f lenv optid ef bl k e le m vargs t vres m',
   eval_exprlist ge e le m lenv bl vargs ->
   external_call ef ge vargs m t vres m' ->
   step ge (State f (Sbuiltin optid ef bl) k e le m)
     t (State f Sskip k e (set_optvar optid vres le) m').

FEnd Cminor.

FEnd Comp_Builtin.

Trait Comp_External extends Base, Comp_Builtin.
  Family Cminor extends Cfam. FEnd Cminor.
FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Family Cminor extends Cfam.

FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt
| Stailcall: signature -> expr -> list expr -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge lenv f optid sig a bl k e le m vf vargs fd,
      eval_expr ge le e m lenv a vf ->
      eval_exprlist ge le e m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step ge (State f (Scall optid sig a bl) k le e m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)
| step_tailcall: forall ge lenv f optid sig a bl k e le m m' vf vargs fd,
      eval_expr ge le e m lenv a vf ->
      eval_exprlist ge le e m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m le 0 (self__Cminor.fn_stackspace f) = Some m' ->
      step ge (State f (Scall optid sig a bl) k le e m)
        E0 (Callstate fd vargs (call_cont k) m'). 
FEnd Cminor.

FEnd Comp_Call.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Cminor extends Cfam.
FInductive expr : Type :=
 | Eload : memory_chunk -> expr -> expr.

FInductive stmt : Type :=                                                        
| Sstore : memory_chunk -> expr -> expr -> stmt.

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eload: forall ge sp e m chunk addr vaddr v lenv,
   eval_expr ge sp e m lenv addr vaddr ->
   Mem.loadv chunk m vaddr = Some v ->
   eval_expr ge sp e m lenv (Eload chunk addr) v.
           
FRecursion find_label.  
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_store: forall ge f chunk addr a k e le m vaddr v m' lenv,
      eval_expr ge e le m lenv addr vaddr ->
      eval_expr ge e le m lenv a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step ge (State f (Sstore chunk addr a) k e le m)
        E0 (State f Sskip k e le m').
FEnd Cminor.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Cminor extends Cfam.
FEnd Cminor.

FEnd Comp_Field.

(*Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  Comp_External,
  Comp_Builtin.

FEnd Comp. *)
