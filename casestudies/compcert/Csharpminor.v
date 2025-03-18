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

Family Csharpminor extends Cfam.

FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant.

FInductive expr : Type :=
| Econst : constant -> expr (* constants *)
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)                                    
                                                                              
FInductive stmt : Type :=
| Sifthenelse: expr -> stmt -> stmt -> stmt.
       
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
(* ------------------------------------------------ *)
(*             Semantics for Csharpminor            *)
(* ------------------------------------------------ *)
(* function stack environment *)       
FOverride Definition fenv := PTree.t (block * Z).
FOverride Definition empty_fenv := PTree.empty (block * Z).

FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
 match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
  List.map block_of_binding (PTree.elements e).

FOverride Definition free_fenv := fun m e f => Mem.free_list m (blocks_of_env e).
   
MetaData alloc_variables.
Inductive alloc_variables: self__Csharpminor.fenv -> mem ->
               list (ident * Z) ->
               self__Csharpminor.fenv -> mem -> Prop :=
| alloc_variables_nil:
  forall e m,
    alloc_variables e m nil e m
| alloc_variables_cons:
  forall e m id sz vars m1 b1 m2 e2,
    Mem.alloc m 0 sz = (m1, b1) ->
    alloc_variables (PTree.set id (b1, sz) e) m1 vars e2 m2 ->
    alloc_variables e m ((id, sz) :: vars) e2 m2.
FEnd alloc_variables.
         
FOverride Definition alloc_fenv := fun e m f e' m' => 
  list_norepet (map fst f.(self__Csharpminor.fn_vars)) /\
  list_norepet f.(self__Csharpminor.fn_params) /\
  list_disjoint f.(self__Csharpminor.fn_params) f.(self__Csharpminor.fn_temps) /\
  alloc_variables self__Csharpminor.empty_fenv m (self__Csharpminor.fn_vars f) e m'.

FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
Case Ointconst := (fun n => Some (Vint n)). 
Case Ofloatconst := (fun n => Some (Vfloat n)).
Case Osingleconst := (fun n => Some (Vsingle n)).
Case Olongconst := (fun n => Some (Vlong n)).
FEnd eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
  | eval_Econst: forall ge lenv e le m cst v,
      eval_constant cst = Some v ->
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
    step ge (self__Csharpminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Csharpminor.State f (if b then s1 else s2) k sp e m)
| step_internal_function: forall ge f vargs k m m1 e le,
   Val.has_argtype_list vargs (self__Csharpminor.fn_sig f).(sig_args) ->
   list_norepet (map fst (self__Csharpminor.fn_vars f)) ->
   list_norepet (self__Csharpminor.fn_params f) ->
   list_disjoint (self__Csharpminor.fn_params f) (self__Csharpminor.fn_temps f) ->
   alloc_variables empty_fenv m (self__Csharpminor.fn_vars f) e m1 ->
   bind_parameters (self__Csharpminor.fn_params f) vargs (create_undef_temps (self__Csharpminor.fn_temps f)) = Some le ->
   step ge (Callstate (AST.Internal f) vargs k m)
     E0 (State f (self__Csharpminor.fn_body f) k e le m1).
FEnd Csharpminor.

FEnd Base.

Trait Comp_Loops extends Base.

Family Csharpminor extends Cfam. FEnd Csharpminor.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

Family Csharpminor extends Cfam.

FInductive stmt : Type :=
| Sswitch: bool -> expr -> lbl_stmts -> stmt
with lbl_stmts : Type :=
  | LSnil: lbl_stmts
  | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

From Rocqet Require Import Switch.

FRecursion select_switch_default about lbl_stmts motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons opt s sl' :=
  (match opt with
   | None => LScons opt s sl'
   | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons opt s sl' :=
  (fun n =>
     match opt with
     | None => select_switch_case sl' n
     | Some c => if zeq c n then Some (LScons opt s sl')  else select_switch_case sl' n
     end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FRecursion seq_of_lbl_stmt about lbl_stmts motive (fun (_: lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons c s sl' := (Sseq s (seq_of_lbl_stmt sl')).
FEnd seq_of_lbl_stmt.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) 
  with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sswitch long a sl := 
  (fun lbl k => find_label_ls sl lbl k).

Case LSnil := (fun lbl k => None).
Case LScons x s sl' :=
  (fun lbl k =>
     match find_label s lbl (Kseq (seq_of_lbl_stmt sl') k) with
     | Some sk => Some sk
     | None => find_label_ls sl' lbl k
     end).
FEnd find_label with find_label_ls.
      
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f islong a cases k e le m v n lenv,
      eval_expr ge e le m lenv a v ->
      switch_argument islong v n ->
      step ge (State f (Sswitch islong a cases) k e le m)
        E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m).

FEnd Csharpminor.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base.

Family Csharpminor extends Cfam.
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
FEnd Csharpminor.

FEnd Comp_Builtin.

Trait Comp_External extends Base.

Family Csharpminor extends Cfam. FEnd Csharpminor.

FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Family Csharpminor extends Cfam.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge lenv f optid sig a bl k e le m vf vargs fd,
      eval_expr ge e le m lenv a vf ->
      eval_exprlist ge e le m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step ge (State f (Scall optid sig a bl) k e le m)
        E0 (Callstate fd vargs (Kcall optid f le e k) m).
FEnd Csharpminor.

FEnd Comp_Call.

Trait Comp_Heap extends Base, Comp_Builtin.

Trait Csharpminor_Eaddrof extends Csharpminor.

FInductive expr : Type :=
  | Eaddrof : ident -> expr. (* taking the address of a variable *)


Inherit letenv.

MetaData eval_var_addr.
Inductive eval_var_addr: genv -> fenv -> ident -> block -> Prop :=
  | eval_var_addr_local:
      forall ge e id b sz,
      PTree.get id e = Some (b, sz) ->
      eval_var_addr ge e id b
  | eval_var_addr_global:
      forall ge e id b,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      eval_var_addr ge e id b.
FEnd eval_var_addr.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eaddrof: forall ge le e lenv m id b,
      eval_var_addr ge le id b ->
      eval_expr ge le e m lenv (Eaddrof id) (Vptr b Ptrofs.zero).
                
FEnd Csharpminor_Eaddrof.

Trait Csharpminor_Eload extends Csharpminor.
FInductive expr : Type :=
| Eload : memory_chunk -> expr -> expr. (* memory read *)

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eload: forall ge le e lenv m chunk a v1 v,
      eval_expr ge le e m lenv a v1 ->
      Mem.loadv chunk m v1 = Some v ->
      eval_expr ge le e m lenv (Eload chunk a) v.
  
FEnd Csharpminor_Eload.

Trait Csharpminor_Sstore extends Csharpminor.
FInductive stmt : Type :=
| Sstore : memory_chunk -> expr -> expr -> stmt.

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
  
FEnd Csharpminor_Sstore.

Family Csharpminor extends 
  Csharpminor_Sstore, 
  Csharpminor_Eload, 
  Csharpminor_Eaddrof.
FEnd Csharpminor.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Csharpminor.
FEnd Csharpminor.

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
