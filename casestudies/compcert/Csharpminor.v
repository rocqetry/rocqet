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

Family Csharpminor.

FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant.

FInductive expr : Type :=
| Evar : ident -> expr (* reading a temporary variable *)                                           
| Econst : constant -> expr (* constants *)
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)                                    

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt  
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
FDefinition function := fn.
FDefinition function_body := self__Csharpminor.fn_body.
FDefinition function_locals := self__Csharpminor.fn_temps.
FDefinition function_params := self__Csharpminor.fn_params.
FDefinition function_sig := self__Csharpminor.fn_sig.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

(* ------------------------------------------------ *)
(*             Semantics for Csharpminor            *)
(* ------------------------------------------------ *)
(* function stack environment *)

FDefinition genv := Genv.t fundef unit.

FDefinition fenv := PTree.t (block * Z).
FDefinition empty_fenv := PTree.empty (block * Z).

FDefinition env := PTree.t val.            
FDefinition empty_env : env := PTree.empty val.

FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
 match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

MetaData set_params.
Fixpoint set_params (vl: list val) (il: list ident) {struct il} : self__Csharpminor.env :=
 match il, vl with
 | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
 | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
 | _, _ => PTree.empty val
 end.
FEnd set_params.

MetaData set_locals.
Fixpoint set_locals (il: list ident) (e: self__Csharpminor.env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.
FEnd set_locals.
       
FDefinition init_env : function -> list val -> env := fun f vargs => 
  set_locals (function_locals f) (set_params vargs (function_params f)).            
FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
  List.map block_of_binding (PTree.elements e).

FDefinition free_fenv : mem -> fenv -> function -> option mem := fun m e f => Mem.free_list m (blocks_of_env e).
   
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
         
FDefinition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := fun e m f e' m' => 
  list_norepet (map fst f.(self__Csharpminor.fn_vars)) /\
  list_norepet f.(self__Csharpminor.fn_params) /\
  list_disjoint f.(self__Csharpminor.fn_params) f.(self__Csharpminor.fn_temps) /\
    alloc_variables self__Csharpminor.empty_fenv m (self__Csharpminor.fn_vars f) e m'.

MetaData create_undef_temps.
Fixpoint create_undef_temps (temps: list ident) : self__Csharpminor.env :=
 match temps with
 | nil => PTree.empty val
 | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
end.
FEnd create_undef_temps.

MetaData bind_parameters.
Fixpoint bind_parameters (formals: list ident) (args: list val)
             (le: self__Csharpminor.env) : option self__Csharpminor.env :=
 match formals, args with
 | nil, nil => Some le
 | id :: xl, v :: vl => bind_parameters xl vl (PTree.set id v le)
 | _, _ => None
 end.
FEnd bind_parameters.
            
FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.
                   
MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State:(* Execution within a function *)
      forall (f: function)(* currently executing function *)
             (s: stmt)(* statement under consideration *)
             (k:  cont)(* its continuation -- what to do next *)
             (sp: fenv) (* current "function" environment: i.e stackspace, ... *)
             (e: env)(* current local environment *)
             (m: mem),(* current memory state *)
      state
  | Callstate:(* Invocation of a function *)
      forall (f: fundef)(* function to invoke *)
             (args: list val)(* arguments provided by caller *)
             (k: cont)(* what to do next *)
             (m: mem),(* memory state *)
      state
  | Returnstate:(* Return from a function *)
      forall (v: val)(* Return value *)
             (k: cont)(* what to do next *)
             (m: mem),(* memory state *)
      state.
FEnd state.
            
FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq s c := (call_cont c).             
FEnd call_cont.
               
FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
Case Kstop := True.                   
Case Kseq s c := False.
FEnd is_call_cont.              

FDefinition letenv := list val.

FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
Case Ointconst := (fun n => Some (Vint n)). 
Case Ofloatconst := (fun n => Some (Vfloat n)).
Case Osingleconst := (fun n => Some (Vsingle n)).
Case Olongconst := (fun n => Some (Vlong n)).
FEnd eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Evar: forall ge lenv e le m id v,
    PTree.get id le = Some v ->
    eval_expr ge e le m lenv (Evar id) v  
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

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sifthenelse a s1 s2 := 
(fun lbl k => 
   match find_label s1 lbl k with
   | Some sk => Some sk
   | None => find_label s2 lbl k
   end).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
    step ge (State f Sskip (Kseq s k) e le m)
      E0 (State f s k e le m)              
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->                       
    free_fenv m e f = Some m' ->
    step ge (State f Sskip k e le m)
      E0 (Returnstate Vundef k m')
| step_assign: forall lenv ge f id a k e le m v,
    eval_expr ge e le m lenv a v ->
    step ge (State f (Sassign id a) k e le m)
      E0 (State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
    step ge (State f (Sseq s1 s2) k e le m)
      E0 (State f s1 (Kseq s2 k) e le m)              
| step_return_0: forall ge f k e le m m',                       
    free_fenv m e f = Some m' ->
    step ge (State f (Sreturn None) k e le m)
      E0 (Returnstate Vundef (call_cont k) m')    
| step_return_1: forall lenv ge f a k e le m v m',
    eval_expr ge e le m lenv a v ->
    free_fenv m e f = Some m' ->
    step ge (State f (Sreturn (Some a)) k e le m)
      E0 (Returnstate v (call_cont k) m')
| step_label: forall ge f lbl s k e le m,
      step ge (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
      find_label (function_body f) lbl (call_cont k) = Some(s', k') ->
      step ge (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)  
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

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->               
    initial_state p (Callstate f nil Kstop m0).
FEnd initial_state.
            
MetaData final_state.
Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
   final_state (Returnstate (Vint r) Kstop m) r.
FEnd final_state.

FEnd Csharpminor.
FEnd Base.

Trait Comp_Loops extends Base.

Family Csharpminor.
FInductive stmt : Type :=
| Sloop: stmt -> stmt
| Sblock: stmt -> stmt
| Sexit: nat -> stmt.

FInductive cont: Type :=
| Kblock: cont -> cont.  

FRecursion call_cont.
Case Kblock k := (call_cont k).
FEnd call_cont.
               
FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label.
Case Sloop s1 :=
   (fun lbl k => find_label s1 lbl (Kseq (Sloop s1) k)).
Case Sblock s1 := 
  (fun lbl k => find_label s1 lbl (Kblock k)).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_block: forall ge f k sp e m,
      step ge (State f Sskip (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)  
| step_loop: forall ge f s k sp e m,
      step ge (State f (Sloop s) k sp e m)
        E0 (State f s (Kseq (Sloop s) k) sp e m)
| step_block: forall ge f s k e le m,
      step ge (State f (Sblock s) k e le m)
        E0 (State f s (Kblock k) e le m)
| step_exit_seq: forall ge f n s k e le m,
      step ge (State f (Sexit n) (Kseq s k) e le m)
        E0 (State f (Sexit n) k e le m)
| step_exit_block_0: forall ge f k e le m,
      step ge (State f (Sexit O) (Kblock k) e le m)
        E0 (State f Sskip k e le m)
| step_exit_block_S: forall ge f n k e le m,
      step ge (State f (Sexit (S n)) (Kblock k) e le m)
        E0 (State f (Sexit n) k e le m).
FEnd Csharpminor.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

Family Csharpminor.

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

Family Csharpminor.
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

Family Csharpminor.
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_external_function: forall ge ef vargs k m t vres m',
   external_call ef (Genv.to_senv ge) vargs m t vres m' ->
   step ge (Callstate (AST.External ef) vargs k m)
      t (Returnstate vres k m').
FEnd Csharpminor.

FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Family Csharpminor.
FInductive stmt : Type :=
  | Scall : option ident -> signature -> expr -> list expr -> stmt.

FInductive cont: Type :=
  | Kcall: option ident -> function -> env -> fenv -> cont -> cont.

FRecursion call_cont.
Case Kcall a b c d e := (Kcall a b c d e).
FEnd call_cont.
               
FRecursion is_call_cont.
Case Kcall a b c d e := True.
FEnd is_call_cont.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_return: forall ge v optid f sp e k m,
      step ge (Returnstate v (Kcall optid f e sp k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m)  
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
