(* The plugin *)
From NFPOP Require Import Loader.

(* CompCert libs *)
From NFPOP Require Import Coqlib.
From NFPOP Require Import Errors.
From NFPOP Require Import Memory.
From NFPOP Require Import Smallstep.
From NFPOP Require Import Maps.
From NFPOP Require Import AST.
From NFPOP Require Import Globalenvs.
From NFPOP Require Import Events.
From NFPOP Require Import Memory.
From NFPOP Require Import Integers.
From NFPOP Require Import Values.
Local Open Scope error_monad_scope.

Axiom cheat : forall {X}, X.

Family Compiler.

FInductive constant : Set :=
| Ointconst: int -> constant. (* integer constant *)

FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
Case Ointconst := (fun n => Some (Vint n)). 
FEnd eval_constant.
     
FInductive unary_operation : Set :=
| Onotint: unary_operation. (* bitwise complement *)

FRecursion eval_unop about
  unary_operation motive
  (fun (_ : unary_operation) => val -> option val) by _rect.  
Case Onotint := (fun arg => Some (Val.notint arg)). 
FEnd eval_unop.

FInductive binary_operation : Set :=
| Oadd: binary_operation (* integer addition *)
| Osub: binary_operation (* integer subtraction *)
| Omul: binary_operation. (* integer multiplication *)    

FRecursion eval_binop about
    binary_operation motive
    (fun (_ : binary_operation) => val -> val -> option val) by _rect.
Case Oadd := (fun arg1 arg2 => Some (Val.add arg1 arg2)).
Case Osub := (fun arg1 arg2 => Some (Val.sub arg1 arg2)).
Case Omul := (fun arg1 arg2 => Some (Val.mul arg1 arg2)).  
FEnd eval_binop.

Family I.
MetaData incr_or_decr.
Inductive incr_or_decr : Set := Incr | Decr.
FEnd incr_or_decr.
FEnd I.

Family HIR.

FInductive expr : Set :=
| Evar : ident -> expr 
| Econst : constant -> expr 
| Eunop : unary_operation -> expr -> expr
| Ebinop : binary_operation -> expr -> expr -> expr
| Eparen : expr -> expr (* marked expression *)                                                   
(* Side effects *)
| Eseqand : expr -> expr -> expr (* sequential "and" r1 && r2 *)
| Eseqor : expr -> expr -> expr (* sequential "or" r1 || r2 *)
| Econdition : expr -> expr -> expr -> expr    
| Eassign : ident -> expr -> expr (* assignment l = r *)
| Eassignop : binary_operation -> ident -> expr -> expr
| Epostincr : I.incr_or_decr -> ident -> expr
| Epreincr : I.incr_or_decr -> ident -> expr.
                                                   
FInductive stmt : Set :=
| Sskip: stmt
| Sset : ident -> expr -> stmt            
| Sseq: stmt -> stmt -> stmt.  

FDefinition function := stmt.
FDefinition fundef := AST.fundef function.  
FDefinition program : Type := AST.program fundef unit.

FDefinition env := PTree.t val.
FDefinition genv := Genv.t fundef unit.

FDefinition bool_val : val -> option bool := 
  fun v => 
    match v with 
    | Vint n => Some (negb (Int.eq n Int.zero))    
    | _ => None
    end.

FInductive eval_expr : env ->  expr -> val -> Prop :=
| eval_Evar: forall e id v,
    PTree.get id e = Some v ->
    eval_expr e (Evar id) v       
| eval_Econst: forall e cst v,
    eval_constant cst = Some v ->
    eval_expr e (Econst cst) v
| eval_Eunop: forall e op a1 v1 v,
    eval_expr e a1 v1 ->
    eval_unop op v1 = Some v ->
    eval_expr e (Eunop op a1) v
| eval_Ebinop: forall e op a1 a2 v1 v2 v,
    eval_expr e a1 v1 ->
    eval_expr e a2 v2 ->
    eval_binop op v1 v2 = Some v ->
    eval_expr e (Ebinop op a1 a2) v
| eval_Eseqand_false_0: forall e a1 a2 v1, 
   eval_expr e a1 v1 -> 
   bool_val v1 = Some false -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.zero)
| eval_Eseqand_false_1: forall e a1 a2 v2, 
   eval_expr e a2 v2 -> 
   bool_val v2 = Some false -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.zero)
| eval_Eseqand_true: forall e a1 a2 v1 v2, 
   eval_expr e a1 v1 -> 
   eval_expr e a2 v2 -> 
   bool_val v1 = Some true -> 
   bool_val v2 = Some true -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.one)
| eval_Eseqor_false: forall e a1 a2 v1 v2, 
   eval_expr e a1 v1 -> 
   eval_expr e a2 v2 -> 
   bool_val v1 = Some false -> 
   bool_val v2 = Some false -> 
   eval_expr e (Eseqor a1 a2) (Vint Int.zero)
| eval_Eseqor_true_0: forall e a1 a2 v1, 
   eval_expr e a2 v1 -> 
   bool_val v1 = Some true -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.one)
| eval_Eseqor_true_1: forall e a1 a2 v2, 
   eval_expr e a1 v2 -> 
   bool_val v2 = Some true -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.one)
| eval_Econdition: forall e a b a1 a2 v1 v,
    eval_expr e a v1 ->
    bool_val v1 = Some b ->      
    eval_expr e (Eparen (if b then a1 else a2)) v ->
    eval_expr e (Econdition a a1 a2) v
(* These should update memory, not the temporary env. 
   In fact, these rules are wrong *)
| eval_Eassign: forall e a v id,      
    eval_expr e a v ->
    eval_expr (PTree.set id v e) (Eassign id a) v
| eval_Eassignop: forall id e op a2 v1 v2 v,
    PTree.get id e = Some v1 ->
    eval_expr e a2 v2 ->
    eval_binop op v1 v2 = Some v ->
    eval_expr (PTree.set id v e) (Eassignop op id a2) v
| eval_Epostincr_incr: forall id e v,      
    PTree.get id e = Some v ->
    eval_expr 
      (PTree.set id (Val.add v (Vint Int.one)) e)
      (Epostincr I.Incr id) v
| eval_Epostincr_decr: forall id e v,      
    PTree.get id e = Some v ->
    eval_expr 
      (PTree.set id (Val.sub v (Vint Int.one)) e)
      (Epostincr I.Decr id) v
| eval_Epreincr_incr: forall id e v v',      
    PTree.get id e = Some v ->
    v' = Val.add v (Vint Int.one) -> 
    eval_expr 
      (PTree.set id v' e)
      (Epostincr I.Incr id) v'
| eval_Epreincr_decr: forall id e v v', 
    PTree.get id e = Some v ->
    v' = Val.sub v (Vint Int.one) -> 
    eval_expr 
      (PTree.set id v' e)
      (Epostincr I.Decr id) v'.

FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.

FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq := (fun s c call_cont_c => call_cont_c).  
FEnd call_cont.
               
FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
Case Kstop := True.                   
Case Kseq := (fun s c call_cont_c => False).  
FEnd is_call_cont.

MetaData state.
Inductive state: Type :=
| State:(* Execution within a function *)
    forall (f: self__HIR.function)(* currently executing function *)
           (s: self__HIR.stmt)(* statement under consideration *)
           (k: self__HIR.cont)(* its continuation -- what to do next *)
           (e: self__HIR.env)(* current local environment *)               
           (m: mem),(* current memory state *)
      state
| Returnstate:(* Return from a function *)
    forall (v: val)(* Return value *)
           (k: self__HIR.cont)(* what to do next *)
           (m: mem),(* memory state *)
    state.            
FEnd state.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e m,
   step ge (self__HIR.State f Sskip (Kseq s k) e m)
     E0 (self__HIR.State f s k e m)
| step_set: forall ge f id a k e m v,
   eval_expr e a v ->
   step ge (self__HIR.State f (Sset id a) k e m)
     E0 (self__HIR.State f Sskip k (PTree.set id v e) m)
| step_seq: forall ge f s1 s2 k e m,
   step ge (self__HIR.State f (Sseq s1 s2) k e m)
     E0 (self__HIR.State f s1 (Kseq s2 k) e m).

MetaData initial_state.
Inductive initial_state : self__HIR.state -> Prop :=
| initial_state_intro: forall f s e m0,        
   initial_state (self__HIR.State f s self__HIR.Kstop e m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__HIR.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__HIR.Returnstate (Vint r) self__HIR.Kstop m) r.
FEnd final_state.

FEnd HIR.

Family MIR.

FInductive expr : Set :=
| Evar : ident -> expr 
| Econst : constant -> expr 
| Eunop : unary_operation -> expr -> expr
| Ebinop : binary_operation -> expr -> expr -> expr.  
                                                   
FInductive stmt : Set :=
| Sskip: stmt
| Sset : ident -> expr -> stmt            
| Sseq: stmt -> stmt -> stmt.  

FDefinition function := stmt.
FDefinition fundef := AST.fundef function.  
FDefinition program : Type := AST.program fundef unit.

FDefinition env := PTree.t val.
FDefinition genv := Genv.t fundef unit.

FDefinition bool_val : val -> option bool := 
  fun v => 
    match v with 
    | Vint n => Some (negb (Int.eq n Int.zero))    
    | _ => None
    end.

FInductive eval_expr : env ->  expr -> val -> Prop :=
| eval_Evar: forall e id v,
    PTree.get id e = Some v ->
    eval_expr e (Evar id) v       
| eval_Econst: forall e cst v,
    eval_constant cst = Some v ->
    eval_expr e (Econst cst) v
| eval_Eunop: forall e op a1 v1 v,
    eval_expr e a1 v1 ->
    eval_unop op v1 = Some v ->
    eval_expr e (Eunop op a1) v
| eval_Ebinop: forall e op a1 a2 v1 v2 v,
    eval_expr e a1 v1 ->
    eval_expr e a2 v2 ->
    eval_binop op v1 v2 = Some v ->
    eval_expr e (Ebinop op a1 a2) v.

FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.

FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq := (fun s c call_cont_c => call_cont_c).  
FEnd call_cont.
               
FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
Case Kstop := True.                   
Case Kseq := (fun s c call_cont_c => False).  
FEnd is_call_cont.

MetaData state.
Inductive state: Type :=
| State:(* Execution within a function *)
    forall (f: self__MIR.function)(* currently executing function *)
           (s: self__MIR.stmt)(* statement under consideration *)
           (k: self__MIR.cont)(* its continuation -- what to do next *)
           (e: self__MIR.env)(* current local environment *)               
           (m: mem),(* current memory state *)
      state
| Returnstate:(* Return from a function *)
    forall (v: val)(* Return value *)
           (k: self__MIR.cont)(* what to do next *)
           (m: mem),(* memory state *)
    state.            
FEnd state.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e m,
   step ge (self__MIR.State f Sskip (Kseq s k) e m)
     E0 (self__MIR.State f s k e m)
| step_set: forall ge f id a k e m v,
   eval_expr e a v ->
   step ge (self__MIR.State f (Sset id a) k e m)
     E0 (self__MIR.State f Sskip k (PTree.set id v e) m)
| step_seq: forall ge f s1 s2 k e m,
   step ge (self__MIR.State f (Sseq s1 s2) k e m)
     E0 (self__MIR.State f s1 (Kseq s2 k) e m).

MetaData initial_state.
Inductive initial_state : self__MIR.state -> Prop :=
| initial_state_intro: forall f s e m0,        
   initial_state (self__MIR.State f s self__MIR.Kstop e m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__MIR.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__MIR.Returnstate (Vint r) self__MIR.Kstop m) r.
FEnd final_state.

FEnd MIR.

Family HIR_to_MIR.

Family S extends HIR. FEnd S.
Family T extends MIR. FEnd T.

FRecursion lower_expr about S.expr motive 
   (fun (_ : S.expr) => res (T.stmt * T.expr)) by _rect.
Case Evar := cheat.
Case Econst := cheat.
Case Eunop := cheat.
Case Ebinop := cheat.
Case Eparen := cheat.
Case Eseqand := cheat.
Case Eseqor := cheat.
Case Econdition := cheat.
Case Eassign := cheat.
Case Eassignop := cheat.
Case Epostincr := cheat.
Case Epreincr := cheat.
FEnd lower_expr.                          

FRecursion lower_stmt about S.stmt motive 
  (fun (s : S.stmt) => res T.stmt) by _rect.
Case Sskip := cheat.
Case Sset := cheat.
Case Sseq := cheat.
FEnd lower_stmt.

FDefinition transl_function : S.function -> res T.function := cheat.

FDefinition transl_program : S.program -> res T.program := cheat.

MetaData match_env.
Record match_env (e: self__HIR_to_MIR.S.env) (te: self__HIR_to_MIR.T.env) : Prop :=
mk_match_env {
  me_local:
    forall id v,
    e!id = Some v -> te!id = Some v;
  me_local_inv:
    forall id v,
    te!id = Some v -> exists x, e!id = Some x
}.
FEnd match_env.
  
(* matching continuations *)
FInductive match_cont: S.cont -> T.cont -> Prop :=
| match_Kstop:
    match_cont S.Kstop T.Kstop
| match_Kseq: forall s k ts tk,
    lower_stmt s = OK ts ->
    match_cont k tk ->
    match_cont (S.Kseq s k) (T.Kseq ts tk).     
  
(* matching program states *)
MetaData match_states.
Inductive match_states: self__HIR_to_MIR.S.state -> self__HIR_to_MIR.T.state -> Prop :=
| match_state:
   forall f s k e m tf ts tk te ts' tk'
       (TRF: self__HIR_to_MIR.transl_function f = OK tf)
       (TR: self__HIR_to_MIR.lower_stmt s = OK ts)          
       (MENV: self__HIR_to_MIR.match_env e te)
       (MK: self__HIR_to_MIR.match_cont k tk),
   match_states (self__HIR_to_MIR.S.State f s k e m)
                   (self__HIR_to_MIR.T.State tf ts' tk' te m)
| match_returnstate:
    forall res k m tk
        (MK: self__HIR_to_MIR.match_cont k tk),          
    match_states (self__HIR_to_MIR.S.Returnstate res k m)
                 (self__HIR_to_MIR.T.Returnstate res tk m).
FEnd match_states.
  
FOpaque Definition measure : S.state -> nat := fun _ => 0%nat.
  
FInduction transl_expr_correct about S.eval_expr motive 
   (fun  e a v (_ : S.eval_expr e a v) =>        
      forall ta (TR: (do (_stmt, x) <- (lower_expr a); OK x) = OK ta),          
           T.eval_expr e ta v).
FProof.
(* Evar *)
+ intros. apply cheat.
(* Econst *)
+  intros. apply cheat.
(* Eunop *)
+ intros. apply cheat.
(* Ebinop *)
+ intros. apply cheat.
(* Eseqand*)
+ apply cheat.
(* Eseqor*)
+ apply cheat.
(* Econdition*)
+ apply cheat.
(* Eassign*)
+ apply cheat.
(* Eassignop*)
+ apply cheat.
(* Epostincr*)
+ apply cheat.
(* Epreincr*)
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat
+ apply cheat.
+ apply cheat.
Qed. FEnd transl_expr_correct.
  
FInduction transl_stmt_correct about S.step motive
   (fun ge S1 t S2 (_ : S.step ge S1 t S2) => 
   forall prog tprog tge, (* match_prog prog tprog -> *)
      Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->               
     forall T1, match_states S1 T1 -> 
     (exists T2, plus T.step tge T1 t T2 /\ match_states S2 T2) \/
     (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat).
FProof.
(* Skip *)
+ apply cheat.  
(* Set *)
+ apply cheat.
(* Seq *)
+ apply cheat.
Qed. FEnd transl_stmt_correct.

FLemma transl_initial_states:
   forall St prog tprog, S.initial_state St ->
   transl_program prog = OK tprog ->
   exists R, T.initial_state R /\ match_states St R.
FProofLemma. intros. inv H. apply cheat.
Qed. CloseFLemma.
        
FLemma transl_final_states:
  forall St R r,
  match_states St R -> S.final_state St r -> T.final_state R r.
FProofLemma. intros. inv H0. inv H. apply cheat.
Qed. CloseFLemma.  
  
FEnd HIR_to_MIR.

FEnd Compiler.

Family Compiler_loops extends Compiler.


Trait HIR_while extends HIR.
FInductive stmt : Set := 
| Swhile : expr -> stmt -> stmt. (* while loop *)

FInductive cont: Type :=
| Kwhile1: expr -> stmt -> cont -> cont (* Kwhile1 x s k = after x in while(x) s *)
| Kwhile2: expr -> stmt -> cont -> cont. (* Kwhile x s k = after s in while (x) s *)

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_while.
FEnd HIR_while.

Trait HIR_for extends HIR.
FInductive stmt : Set := 
| Sfor: statement -> expr -> statement -> statement -> statement(* for loop *)

FInductive cont: Type :=
| Kfor2: expr -> statement -> statement -> cont -> cont(* Kfor2 e2 e3 s k = after e2 in for(e1;e2;e3) s *)
| Kfor3: expr -> statement -> statement -> cont -> cont(* Kfor3 e2 e3 s k = after s in for(e1;e2;e3) s *)
| Kfor4: expr -> statement -> statement -> cont -> cont(* Kfor4 e2 e3 s k = after e3 in for(e1;e2;e3) s *)

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_for 
FEnd HIR_for.

Trait HIR_do_while extends HIR.
FInductive stmt : Set := 
| Sdowhile : expr -> statement -> statement(* do loop *)

FInductive cont: Type :=
| Kdowhile1: expr -> statement -> cont -> cont(* Kdowhile1 x s k = after s in do s while (x) *)
| Kdowhile2: expr -> statement -> cont -> cont(* Kdowhile2 x s k = after x in do s while (x) *)

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_do_while
FEnd HIR_do_while.

(* 
Trait HIR_loop_base extends HIR.
FInductive stmt : Set :=
| Sbreak : stmt
| Scontinue : stmt.

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_continue_seq: forall f s k e m,
      step (State f Scontinue (Kseq s k) e m)
         E0 (State f Scontinue k e m)
| step_break_seq: forall f s k e m,
    sstep (State f Sbreak (Kseq s k) e m)
       E0 (State f Sbreak k e m)
FEnd HIR.
*)

Family MIR. 
FInductive stmt : Set :=
| Sloop : stmt -> stmt -> stmt.

FInductive cont : Set :=
| Kwhile1 : expr -> stmt -> cont
| Kwhile2 : expr -> stmt -> cont.

FInductive step : genv -> state -> trace -> state -> Prop := 
  | step_loop
FEnd MIR.

Trair HIR_while_to_MIR extends HIR_to_MIR.
Family S extends HIR_while. End S. 
Family T extends MIR. End T. 

FRecursion lower_stmt.
Case Swhile := cheat.
End lower_stmt.

FInduction lower_stmt_correct.
+ apply cheat.
End lower_stmt_correct.
End HIR_while_to_MIR.

Family HIR_for_to_MIR.
Family S extends HIR_for. End S. 
Family T extends MIR. End T. 

FRecursion lower_stmt.
Case Sfor := cheat.
End lower_stmt.

FInduction lower_stmt_correct.
+ apply cheat.
End lower_stmt_correct.
End HIR_while_to_MIR.

Trait HIR_while_to_MIR extends HIR_to_MIR.
Family S extends HIR_for. End S. 
Family T extends MIR. End T. 

FRecursion lower_stmt.
Case Swhile := cheat.
End lower_stmt.

FInduction lower_stmt_correct.
+ apply cheat.
End lower_stmt_correct.
End HIR_while_to_MIR.

Trait HIR_do_while_to_MIR extends HIR_to_MIR.
Family S extends HIR_do_while. End S. 
Family T extends MIR. End T. 

FRecursion lower_stmt.
Case Sdowhile := cheat.
End lower_stmt.

FInduction lower_stmt_correct.
+ apply cheat.
End lower_stmt_correct.
End HIR_while_to_MIR.

Family HIR. 
FInductive stmt : Set :=
| Sbreak : stmt
| Scontinue : stmt.

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_continue_seq: forall f s k e m,
      sstep (State f Scontinue (Kseq s k) e m)
         E0 (State f Scontinue k e m)
| step_break_seq: forall f s k e m,
    sstep (State f Sbreak (Kseq s k) e m)
       E0 (State f Sbreak k e m)
FEnd HIR.

Family HIR_to_MIR extends HIR_while_to_MIR, HIR_for_to_MIR, HIR_do_while_to_MIR. 
FEnd HIR_to_MIR.
   
FEnd Compiler_loops.
