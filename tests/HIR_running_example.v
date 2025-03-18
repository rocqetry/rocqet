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

FInductive constant : Type :=
| Ointconst: int -> constant. (* integer constant *)

FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
Case Ointconst := (fun n => Some (Vint n)). 
FEnd eval_constant.
     
FInductive unary_operation : Type :=
| Onotint: unary_operation. (* bitwise complement *)

FRecursion eval_unop about
  unary_operation motive
  (fun (_ : unary_operation) => val -> option val) by _rect.  
Case Onotint := (fun arg => Some (Val.notint arg)). 
FEnd eval_unop.

FInductive binary_operation : Type :=
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

Inductive incr_or_decr : Type := Incr | Decr.

Family HIR_common.  

FInductive expr : Set :=
| Evar : ident -> expr 
| Econst : constant -> expr 
| Eunop : unary_operation -> expr -> expr
| Ebinop : binary_operation -> expr -> expr -> expr
| Eparen : expr -> expr (* marked expression *)                                                   
(* Side effects *)
| Eseqand : expr -> expr -> expr. (* sequential "and" r1 && r2 *)
| Eseqor : expr -> expr -> expr. (* sequential "or" r1 || r2 *)
| Econdition : expr -> expr -> expr -> expr.    
| Eassign : ident -> expr -> expr. (* assignment l = r *)
| Eassignop : binary_operation -> ident -> expr -> expr. 
| Epostincr : incr_or_decr -> ident -> expr.
| Epreincr : incr_or_decr -> ident -> expr.
                                                   
FInductive stmt : Set :=
| Sskip: stmt
| Sset : ident -> expr -> stmt            
| Sseq: stmt -> stmt -> stmt.  

FDefinition function := stmt.
FDefinition fundef := AST.fundef function.  
FDefinition program : Type := AST.program fundef unit.

FDefinition env := PTree.t (block * Z).
FDefinition genv := Genv.t fundef unit.

FDefinition bool_val : val -> Some bool := 
  fun v => 
    match v with 
    | Vint 0 => Some false 
    | Vint _ => Some true 
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
   bool_val v2 = Some true -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.one)
| eval_Eseqor_true_1: forall e a1 a2 v2, 
   eval_expr e a1 v2 -> 
   bool_val v1 = Some true -> 
   eval_expr e (Eseqand a1 a2) (Vint Int.one)
| eval_Econdition: forall e a1 a2 a3 v1 v,
    eval_expr e a v1 ->
    bool_val v1 = Some b ->      
    eval_expr (Econdition a a1 a2) (Eparen (if b then a1 else a2))  
| eval_Eassign: forall e a v,      
    eval_expr e a v ->
    eval_expr (PTree.set id v e) (Eassign id a2) v  
| eval_Eassignop: forall e op a1 a2 v1 v2 v,
    PTree.get id e = Some v1 ->
    eval_expr e a2 v2 ->
    eval_binop op v1 v2 = Some v ->
    eval_expr (PTree.set id v e) (Eassignop op id a2) v
| eval_Epostincr_incr: forall e op a v1 v,      
    PTree.get id e = Some v ->
    eval_expr 
      (PTree.set id Val.add v (Vint Int.one) e)
      (Epostincr Incr id) v
| eval_Epostincr_decr: forall e a v1 v,      
    PTree.get id e = Some v ->
    eval_expr 
      (PTree.set id Val.sub v (Vint Int.one) e)
      (Epostincr Decr id) v
| eval_Epreincr_incr: forall e op a v1 v,      
    PTree.get id e = Some v ->
    v' = Val.add v (Vint Int.one) -> 
    eval_expr 
      (PTree.set id v' e)
      (Epostincr Incr id) v'
| eval_Epreincr_decr: forall e a v1 v,      
    PTree.get id e = Some v ->
    v' = Val.sub v (Vint Int.one) -> 
    eval_expr 
      (PTree.set id v' e)
      (Epostincr Decr id) v'.                

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

Inductive state: Type :=
| State:(* Execution within a function *)
    forall (f: self__Base.function)(* currently executing function *)
           (s: self__Base.stmt)(* statement under consideration *)
           (k: self__Base.cont)(* its continuation -- what to do next *)
           (e: self__Base.env)(* current local environment *)               
           (m: mem),(* current memory state *)
      state
| Returnstate:(* Return from a function *)
    forall (v: val)(* Return value *)
           (k: self__Base.cont)(* what to do next *)
           (m: mem),(* memory state *)
    state.            

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
   step ge (self__Base.State f Sskip (Kseq s k) e le m)
     E0 (self__Base.State f s k e le m)
| step_set: forall ge f id a k e le m v,
   eval_expr e le a v ->
   step ge (self__Base.State f (Sset id a) k e le m)
     E0 (self__Base.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
   step ge (self__Base.State f (Sseq s1 s2) k e le m)
     E0 (self__Base.State f s1 (Kseq s2 k) e le m).

MetaData initial_state.
Inductive initial_state : self__Base.state -> Prop :=
| initial_state_intro: forall f s m0,        
   initial_state (State f s self__Base.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Base.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__Base.Returnstate (Vint r) self__Base.Kstop m) r.
FEnd final_state.

FEnd HIR_common.

Family MIR_common.

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

FDefinition env := PTree.t (block * Z).
FDefinition genv := Genv.t fundef unit.

FDefinition bool_val : val -> Some bool := 
fun v => 
  match v with 
  | Vint 0 => Some false 
  | Vint _ => Some true 
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

Inductive state: Type :=
| State:(* Execution within a function *)
    forall (f: self__Base.function)(* currently executing function *)
           (s: self__Base.stmt)(* statement under consideration *)
           (k: self__Base.cont)(* its continuation -- what to do next *)
           (e: self__Base.env)(* current local environment *)               
           (m: mem),(* current memory state *)
      state
| Returnstate:(* Return from a function *)
    forall (v: val)(* Return value *)
           (k: self__Base.cont)(* what to do next *)
           (m: mem),(* memory state *)
    state.            

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
   step ge (self__Base.State f Sskip (Kseq s k) e le m)
     E0 (self__Base.State f s k e le m)
| step_set: forall ge f id a k e le m v,
   eval_expr e le a v ->
   step ge (self__Base.State f (Sset id a) k e le m)
     E0 (self__Base.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
   step ge (self__Base.State f (Sseq s1 s2) k e le m)
     E0 (self__Base.State f s1 (Kseq s2 k) e le m).

MetaData initial_state.
Inductive initial_state : self__Base.state -> Prop :=
| initial_state_intro: forall f s m0,        
   initial_state (State f s self__Base.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Base.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__Base.Returnstate (Vint r) self__Base.Kstop m) r.
FEnd final_state.

FEnd MIR_common.

Family HIR extends HIR_common. FEnd HIR.
Family MIR extends MIR_common. FEnd MIR.

Family HIR_to_MIR.

Family S extends HIR. FEnd S.
Family T extends MIR. FEnd T.

FRecursion lower_expr about S.expr motive 
   (fun (_ : S.expr) => res (T.stmt * T.expr)).
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

FRecursion lower_stmt about S.expr motive 
  (fun (s : S.stmt) => res T.stmt).
Case Sskip := cheat.
Case Sset := cheat.
Case Sseq := cheat.
FEnd lower_stmt.

Record match_env (e: self__Basetransl.Source.env) (te: self__Basetransl.Target.env) : Prop :=
mk_match_env {
  me_local:
    forall id b sz,
    e!id = Some (b, sz) -> te!id = Some(b, sz);
  me_local_inv:
    forall id b sz,
    te!id = Some (b, sz) -> exists x, e!id = Some(b, x)
}.
  
(* matching continuations *)
FInductive match_cont: Source.cont -> Target.cont -> Prop :=
| match_Kstop:
    match_cont Source.Kstop Target.Kstop
| match_Kseq: forall s k ts tk,
    transl_stmt s = OK ts ->
    match_cont k tk ->
    match_cont (Source.Kseq s k) (Target.Kseq ts tk).     
  
(* matching program states *)
MetaData match_states.
Inductive match_states: self__Basetransl.Source.state -> self__Basetransl.Target.state -> Prop :=
| match_state:
   forall f s k e le m tf ts tk te ts' tk'
       (TRF: self__Basetransl.transl_function f = OK tf)
       (TR: self__Basetransl.transl_stmt s = OK ts)          
       (MENV: self__Basetransl.match_env e te)
       (MK: self__Basetransl.match_cont k tk),
   match_states (self__Basetransl.Source.State f s k e le m)
                   (self__Basetransl.Target.State tf ts' tk' te le m)  
| match_returnstate:
    forall res k m tk
        (MK: self__Basetransl.match_cont k tk),          
    match_states (self__Basetransl.Source.Returnstate res k m)
                 (self__Basetransl.Target.Returnstate res tk m).
FEnd match_states.
  
FOpaque Definition measure : Source.state -> nat := fun _ => 0%nat.
  
FInduction transl_expr_correct about Source.eval_expr motive 
   (fun  e le a v (_ : Source.eval_expr e le a v) =>        
      forall ta te (MENV: match_env e te) (TR: transl_expr a = OK ta),          
           Target.eval_expr te le ta v).
FProof.
(* Evar *)
+ intros. fsimpl in TR. monadInv TR. fconstructor. 
(* Econst *)
+  intros. fsimpl in TR. monadInv TR. fconstructor.
(* Eunop *)
+ intros. fsimpl in TR.  monadInv TR. fconstructor.
(* Ebinop *)
+ intros. fsimpl in TR.  monadInv TR. fconstructor.
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
Qed. FEnd transl_expr_correct.
  
FInduction transl_stmt_correct about Source.step motive
   (fun ge S1 t S2 (_ : Source.step ge S1 t S2) => 
   forall prog tprog tge, (* match_prog prog tprog -> *)
      Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->               
     forall T1, match_states S1 T1 -> 
     (exists T2, plus Target.step tge T1 t T2 /\ match_states S2 T2) \/
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
   forall S prog tprog, Source.initial_state prog S ->
   transl_program prog = OK tprog ->
   exists R, Target.initial_state tprog R /\ match_states S R.
FProofLemma. intros. inv H. apply cheat.
Qed. CloseFLemma.
        
FLemma transl_final_states:
  forall S R r,
  match_states S R -> Source.final_state S r -> Target.final_state R r.
FProofLemma. intros. inv H0. inv H. apply cheat.
Qed. CloseFLemma.  
  
FEnd HIR_common_to_MIR_common.

FEnd Compiler.

Family Compiler_loops extends Compiler.

Family HIR_common.
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
FEnd HIR_common.

Family MIR_common. 
FInductive stmt : Set :=
| Sloop : stmt -> stmt -> stmt.

FInductive cont : Set :=
| Kwhile1 : expr -> stmt -> cont
| Kwhile2 : expr -> stmt -> cont.

FInductive step : genv -> state -> trace -> state -> Prop := 
  | step_loop
FEnd MIR_common.


Family HIR_while extends HIR_common.
FInductive stmt : Set := 
| Swhile : expr -> statement -> statement(* while loop *)

FInductive cont: Type :=
| Kwhile1: expr -> statement -> cont -> cont(* Kwhile1 x s k = after x in while(x) s *)
| Kwhile2: expr -> statement -> cont -> cont(* Kwhile x s k = after s in while (x) s *)

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_while 
FEnd HIR_while.

Family HIR_for extends HIR_common.
FInductive stmt : Set := 
| Sfor: statement -> expr -> statement -> statement -> statement(* for loop *)

FInductive cont: Type :=
| Kfor2: expr -> statement -> statement -> cont -> cont(* Kfor2 e2 e3 s k = after e2 in for(e1;e2;e3) s *)
| Kfor3: expr -> statement -> statement -> cont -> cont(* Kfor3 e2 e3 s k = after s in for(e1;e2;e3) s *)
| Kfor4: expr -> statement -> statement -> cont -> cont(* Kfor4 e2 e3 s k = after e3 in for(e1;e2;e3) s *)

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_for 
FEnd HIR_for.

Family HIR_do_while extends HIR_common.
FInductive stmt : Set := 
| Sdowhile : expr -> statement -> statement(* do loop *)

FInductive cont: Type :=
| Kdowhile1: expr -> statement -> cont -> cont(* Kdowhile1 x s k = after s in do s while (x) *)
| Kdowhile2: expr -> statement -> cont -> cont(* Kdowhile2 x s k = after x in do s while (x) *)

FInductive step : genv -> state -> trace -> state -> Prop := 
| step_do_while
FEnd HIR_do_while.

Family HIR extends HIR_common, HIR_while, HIR_for, HIR_do_while.
End HIR.

Family HIR_while_to_MIR.
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

Family HIR_while_to_MIR.
Family S extends HIR_for. End S. 
Family T extends MIR. End T. 

FRecursion lower_stmt.
Case Swhile := cheat.
End lower_stmt.

FInduction lower_stmt_correct.
+ apply cheat.
End lower_stmt_correct.
End HIR_while_to_MIR.

Family HIR_do_while_to_MIR.
Family S extends HIR_do_while. End S. 
Family T extends MIR. End T. 

FRecursion lower_stmt.
Case Sdowhile := cheat.
End lower_stmt.

FInduction lower_stmt_correct.
+ apply cheat.
End lower_stmt_correct.
End HIR_while_to_MIR.

Family HIR_to_MIR extends HIR_while_to_MIR, HIR_for_to_MIR, HIR_do_while_to_MIR. 
FEnd HIR_to_MIR.
   
FEnd Compiler_loops.
