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

Family BaseExt.  
  (* We use the val from the CompCert lib *)
  (* FInductive val: Type :=
     | Vundef: val
     | Vint: int -> val. *)
  
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
    (* | Odiv: binary_operation. (* integer signed division *)*)

  FRecursion eval_binop about
    binary_operation motive
    (fun (_ : binary_operation) => val -> val -> option val) by _rect.  
  Case Oadd := (fun arg1 arg2 => Some (Val.add arg1 arg2)).
  Case Osub := (fun arg1 arg2 => Some (Val.sub arg1 arg2)).
  Case Omul := (fun arg1 arg2 => Some (Val.mul arg1 arg2)).
  (* Case Odiv := (fun arg1 arg2 => Val.divs arg1 arg2).*)
  FEnd eval_binop.

  Family Base.    
  FInductive expr : Type :=
    | Evar : ident -> expr (* reading a temporary variable *)            
    | Econst : constant -> expr (* constants *)          
    | Eunop : unary_operation -> expr -> expr(* unary operation *)
    | Ebinop : binary_operation -> expr -> expr -> expr.

  FInductive stmt : Type :=
    | Sskip: stmt
    | Sset : ident -> expr -> stmt            
    | Sseq: stmt -> stmt -> stmt.

  MetaData function.
  Record function : Type := mkfunction {    
    fn_params: list ident;    
    fn_body: self__Base.stmt
  }.
  FEnd function.
  
  FDefinition fundef := AST.fundef function.  
  FDefinition program : Type := AST.program fundef unit.

  (* semantics *) 
  FDefinition env := PTree.t (block * Z).
  FDefinition temp_env := PTree.t val.
  FDefinition genv := Genv.t fundef unit.

  FInductive eval_expr : env -> temp_env -> expr -> val -> Prop :=
    | eval_Evar: forall e le id v,
        PTree.get id le = Some v ->
        eval_expr e le (Evar id) v               
    | eval_Econst: forall e le cst v,
        eval_constant cst = Some v ->
        eval_expr e le (Econst cst) v
    | eval_Eunop: forall e le op a1 v1 v,
        eval_expr e le a1 v1 ->
        eval_unop op v1 = Some v ->
        eval_expr e le (Eunop op a1) v
    | eval_Ebinop: forall e le op a1 a2 v1 v2 v,
        eval_expr e le a1 v1 ->
        eval_expr e le a2 v2 ->
        eval_binop op v1 v2 = Some v ->
        eval_expr e le (Ebinop op a1 a2) v.

  (* continuation-based semantics *)
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
        forall (f: self__Base.function)(* currently executing function *)
               (s: self__Base.stmt)(* statement under consideration *)
               (k: self__Base.cont)(* its continuation -- what to do next *)
               (e: self__Base.env)(* current local environment *)
               (le: self__Base.temp_env)(* current temporary environment *)
               (m: mem),(* current memory state *)
        state
    | Callstate:(* Invocation of a function *)
        forall (f: self__Base.fundef)(* function to invoke *)
               (args: list val)(* arguments provided by caller *)
               (k: self__Base.cont)(* what to do next *)
               (m: mem),(* memory state *)
        state
    | Returnstate:(* Return from a function *)
        forall (v: val)(* Return value *)
               (k: self__Base.cont)(* what to do next *)
               (m: mem),(* memory state *)
        state.
  FEnd state.
  
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
  Inductive initial_state (p: self__Base.program): self__Base.state -> Prop :=
    | initial_state_intro: forall b f m0,
        let ge := Genv.globalenv p in
        Genv.init_mem p = Some m0 ->
        Genv.find_symbol ge p.(prog_main) = Some b ->
        Genv.find_funct_ptr ge b = Some f ->
        (*funsig f = signature_main ->*)
        initial_state p (self__Base.Callstate f nil self__Base.Kstop m0).
  FEnd initial_state.

  MetaData final_state.
  Inductive final_state: self__Base.state -> int -> Prop :=
    | final_state_intro: forall r m,
        final_state (self__Base.Returnstate (Vint r) self__Base.Kstop m) r.
  FEnd final_state.
  FEnd Base.

  Family Basetransl.  
  Family Source extends Base.
  FEnd Source.  

  Family Target extends Base. 
  FEnd Target.

  FRecursion transl_expr about Source.expr motive (fun (_ : Source.expr) => res Target.expr) by _rect.
  Case Evar := (fun id => OK (Target.Evar id)).
  Case Econst := (fun c => OK (Target.Econst c)).
  Case Eunop := (fun op e transl_expr_e =>
                   do te <- transl_expr_e;
                   OK (Target.Eunop op te)).
  Case Ebinop := (fun op e0 transl_expr_e0 e1 transl_expr_e1 =>
     do te0 <- transl_expr_e0;              
     do te1 <- transl_expr_e1;              
     OK (Target.Ebinop op te0 te1)).
  FEnd transl_expr.
  
  FRecursion transl_stmt about Source.stmt motive (fun (_ : Source.stmt) => res Target.stmt) by _rect.
  Case Sskip := (OK (Target.Sskip)).
  Case Sset := (fun id e =>
    do te <- transl_expr e;
    OK (Target.Sset id te)).
  Case Sseq := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 =>                        
    do ts1 <- transl_stmt_s1; 
    do ts2 <- transl_stmt_s2; 
    OK (Target.Sseq ts1 ts2)).
  FEnd transl_stmt.

  FDefinition transl_function : Source.function -> res Target.function := fun f => 
     do tbody <- transl_stmt f.(self__Basetransl.Source.fn_body);
     OK (Target.mkfunction            
            (Source.fn_params f)                        
            tbody).
  
  FDefinition transl_fundef : Source.fundef -> res Target.fundef := fun f =>
    transf_partial_fundef transl_function f.  

  FDefinition transl_program : Source.program -> res Target.program := fun p =>
    transform_partial_program transl_fundef p.
  
  (* matching translated envs *)
  MetaData match_env.
  Record match_env (e: self__Basetransl.Source.env) (te: self__Basetransl.Target.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b sz,
      e!id = Some (b, sz) -> te!id = Some(b, sz);
    me_local_inv:
      forall id b sz,
      te!id = Some (b, sz) -> exists x, e!id = Some(b, x)
  }.
  FEnd match_env.
  
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
  | match_callstate:
      forall fd args k m tfd tk
            (TR: self__Basetransl.transl_fundef fd = OK tfd)          
            (MK: self__Basetransl.match_cont k tk)
            (ISCC: self__Basetransl.Source.is_call_cont k),          
        match_states (self__Basetransl.Source.Callstate fd args k m)
                     (self__Basetransl.Target.Callstate tfd args tk m)
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
  Qed. FEnd transl_expr_correct.

  FInduction match_cont_seq_commutes about match_cont motive 
    (fun k tk (_ : match_cont k tk) =>
       forall s k' (M : k = Source.Kseq s k'),
       exists s' tk',
       tk = Target.Kseq s' tk' /\ match_cont k' tk').
  FProof.
  + intros. apply cheat (* fdiscriminate *).
  + intros. apply cheat.
  Qed. FEnd match_cont_seq_commutes.
    
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
  FEnd Basetransl.

  Family Implight extends Base.
  FEnd Implight.

  Family Imp extends Base.
  FEnd Imp.

  Family Impsharpminor extends Base.
  FEnd Impsharpminor.

  Family Impminor extends Base.
  FEnd Impminor. 

  (* Imp -> Implight *)
  Family SimplExpr extends Basetransl. 
    Family Source extends Imp.
    FEnd Source.
    
    Family Target extends Implight. 
    FEnd Target.
  FEnd SimplExpr.

  (* Implight -> Impsharpminor *)
  Family Impshmgen extends Basetransl. 
    Family Source extends Implight.
    FEnd Source.
    
    Family Target extends Impsharpminor. 
    FEnd Target.
  FEnd Impshmgen.

  (* Impsharpminor -> Impminor *)
  Family Impminorgen extends Basetransl. 
    Family Source extends Impsharpminor.
    FEnd Source.
    
    Family Target extends Impminor. 
    FEnd Target.
  FEnd Impminorgen.
FEnd BaseExt.

(* post/pre increment operators + assign ops *)
Family ArithExt extends BaseExt.  
  Inherit Implight.
  
  (* We want this nanopass: *)  
  (* Imp -> ImpEpostdecr -> ImpEpredecr -> ImpEpostincr -> ImpEpreincr -> Implight *)  

  (* We define the IRs in reverser order to enable sharing *)  
  (*      
     FInductive stmt : Type :=
       | Sskip: stmt
       | Sset : ident -> expr -> stmt            
       | Sseq: stmt -> stmt -> stmt.
       | Spreincr : ident -> stmt.
  *)
  Family ImpEpreincr extends Implight.
  FInductive stmt : Type :=
    | Spreincr : ident -> stmt.

  FInductive step : genv -> state -> trace -> state -> Prop :=  
    | step_preincr : forall ge f id k e le m v v',
        PTree.get id le = Some v -> (* Fetch the value of the variable *)
        v' = Val.add v (Vint Int.one) -> (* Increment the value by 1 *)
        step ge (self__ImpEpreincr.State f (Spreincr id) k e le m)
             E0 (self__ImpEpreincr.State f Sskip k e (PTree.set id v' le) m).
  FEnd ImpEpreincr.

  (* FInductive stmt : Type :=
       | Sskip: stmt
       | Sset : ident -> expr -> stmt            
       | Sseq: stmt -> stmt -> stmt.
       | Spreincr : ident -> stmt.
       | Spostincr : ident -> stmt. *)
  Family ImpEpostincr extends ImpEpreincr. 
  FInductive stmt : Type :=    
    | Spostincr : ident -> stmt.
  
  FInductive step : genv -> state -> trace -> state -> Prop :=  
    | step_postincr : forall ge f id k e le m v v',
      PTree.get id le = Some v -> (* Fetch the value of the variable *)
      v' = Val.add v (Vint Int.one) -> (* Increment the value by 1 *)
      step ge (self__ImpEpostincr.State f (Spostincr id) k e le m)
           E0 (self__ImpEpostincr.State f Sskip k e (PTree.set id v' le) m).
  FEnd ImpEpostincr.

  (* FInductive stmt : Type :=
       | Sskip: stmt
       | Sset : ident -> expr -> stmt            
       | Sseq: stmt -> stmt -> stmt.
       | Spreincr : ident -> stmt.
       | Spostincr : ident -> stmt. 
       | Spredecr : ident -> stmt.
   *)
  Family ImpEpredecr extends ImpEpostincr.
  FInductive stmt : Type :=
    | Spredecr : ident -> stmt.

  FInductive step : genv -> state -> trace -> state -> Prop :=  
    | step_predecr : forall ge f id k e le m v v',
        PTree.get id le = Some v -> (* Fetch the value of the variable *)
        v' = Val.sub v (Vint Int.one) -> (* Increment the value by 1 *)
        step ge (self__ImpEpredecr.State f (Spreincr id) k e le m)
             E0 (self__ImpEpredecr.State f Sskip k e (PTree.set id v' le) m).      
  FEnd ImpEpredecr.

  (* FInductive stmt : Type :=
       | Sskip: stmt
       | Sset : ident -> expr -> stmt            
       | Sseq: stmt -> stmt -> stmt.
       | Spreincr : ident -> stmt.
       | Spostincr : ident -> stmt. 
       | Spredecr : ident -> stmt.
       | Spostdecr : ident -> stmt.
   *)
  Family ImpEpostdecr extends ImpEpredecr.
  FInductive stmt : Type :=    
    | Spostdecr : ident -> stmt.    
  
  FInductive step : genv -> state -> trace -> state -> Prop :=  
    | step_postdecr : forall ge f id k e le m v v',
      PTree.get id le = Some v -> (* Fetch the value of the variable *)
      v' = Val.sub v (Vint Int.one) -> (* Increment the value by 1 *)
      step ge (self__ImpEpostdecr.State f (Spostdecr id) k e le m)
           E0 (self__ImpEpostdecr.State f Sskip k e (PTree.set id v' le) m).
  FEnd ImpEpostdecr.

  (* Finally, Imp is the source language, with all the features *)
  (* FInductive stmt : Type :=
       | Sskip: stmt
       | Sset : ident -> expr -> stmt            
       | Sseq: stmt -> stmt -> stmt.
       | Spreincr : ident -> stmt.
       | Spostincr : ident -> stmt. 
       | Spredecr : ident -> stmt.
       | Spostdecr : ident -> stmt.
       | Sassignop : binary_operation -> ident -> expr -> stmt.
   *)
  Family Imp extends ImpEpostdecr.
  FInductive stmt : Type := 
    | Sassignop : binary_operation -> ident -> expr -> stmt.

  FInductive step : genv -> state -> trace -> state -> Prop :=  
  | step_assignop : forall ge f op id a k e le m v1 v2 v',
      PTree.get id le = Some v1 -> (* Fetch the current value of the variable *)
      eval_expr e le a v2 -> (* Evaluate the expression a *)
      eval_binop op v1 v2 = Some v' -> (* Apply the binary operation op to v1 and v2 *)
      step ge (self__Imp.State f (Sassignop op id a) k e le m)
           E0 (self__Imp.State f Sskip k e (PTree.set id v' le) m).
  FEnd Imp.
  
  (* Nanopass: Imp *remove-assign*-> 
               ImpEpostdecr *remove-postdecr*-> 
               ImpEpredecr *remove-predecr*-> 
               ImpEpostincr *remove-postincr*-> 
               ImpEpreincr *remove-preincr*->
               Implight *)    

  (* We can also compose the passes in reverser order to 
     enable sharing and also automatically "merging" all 
     the nanopasses into one big pass *)

  
  (* This is the last pass which goes to Implight *)
  Family RemovePreincr extends Basetransl.
    Family Source extends ImpEpreincr.
    FEnd Source.

    Family Target extends Implight.
    FEnd Target.

    FRecursion transl_stmt.    
    Case Spreincr := (fun id =>
      OK (Target.Sset id 
            (Target.Ebinop Oadd 
               (Target.Evar id) 
               (Target.Econst (Ointconst Int.one))))). (* id := id + 1 *)
    FEnd transl_stmt.

    FInduction transl_stmt_correct. 
    FProof.
    + apply cheat.
    Qed. FEnd transl_stmt_correct.
  FEnd RemovePreincr.
  
  (* The 2nd-to-the last pass can extend the last pass
     and go directly to Implight. *)
  Family RemovePostincr extends RemovePreincr.
    Family Source extends ImpEpostincr.
    FEnd Source.

    Family Target extends Implight.
    FEnd Target.

    FRecursion transl_stmt.    
    Case Spostincr := (fun id =>
      OK (Target.Sseq
            (Target.Sset id 
               (Target.Ebinop Oadd (Target.Evar id) 
                  (Target.Econst (Ointconst Int.one)))) (* id := id + 1 *)
            Target.Sskip)).
    FEnd transl_stmt.

    FInduction transl_stmt_correct. 
    FProof.
    + apply cheat.    
    Qed. FEnd transl_stmt_correct.
  FEnd RemovePostincr.

  Family RemovePredecr extends RemovePostincr.
    Family Source extends ImpEpredecr.
    FEnd Source.

    Family Target extends Implight.
    FEnd Target.

    FRecursion transl_stmt. 
    Case Spredecr := (fun id =>
      OK (Target.Sset id 
            (Target.Ebinop Osub 
               (Target.Evar id) 
               (Target.Econst (Ointconst Int.one))))). (* id := id - 1 *)    
    FEnd transl_stmt.
    
    FInduction transl_stmt_correct. 
    FProof.
    + apply cheat.    
    Qed. FEnd transl_stmt_correct.
  FEnd RemovePredecr.

  Family RemovePostdecr extends RemovePredecr.
    Family Source extends ImpEpostdecr.
    FEnd Source.

    Family Target extends Implight.
    FEnd Target.
  
    FRecursion transl_stmt. 
    Case Spostdecr := (fun id =>
        OK (Target.Sset id 
              (Target.Ebinop Osub 
                 (Target.Evar id) 
                 (Target.Econst (Ointconst Int.one))))). (* id := id - 1 *)    
    FEnd transl_stmt.

    FInduction transl_stmt_correct. 
    FProof.
    + apply cheat.    
    Qed. FEnd transl_stmt_correct.
  FEnd RemovePostdecr.  

  (* Finally, the first pass can go directly to Implight 
     by extending the second pass (which also goes to Implight) *)
  Family RemoveAssignop extends RemovePostdecr.
    Family Source extends Imp.
    FEnd Source.

    Family Target extends Implight.
    FEnd Target.

    FRecursion transl_stmt.
    Case Sassignop := (fun op id e =>
      do te <- transl_expr e; (* Translate the expression e *)
      OK (Target.Sseq
            (Target.Sset id 
               (Target.Ebinop op 
                  (Target.Evar id) te)) (* id := id op te *)
            Target.Sskip)).
    FEnd transl_stmt.

    FInduction transl_stmt_correct. 
    FProof.
     + apply cheat.
    Qed. FEnd transl_stmt_correct.
  FEnd RemoveAssignop.

  (* Eventually, we can compose these series of nanopasses 
     with the base pass. We don't have to describe a "pipeline" 
     of passes becuase we just use late binding of nested families. 
     The resulting pass is a composition of all the nanopasses together 
     in a single pass (as if they were defined at once).  *)
  (* We reap the benefit of a modular nanopass style compiler, but 
      also don't loose any performance overhead due to chaining
      compiler passes. This essentially fuses the nanopasses. *)
  (* By fusing these passes together, we should be able to recover 
     the compilation speed of CompCert while retaining modularity. *)
  (* I belive this is very similar to: https://dl.acm.org/doi/10.1145/3140587.3062346 *)
  Family SimplExpr extends RemoveAssignop.
  FEnd SimplExpr.
FEnd ArithExt.


(*

(* structured control flow *)
Family Scf .
  Family Base.
  FInductive stmt : Type :=
    | Sifthenelse: expr -> stmt -> stmt -> stmt.    
  FEnd Base.

  Family Imp.
  FInductive stmt : Type := 
    | Sbreak : statement(* break statement *)
    | Scontinue : statement(* continue statement *)
    | Swhile : expr -> statement -> statement(* while loop *)
    | Sdowhile : expr -> statement -> statement(* do loop *)
    | Sfor: statement -> expr -> statement -> statement -> statement. (* for loop *)                    
  FEnd Imp.

  Family Implight.
  FInductive stmt : Type :=
    | Sloop: statement -> statement -> statement(* infinite loop *)
    | Sbreak : statement(* break statement *)
    | Scontinue : statement(* continue statement *)
  FEnd Implight.  
  
  Family Impsharpminor.
  FInductive stmt : Type :=
    | Sloop: stmt -> stmt
    | Sblock: stmt -> stmt
    | Sexit: nat -> stmt.
  FEnd Impsharpminor.

  Family Impminor.
  FInductive stmt : Type :=
    | Sloop: stmt -> stmt
    | Sblock: stmt -> stmt
    | Sexit: nat -> stmt.
  FEnd Impminor.
FEnd Scf.

(* unstructured control flow *)
Family Cf.
  Family Base.
  FInductive stmt : Type :=
    | Slabel: label -> stmt -> stmt
    | Sgoto: label -> stmt.    
  FEnd Base.
FEnd Cf.

(* Switch statement extension *)
Family SwitchExt extends Base.
  Family Imp.
  FInductive stmt : Type :=
    | Sswitch : expr -> lbl_stmts -> stmt (* switch statement *)
  with lbl_stmts : Type :=(* cases of a switch *)
    | LSnil: lbl_stmts
    | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
  FEnd Imp.

  Family Implight.
  FInductive stmt : Type :=
    | Sswitch : expr -> lbl_stmts -> stmt (* switch statement *)
  with lbl_stmts : Type :=(* cases of a switch *)
    | LSnil: lbl_stmts
    | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
  FEnd Implight.

  Family Impsharpminor.
   FInductive stmt : Type :=
    | Sswitch : bool -> expr -> lbl_stmts -> stmt (* switch statement *)
   with lbl_stmts : Type :=(* cases of a switch *)
    | LSnil: lbl_stmts
    | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
  FEnd Impsharpminor.

  Family Impminor.
  FInductive stmt : Type :=
     | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt.
  FEnd Impminor.
FEnd SwitchExt.

(* Array programming extension *)
Family ArrayExt extends Base.
FEnd ArrayExt.
*)
