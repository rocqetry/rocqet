(* A base family for Imp frontend languages *)
family Impzero.Impcommon {
    Inductive constant : Type :=
        | Ointconst: int -> constant

    Inductive unary_operation : Type := ...                              

    Inductive binary_operation : Type :=
        | Binplus
        | Binminus
        | Binmult.

     Inductive expression : Type :=
        | Evar : ident -> expr 
        | Econst : constant -> expr
        | Ebinop : binary_operation -> expr -> expr -> expr.

     Inductive statement : Type :=
        | Sassign : label -> expression -> statement
        | Sseq    : statement -> statement -> statement
        | Sifthenelse : expression -> statement -> statement -> statement        
        | Sskip : statement.      

    (* Top level programs *)
    family Program { }
}

(* The semantics of the language *)                         
family Impzero.Impcommon {
    family Semantics {                                        
        Inductive cont : Type :=
           | Kstop : cont
           | Kseq : statement -> cont -> cont           

        Inductive state: Type :=
           | State: forall (s: statement) (k: cont) (e: env), state

        Inductive eval_expr: expr -> val -> Prop := ...
                                                                
        Inductive eval_exprlist: list expr -> list val -> Prop := ...

        (* A common small step continuation-based semantics for frontned languages *)
        Inductive step : [self].state -> [self].state -> Prop :=
             | step_assign : forall st i a k n,            
                 aeval st a = n ->
                 step (State (Sassign i a) k st)
                   (State Sskip k (t_update st i n))
             (* | step_set: forall f id a k e le m v,
                     eval_expr e le m a v -> (* TODO : fix this *)
                     step (State (Sset id a) k e)
                          (State Sskip k (PTree.set id v e)) *)                                    
             | step_seq : forall st c1 c2 k,  
                 step (State (Sseq c1 c2) k st)
                       (State c1 (Kseq c2 k) st)                             
             | step_iftrue : forall st b c1 c2 k,
                 beval st b = true ->
                 step (State (Sifthenelse b c1 c2) k st)
                       (State c1 k st)                   
             | step_iffalse : forall st b c1 c2 k,
                 beval st b = false ->
                 step (State (Sifthenelse b c1 c2) k st)
                   (State c2 k st)
             (* | step_ifthenelse: forall a s1 s2 k e le m v b,
                     eval_expr e le m a v ->
                     Val.bool_of_val v b -> (* TODO: fix this *)
                     step (State (Sifthenelse a s1 s2) k e)
                          (State (if b then s1 else s2) k e) *)
             | step_skip_seq: forall c k st,
                 step (State Sskip (Kseq c k) st)
                      (State c k st)                               
        
        (* Definitions *)        
        Definition initial_state := ...
        Definition final_state := ...
        Definition semantics := ...
    }
}

(* Translation from A -> B *)
family Impzero.Implowering {
  family A extends Impcommon { }
  family B extends Impcommon { }

  family Proofs {
    (* Semantics preservation of compilation proofs *)
  }
}
    
(* Correctness of the translation A -> B *)                         
family Impzero.ImpcommonProofs {  
  family A extends Impcommon { }
  family B extends Impcommon { }

  (* Correctness of B construction functions *)

  (* Basic preservation invariants *)
  Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSL).

  (* Matching between environments *)
  Record match_env (e: A.Semantics.env) (te: B.Semantics.env) : Prop :=
    mk_match_env { ... }
  
  Lemma transl_vars_names:
       forall ce vars tvars,
       mmap (transl_var ce) vars = OK tvars ->
       map fst tvars = var_names vars.
  Proof.
    ...
   Qed.

  (* Semantic preservation for expressions *)
  Lemma translate_expr_correct:
      forall a v,
      A.Semantics.eval_expr ge e le m a v ->
      forall ta, transl_expr cunit.(prog_comp_env) a = OK ta ->
      B.Semantics.eval_expr tge te le m ta v.
  Proof.
    ...
  Qed.

  (*              
                                        match_states
                A.Semantics.state  ----------------------- B.Semantics.state 
                      |                                        |
                      |                                        | *
                      |                                        |
                      v                                        v
                   A.Semantics.state' ----------------------- B.Semantics.state'
                                          match_states 
   *)
  
   Inductive match_cont : A.Semantics.cont -> B.Semantics.cont -> Prop :=
     | match_Kstop: match_cont Imp.Semantics.Kstop Kstop                 
     | match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
               transl_statement s = OK ts ->
               match_cont k tk ->
               match_cont (A.Semantics.Kseq s k) (B.Semantics.Kseq ts tk)

                               
   Inductive match_states : A.Semantics.state -> B.Semantics.state -> Prop := ...

  
   (* simulation proofs all have the same structure,
      you just have to fill in some lemmas, which are like holes
      for families which extend this proof *)
  (* The simulation proof *)
   Lemma translate_step:
       forall S1 S2, A.Semantics.step S1 S2 ->
       forall T1, match_states S1 T1 ->
       exists T2, plus B.Semantics.step T1 T2 /\ match_states S2 T2.
   Proof.
     induction 1; intros. 

     Case step_assign := ...

     Case step_seq := ...

     ...
   Qed.


   Lemma translate_initial_states: forall prog tprog,
         forall S, A.Semantics.initial_state prog S ->
         exists R, B.Semantics.initial_state tprog R /\ match_states S R.
   Proof.
     ...
   Qed.
  
   Lemma translate_final_states:
         forall S R r,
         match_states S R -> A.Semantics.final_state S r -> B.Semantics.final_state R r.
   Proof.
       intros. inv H0. inv H. inv MK. constructor.
   Qed. 
  
   Theorem translate_program_correct : forall (prog: A.Program.program) (tprog : B.Program.program),
       forward_simulation (A.Semantics.semantics prog) (B.Semantics.semantics tprog).
   Proof.
     eapply forward_simulation_plus.
     apply senv_preserved.
     eexact translate_initial_states.
     eexact translate_final_states.
     eexact translate_step.
   Qed.
}                        

(* Imp source language *)
family Impzero.Imp extends Impcommom {        
    Inductive statement : Type +=      
        | Swhile  : expression -> statement -> statement

    family Semantics {            
      Inductive cont : Type +=           
        | Kwhile : expression -> statement -> cont -> cont              

      Inductive step : [self].state -> [self].state -> Prop +=             
        | KS_WhileTrue : forall st b c k,
            beval st b = true ->
            step (State (Swhile b c) k st)
                  (State c (Kwhile b c k) st)
        | KS_WhileFalse : forall st b c k,
            beval st b = false ->
            step (State (Swhile b c) k st)
                  (State Sskip k st)
        | KS_SkipWhile: forall b c k st,
            step (State Sskip (Kwhile b c k) st)
                  (State (Swhile b c) k st)
    }
}                   
                         
family Impzero.Imp {
   family Program { }
}

(* Impsharpminor frontend IR *)
family Impzero.Impsharpminor extends Impcommon {  
     Inductive expression : Type +=                        
        | Eunop : unary_operation -> expression -> expression

     Inductive stmt : Type +=                                
        | Sblock: stmt -> stmt
        | Sexit: nat -> stmt
        | Sswitch: bool -> expr -> lbl_stmt -> stmt
        | Sloop: stmt -> stmt

        with lbl_stmt : Type :=
           | LSnil: lbl_stmt
           | LScons: option Z -> stmt -> lbl_stmt -> lbl_stmt

     family Semantics {
         Inductive cont: Type +=            
            | Kblock: cont -> cont         
                                                            
         Inductive step: state -> state -> Prop +=                
             | step_skip_block: forall k e,
                   step (State Sskip (Kblock k) e)
                        (State Sskip k e)                               
             | step_loop: forall s k e le m,
                   step (State (Sloop s) k e)
                        (State s (Kseq (Sloop s) k) e)
              | step_block: forall f s k e,
                   step (State (Sblock s) k e)
                        (State s (Kblock k) e)               
              | step_exit_seq: forall n s k e,
                  step (State (Sexit n) (Kseq s k) e)
                       (State (Sexit n) k e)
              | step_exit_block_0: forall k e,
                  step (State (Sexit O) (Kblock k) e)
                       (State Sskip k e)
              | step_exit_block_S: forall f n k e,
                  step (State (Sexit (S n)) (Kblock k) e)
                       (State (Sexit n) k e)              
              | step_switch: forall islong a cases k e m v n,
                    eval_expr e le m a v ->
                    switch_argument islong v n -> (* TODO: evalutaion *)
                    step (State (Sswitch islong a cases) k e)
                         (State (seq_of_lbl_stmt (select_switch n cases)) k e)            
                | step_label: forall lbl s k e,
                   step (State (Slabel lbl s) k e)
                        (State s k e)               
       }     
}

(* Translation from Imp -> Impsharpminor *)
family Impzero.Impshmgen {
   (* This involves mostly simplification of control structures *)
    Fixpoint translate_expression := ...

         
    Fixpoint translate_statment := ...

                                       
   (* Correctness proofs for Imp -> Impsharpminor *)      
   family Proofs extends Impcommonproofs {
         (*              
                           match_states
           Imp.state  ----------------------- Impsharpminor.state 
             |                                   |
             |                                   | *
             |                                   |
             v                                   v
          Imp.state' ----------------------- Impsharpminor.state'
                          match_states 
         *)
      Inductive match_cont : Imp.Semantics.cont -> [self].Semantics.cont -> Prop +=                  
         | match_Kwhile (* TODO: how does while relate to the semantics of Impsharpminor? *)
                 
      Inductive match_states : Imp.Semantics.state -> [self].Semantics.state -> Prop +=
         | match_state:
             forall f nbrk ncnt s k e le m tf ts tk te ts' tk' cu,                         
                 (TR: translate_statement cu.(prog_comp_env) nbrk ncnt s = OK ts)
                 (MTR: match_transl ts tk ts' tk')
                 (MK: match_cont k tk),
                        match_states (Imp.Semantics.State s k e)
                                     ([self].Semantics.State tf ts' tk' te le m)
}

family Impzero.Impminor extends Impcommon {
  Inductive expression : Type +=                        
     | Eunop : unary_operation -> expression -> expression

  Inductive stmt : Type +=                                
     | Sblock: stmt -> stmt
     | Sexit: nat -> stmt
     | Sswitch: bool -> expr -> lbl_stmt -> stmt
     | Sloop: stmt -> stmt

  family Semantics {                        
    Inductive cont: Type +=            
      | Kblock: cont -> cont

     (* This is basically the same as Impzero.Impsharpminor *)
     Inductive step: state -> state -> Prop +=                
             | step_skip_block: forall k e,
                   step (State Sskip (Kblock k) e)
                        (State Sskip k e)                               
             | step_loop: forall s k e le m,
                   step (State (Sloop s) k e)
                        (State s (Kseq (Sloop s) k) e)
              | step_block: forall f s k e,
                   step (State (Sblock s) k e)
                        (State s (Kblock k) e)               
              | step_exit_seq: forall n s k e,
                  step (State (Sexit n) (Kseq s k) e)
                       (State (Sexit n) k e)
              | step_exit_block_0: forall k e,
                  step (State (Sexit O) (Kblock k) e)
                       (State Sskip k e)
              | step_exit_block_S: forall f n k e,
                  step (State (Sexit (S n)) (Kblock k) e)
                       (State (Sexit n) k e)              
              | step_switch: forall islong a cases k e m v n,
                    eval_expr e le m a v ->
                    switch_argument islong v n -> (* TODO: evalutaion *)
                    step (State (Sswitch islong a cases) k e)
                         (State (seq_of_lbl_stmt (select_switch n cases)) k e)            
                | step_label: forall lbl s k e,
                   step (State (Slabel lbl s) k e)
                        (State s k e)
    }
}

(* Translation from Impsharpminor -> Impminor *)
family Impzero.Impminorgen extends Implowering {
  
}

  
family Impzero {
   family ImppminorSel extends Impcommon {

   }

   family LTL { }

   family RTL { }

   family Linearcommon {
       family Semantics { }
   }

   family Linear extends Linearcommon {
          
   }

   family Mach extends Linearcommon {

   }

   family Processor {
      family Op { }      
   } 

   family Aarch64 extends Processor {
      family Op { }
   }
}


