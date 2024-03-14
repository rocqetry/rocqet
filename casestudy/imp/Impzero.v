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
     family Program {
         Definition program := list statement
   
(* The semantics of the language *)                         
family Impzero.Impcommon {
    family Semantics {                                        
        family Values {
            Inductive value: Type :=
              | Vint: int -> val              
        }

        Inductive cont : Type :=
           | Kstop : cont
           | Kseq : statement -> cont -> cont           

        Inductive state: Type :=
           | State: forall (s: statement) (k: cont) (e: env), state        

         Definition eval_binop := ... 
         Inductive eval_expr: expression -> Values.value -> Prop :=
            | eval_Evar: forall id v,
                le!id = Some v ->
                eval_expr (Evar id) v           
            | eval_Econst: forall cst v,
                eval_constant cst = Some v ->
                eval_expr (Econst cst) v
            | eval_Eunop: forall op a1 v1 v,
                eval_expr a1 v1 ->
                eval_unop op v1 = Some v ->
                eval_expr (Eunop op a1) v
            | eval_Ebinop: forall op a1 a2 v1 v2 v,
                eval_expr a1 v1 ->
                eval_expr a2 v2 ->
                eval_binop op v1 v2 m = Some v ->
                eval_expr (Ebinop op a1 a2) v            
        
        Inductive eval_exprlist: list expression -> list Values.value -> Prop :=
          | eval_Enil:
              eval_exprlist nil nil
          | eval_Econs: forall a1 al v1 vl,
              eval_expr a1 v1 -> eval_exprlist al vl ->
              eval_exprlist (a1 :: al) (v1 :: vl).

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


(* What happens when Source is extended in a derived family? *)
(* What happens when Target is extended in a derived family? *)
(* Generating Imp-like IRs / translation from Source -> Target *)
family Impzero.Impgen {
  family Source extends Impcommon { }
  family Target extends Impcommon { }

  (* Semantics preservation of compilation proofs *)
  family Proofs { }
}
    
(* Correctness of the translation Source -> Target *)                         
family Impzero.Impgen.Proofs {  
  (* Correctness of B construction functions *)

  (* Basic preservation invariants *)
  Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSL).

  (* Matching between environments *)
  Record match_env (e: Source.Semantics.env) (te: Target.Semantics.env) : Prop :=
    mk_match_env { ... }
  
  Lemma transl_vars_names:
       forall ce vars tvars,
       mmap (transl_var ce) vars = OK tvars ->
       map fst tvars = var_names vars.
  Proof.
    ...
   Qed.

  (* Semantic preservation for expressions *)
  Lemma translate_expressionx_correct:
      forall a v,
      Source.Semantics.eval_expr a v ->
      forall ta, translate_expr a  = OK ta ->
      Target.Semantics.eval_expr ta v.
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
  
   Inductive match_cont : Source.Semantics.cont -> Target.Semantics.cont -> Prop :=
     | match_Kstop: match_cont Imp.Semantics.Kstop Kstop                 
     | match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
               transl_statement s = OK ts ->
               match_cont k tk ->
               match_cont (Source.Semantics.Kseq s k) (Target.Semantics.Kseq ts tk)

                               
   Inductive match_states : Source.Semantics.state -> Target.Semantics.state -> Prop := ...

  
   (* simulation proofs all have the same structure,
      you just have to fill in some lemmas, which are like holes
      for families which extend this proof *)
  (* The simulation proof *)
   Lemma translate_step:
       forall S1 S2, Source.Semantics.step S1 S2 ->
       forall T1, match_states S1 T1 ->
       exists T2, plus Target.Semantics.step T1 T2 /\ match_states S2 T2.
   Proof.
     induction 1; intros. 

     Case step_assign := ...

     Case step_seq := ...

     ...
   Qed.


   Lemma translate_initial_states: forall prog tprog,
         forall S, Source.Semantics.initial_state prog S ->
         exists R, Target.Semantics.initial_state tprog R /\ match_states S R.
   Proof.
     ...
   Qed.
  
   Lemma translate_final_states:
         forall S R r,
         match_states S R -> Source.Semantics.final_state S r -> Target.Semantics.final_state R r.
   Proof.
       intros. inv H0. inv H. inv MK. constructor.
   Qed. 
  
   Theorem translate_program_correct :
     forall (prog  : Source.Program.program)
            (tprog : Target.Program.program),
       forward_simulation (Source.Semantics.semantics prog) (Target.Semantics.semantics tprog).
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
family Impzero.Impshmgen extends Impgen {
   family Source extends Imp { }
   family Target extends Impsharpminor { }       
  
   (* This involves mostly simplification of control structures *)
    Fixpoint translate_expression := ... 
         
    Fixpoint translate_statment := ...

                                       
   (* Correctness proofs for Imp -> Impsharpminor *)      
   family Proofs {
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
family Impzero.Impminorgen extends Impgen {
  (* In this case the translation is the identity function *)
  Definition translate_constant += ...
  Fixpoint translate_expr += ...
  Fixpoint translate_statement += ...

  family Source extends Impsharpminor { }
  family Target extends Impminor { }      
  

}

family Impzero.Impminorgen {
  family Proofs {
      Inductive match_cont : [self].Source -> [self].Target -> Prop +=
          | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
              translate_statement cenv xenv s1 = OK ts1 ->
              match_cont (Impsharpminor.Semantics.Kseq s2 k) tk cenv xenv cs ->
              match_cont (Impminor.Semantics.Kseq (Csharpminor.Sseq s1 s2) k)
                         (Kseq ts1 tk) cenv xenv cs
          | match_Kblock: forall k tk,
              match_cont k tk  ->
              match_cont (Imsharpminor.Semantics.Kblock k)
                         (Impminor.Semantics.Kblock tk)
          | match_Kblock2: forall k tk,
              match_cont k tk -> match_cont k (Kblock tk)                                                                    
      (* This is the same thing from base family, so it
       inherited.
       All we have to do is prove the required lemmas *)
      (* Theorem transl_program_correct:
           forward_simulation (Csharpminor.semantics prog) (Cminor.semantics tprog).
         Proof.
           eapply forward_simulation_star; eauto.
           apply senv_preserved.
           eexact transl_initial_states.
           eexact transl_final_states.
           eexact transl_step_correct.
         Qed.
      *)
  }
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


