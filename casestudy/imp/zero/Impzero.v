(* Imp source language *)
family Impzero.Imp {
    Inductive expression : Type :=
      | Var : ident -> expression
      | Lit : nat -> expression 
      | Plus : expression -> expression -> expression
      | Minus : expression -> expression -> expression
      | Mult : expression -> expression -> expression

    Inductive statement : Type :=
      | Assign (x : ident) (e : expression)       (* x = e *)
      | Seq    (a b : statement)                  (* a ; b *)
      | If     (i : expression) (t e : statement) (* if (i) then { t } else { e } *)
      | While  (t : expression) (b : statement)   (* while (t) { b } *)
      | Skip                                      (* ; *)
    
    family Semantics {            
      Inductive cont : Type :=
        | Kstop : cont
        | Kseq : statement -> cont -> cont
        | Kwhile : expression -> statement -> cont -> cont      

      Inductive step : state -> state -> Prop = ...                                           
    }

    Inductive program := ...
}

(* Implight IR *)
family Impzero.Implight extends Impcommon {
  Inductive expression : Type += ...

  Inductive statement : Type += ...                                   

  family Semantics {
      Inductive cont : Type += ...

      Inductive step : Type += ...
  }  
}

(* Simplify Expression *)
(* Translation from Imp -> Implight *)
family Impzero.ImpgenSimplExpr {
   family Source extends Imp { }
   family Target extends Implight { }
     
    Definition translate_constant := ...
    Fixpoint translate_expression := ...
    Fixpoint translate_statement := ...
   
   family Proofs {
     Inductive match_cont := ...

     Inductive match_states := ...

     Lemma translate_initial_states : ...

     Lemma translate_final_states: ...

     Theorem translate_program_correct : ...
   }
}

(* Impsharpminor frontend IR *)
family Impzero.Impsharpminor extends Impcommon {  
     Inductive expression : Type +=  ...        

     Inductive statement : Type += ...                

     family Semantics {
       Inductive cont: Type += ...            
                                                            
       Inductive step: state -> state -> Prop += ...
     }     
}

(* Translation from Imp -> Impsharpminor *)
family Impzero.Impshmgen extends Impgen {
   family Source extends Implight { }
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

  Inductive statement : Type +=                                
     | Sblock: statement -> statement
     | Sexit: nat -> statement
     | Sswitch: bool -> expr -> lbl_statement -> statement
     | Sloop: statement -> statement

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
                         (State (seq_of_lbl_statement (select_switch n cases)) k e)            
                | step_label: forall lbl s k e,
                   step (State (Slabel lbl s) k e)
                        (State s k e)
    }
}

(* Translation from Impsharpminor -> Impminor *)
family Impzero.Impminorgen extends Impgen {
  (* In this case the translation is the identity function *)
  Definition translate_constant += ...
  Fixpoint translate_expression += ...
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

family Impzero.Asm {  
  (* This is a parameter *)  
  family Op extends {
      Inductive operation := ...

      Inductive condition := ...
  }
}

family Impzero.ImppminorSel extends Impcommon {         
  Inductive expression : Type +=
    | Eop : Asm.Op.operation -> exprlist -> expression                        
    | Econdition : condexpr -> expr -> expr -> expr
    | Elet : expr -> expr -> expr
    | Eletvar : nat -> expr

  with exprlist : Type :=
   | Enil: exprlist
   | Econs: expr -> exprlist -> exprlist
                                 
  with condexpr : Type :=
    | CEcond : Asm.Op.condition -> exprlist -> condexpr
    | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
    | CElet: expression -> condexpr -> condexpr.


  Inductive exitexpr : Type :=
     | XEexit: nat -> exitexpr
     | XEjumptable: expr -> list nat -> exitexpr
     | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
     | XElet: expr -> exitexpr -> exitexpr

  (* Overriding some constructors here *)
  Inductive statement : Type +=
     | Sswitch: exitexpr -> statement
     | Sifthenelse: condexpr -> statement -> statement -> statement
                              
  family Semantics {
    Inductive eval_expr: letenv -> expr -> val -> Prop := ...

    with eval_exprlist: letenv -> exprlist -> list val -> Prop := ...

    with eval_condexpr: letenv -> condexpr -> bool -> Prop :=  ...

    Inductive eval_exitexpr: letenv -> exitexpr -> nat -> Prop := ...

    Inductive step: state -> trace -> state -> Prop := ...
  }
}

(* Instruction Selection *)
(* Translation from Impminor -> ImpminorSel *)
family Impzero.ImpSelection extends Impgen {
  family Source extends Impminor { }
  family Target extends ImpminorSel { }

  family Proofs {
    Inductive match_cont := ...

    Theorem translate_program_correct: forall prog tprog,
        forward_simulation (Source.semantics prog) (Target.semantics tprog).
    Proof.
      ...
    Qed.
  }
}
  
family Impzero {
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


