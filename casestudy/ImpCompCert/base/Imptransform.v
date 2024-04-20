family Impzero.SimulationDiagram { 
    family Source extends L { }
    family Target extends { }

    (* This is used to prevennt anti-stuttering in the source language's 
       transistion *)
    (* We need to have a default value for plus or lock-step state relation, 
       because we don't need a measure for that to work.  *)
    (* family Measure {
      
    }*)
    Field compute_measure : Source.state -> Source.state -> Prop := ...
    
    (* Relation Between the state of S and T *)
    family Relation {
        
    } 

    Lemma translate_step:
       forall S1 S2, Source.Semantics.step S1 S2 ->
       forall T1, match_states S1 T1 ->
       exists T2, star Target.Semantics.step T1 T2 /\ match_states S2 T2 /\ compute_measure s1 s2.
    Proof.
}


(* Source -> Target transformation *)
family Impzero.ImpfrontendTransform  extends SimulationDiagram {
  family Source extends Impfrontend { }
  family Target extends Impfrontend { }
}
    
(* Simulation proof of the translation Source -> Target *)                         
family Impzero.Impgen.CorrectnessProof extends SimulationDiagram {
  (* Matching between environments *)  
  Record match_env (e: Source.Semantics.env) (te: Target.Semantics.env) : Prop :=
    mk_match_env { ... }  

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

     Case assign := ...

     Case seq := ...

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
       ....
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

family Impzero.ImpbackendTransform {
    (* Translation from Source -> Target *)
    family Source Impbackend { }
    family Target Impbackend { }        
    
    Definition transform_function := ...

    Definition transform_fundef := ...
    
    Definition tranform_program := ...
    
    (* Correctness of translation *)
    family CorrectnessProof { 
       (* There should be a parameter about the forward simulation
          This parameter should be denote if it is a `star` for `plus` 
          forward simulation  *)
       Inductive match_stackframes: Source.Semantics.stackframe -> Target.Semantics.stackframe -> Prop := ...          
       Inductive match_states : Source.Semantics.state -> Target.Semantics.state -> Prop :=  ...

       Theorem transf_step_correct:
           forall s1 t s2, Source.Semantics.step ge s1 t s2 ->
           forall (WTS: wt_state s1) s1' (MS: match_states s1 s1'),
           exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
       Proof.
         ...
       Qed.
       
       Lemma transf_initial_states:
           forall st1, Source.Semantics.initial_state prog st1 ->
           exists st2, Source.Semantics.initial_state tprog st2 /\ match_states st1 st2.
      Proof.
        ...
      Qed.
       

       Theorem transf_program_correct: forall prog tprog,
          forward_simulation (Source.Semantics.semantics prog) (Source.Semantics.semantics tprog).
       Proof.
         ...
       Qed.
    }
}
