family Impzero.Impminor extends Impcommon {
  Inductive expression : Type += ...     

  Inductive statement : Type += ...

  family Semantics {                        
    Inductive cont: Type += ...            
                                                            
    Inductive step: state -> state -> Prop += ...
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
