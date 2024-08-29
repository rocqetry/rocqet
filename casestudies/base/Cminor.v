family Cminor extends CminorVariant { 
  Inductive statement : Type +=     
     | Sloop: statement -> statement
     | Sblock: statement -> statement
     | Sexit: nat -> statement     
     | Sgoto: label -> statement
     | Sswitch 
        : bool -> self(Impminor).expression -> list (Z * nat) -> nat -> statement

  family Semantics {    
    Inductive cont: Type +=      
      | Kblock: cont -> cont (* exit a block, then do cont *)      

    Inductive state: Type :=
      | State : (* Execution within a function *)
          forall (sp: val), (* current stack pointer *)                 
          state      
                                                            
    Inductive step: state -> trace -> state -> Prop :=
       | step_skip_block: forall f k sp e m,
           step (State f Sskip (Kblock k) sp e m)
             E0 (State f Sskip k sp e m)
       | step_skip_call: forall f k sp e m m',
           is_call_cont k ->
           Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
           step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
             E0 (Returnstate Vundef k m')            
       | step_loop: forall f s k sp e m,
           step (State f (Sloop s) k sp e m)
             E0 (State f s (Kseq (Sloop s) k) sp e m)     
       | step_block: forall f s k sp e m,
           step (State f (Sblock s) k sp e m)
             E0 (State f s (Kblock k) sp e m)
       | step_exit_seq: forall f n s k sp e m,
           step (State f (Sexit n) (Kseq s k) sp e m)
             E0 (State f (Sexit n) k sp e m)
      | step_exit_block_0: forall f k sp e m,
          step (State f (Sexit O) (Kblock k) sp e m)
            E0 (State f Sskip k sp e m)
      | step_exit_block_S: forall f n k sp e m,
          step (State f (Sexit (S n)) (Kblock k) sp e m)
            E0 (State f (Sexit n) k sp e m)
    
      | step_switch: forall f islong a cases default k sp e m v n,
          eval_expr sp e m a v ->
          switch_argument islong v n ->
          step (State f (Sswitch islong a cases default) k sp e m)
            E0 (State f (Sexit (switch_target n default cases)) k sp e m)
     | step_label: forall f lbl s k sp e m,
         step (State f (Slabel lbl s) k sp e m)
           E0 (State f s k sp e m)
   
     | step_goto: forall f lbl k sp e m s' k',
         find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
         step (State f (Sgoto lbl) k sp e m)
           E0 (State f s' k' sp e m)    
  }
}

(* Translation from Impsharpminor -> Impminor *)
(* Nanopasses: *)
(* 
1. Stack allocation of local variables
2. Translation of switch statements to a simpler variant
*)
family Impzero.Impminorgen extends ImpfrontendTransform {
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
