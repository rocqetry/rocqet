(* Source -> Target transformation *)
family Impzero.ImpfrontendTransform {
  family Source extends Impfrontend { }
  family Target extends Impfrontend { }

  (* Semantics preservation of compilation proofs *)
  family CorrectnessProof { }
}
    
(* Correctness of the translation Source -> Target *)                         
family Impzero.Impgen.CorrectnessProof {  
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
    
    (* Correctness of translation *)
    family CorrectnessProof { }
}
