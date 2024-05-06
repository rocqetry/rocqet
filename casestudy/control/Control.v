(* Imp with control flow statements *)
family Impcontrol extends Base { }

family Impcontrol.Imp {
  Inductive statement += 
     | While  (t : expression) (b : statement)   (* while (t) { b } *)
     | Break 
     | Continue 

    family Semantics {
      Inductive cont += 
         | Kwhile : expression -> statement -> cont -> cont
  
       Inductive step : state -> state -> Prop += 
         | KS_WhileTrue : forall st b c k,
             beval st b = true ->
             kstep (<{ while b do c end }>, k, st) (c, Kwhile b c k, st)
         | KS_WhileFalse : forall st b c k,
             beval st b = false ->
             kstep (<{ while b do c end}>, k, st) (CSkip, k, st)
         | KS_SkipWhile: forall b c k st,
              kstep (CSkip, Kwhile b c k, st) (<{ while b do c end }>, k, st)
    }
}

family Impcontrol.Implightgen {
  family S extends Imp { }
  family T extends Implight { }
  
  Inductive match_cont : S.Semenatics.cont -> T.Semantics.cont -> Prop := 
    | match_Kwhile1: forall ce r s k s' a ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont_exp ce For_val a
         (Csem.Kwhile1 r s k)
         (Kseq (makeif a Sskip Sbreak)
           (Kseq ts (Kloop1 (Ssequence s' ts) Sskip tk)))

  (* Inductive match_states : S.Semantics.state -> T.Semantics.state := ... *)
  
  Field translate_program {
      Case While := ...
  }

  family CorrectnessProofs {
      Lemma translate_step:
       forall S1 S2, S.Semantics.step S1 S2 ->
       forall T1, match_states S1 T1 ->
       exists T2, plus T.Semantics.step T1 T2 /\ match_states S2 T2.
      Proof.  
        Case While := ...     
      Qed.
  }
}

family Imploop.Impfrontend { 
    Inductive statement : Type +=
       | Sloop: statement -> statement -> statement (**r infinite loop *)       
}

family Imploop.Impfrontend.Semantics {
  Inductive cont : Type += ...

  Inductive step : state -> state -> Prop += 
    | step_loop: forall f s k e le m,
      step (State f (Sloop s) k e le m)
        E0 (State f s (Kseq (Sloop s) k) e le m)                                          
}

family Imploop.ImpfrontendTransform { 
  Definition translate_program := ...
  family Proofs {
      Lemma translate_step:
       forall S1 S2, Source.Semantics.step S1 S2 ->
       forall T1, match_states S1 T1 ->
       exists T2, plus Target.Semantics.step T1 T2 /\ match_states S2 T2.
      Proof.  
        Case Sloop := ...     
      Qed.


  (*  Lemma translate_initial_states: ... Inherited *)
   
  (* Lemma translate_final_states: Inherited *)
  
  (* Theorem translate_program_correct : Inherited *)
  
  }                                  
}

family Imploop.Impbackend { }

family Impgoto extends Impzero { }
family Impgoto.Imp {
  Inductive statement += 
      | Label : label -> statement -> statement
      | Goto : label -> statement
}
