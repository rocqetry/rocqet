(* Imp with function calls *)
family Impfunctions extends Impzero { }

family Impfunctions.Impcommon {
   Inductive statement : Type +=
     | Scall: option ident -> expression -> list expression -> statement
     | Sreturn : option expression -> statement

   family Program { } (* We inherit the necessary items here *)
}

family Impfunctions.Impcommon {
    family Semantics {
      Inductive cont : Type +=
         | Kcall:
            option ident -> 
            Program.function -> 
            env ->                       
            temp_env -> 
            cont -> 
            cont.

      Inductive state : Type +=
         | Callstate:                        
              forall (f: Program.fundef)
                     (args: list Value.value)
                     (k: cont), state
         | Returnstate: 
              forall (v: Value.value) (k: cont), state.

      Inductive step : state -> state -> Prop += 
          | step_call: forall f optid sig a bl k e le m vf vargs fd,
               eval_expr e le m a vf ->
               eval_exprlist e le m bl vargs ->
               Genv.find_funct ge vf = Some fd ->
               funsig fd = sig ->
               step (State f (Scall optid a bl) k e le m)
                    (Callstate fd vargs (Kcall optid f e le k) m)
          | step_return_0: forall f k e le m m',
              Mem.free_list m (blocks_of_env e) = Some m' ->
              step (State f (Sreturn None) k e le m)
                   (Returnstate Vundef (call_cont k) m')
          | step_return_1: forall f a k e le m v m',
              eval_expr e le m a v ->
              Mem.free_list m (blocks_of_env e) = Some m' ->
              step (State f (Sreturn (Some a)) k e le m)
                   (Returnstate v (call_cont k) m')
          | step_skip_call: forall f k e le m m',
              is_call_cont k -> 
              Mem.free_list m (blocks_of_env e) = Some m' ->
              step (State f Sskip k e le m)
                E0 (Returnstate Vundef k m')
          | step_internal_function: forall f vargs k m e le m1,
               function_entry f vargs m e le m1 -> (* function_entry?? *)
               step (Callstate (Internal f) vargs k m)
                    (State f f.(fn_body) k e le m1)
          | step_returnstate: forall v optid f e le k m,
              step (Returnstate v (Kcall optid f e le k) m)
                   (State f Sskip k e (set_opttemp optid v le) m). (* set_opttemp?? *)
    }
  
}

family Impfunctions.Impgen { }

family Impfunctions.Impgen.Proofs { 
  Inductive match_cont : Source.Semantics.cont -> Target.Semantics.cont -> Prop += 
        | match_Kcall: forall optid fn e le k tfn sp te tk lo hi cs sz cenv',
         transl_funbody cenv sz fn = OK tfn ->
         match_cont k tk  ->
         match_cont (Source.Semantics.Kcall optid fn e le k)
                    (Target.Semantics.Kcall optid tfn e te tk)

  Inductive match_states Source.Semantics.state -> Target.Semantics.state -> Prop += 
     | match_callstate:
        forall fd args k m tfd tk targs tres cconv cu ce          
          (TR: match_fundef cu fd tfd)
          (MK: match_cont ce tres k tk)
          (ISCC: Source.is_call_cont k)          
         match_states (Source.Semantics.Returnstate.Callstate fd args k m)
                      (Target.Semantics.Returnstate.Callstate tfd args tk m)
    | match_returnstate:
        forall res tres k m tk ce
            (MK: match_cont k tk)
            (WT: wt_val res tres),
        match_states (Source.Semantics.Returnstate res k m)
                     (Target.SemanticsReturnstate res tk m).
}

family Impfunctions.Impgen {    
    family Proofs {
       Lemma translate_step:
          forall S1 S2, Source.Semantics.step S1 S2 ->
          forall T1, match_states S1 T1 ->
          exists T2, plus Target.Semantics.step T1 T2 /\ match_states S2 T2.
       Proof.
        (* Handle the new instruction *)
        Case call := ... 
       Qed.
    }
}

(* They get the proof for free *)
family Impfunctions.Impshmgen { }
family Impfunctions.Impminorgen { }
family Impfunctions.ImpSelectioon { }
