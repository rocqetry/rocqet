family Impzero.ImpMinor extends MinorLanguage {
  Inductive expression : Type := 
     | Evar : ident -> expression
     | Econst : constant -> expression
     | Eunop : unary_operation -> expression -> expression
     | Ebinop : binary_operation -> expression -> expression -> expression     

  Inductive statement : Type := 
     | Sskip: statement
     | Sassign : ident -> expression -> statement     
     | Sseq: statement -> statement -> statement
     | Sifthenelse 
        : self(Impminor).expression -> statement -> statement -> statement
     | Sloop: statement -> statement
     | Sblock: statement -> statement
     | Sexit: nat -> statement
     | Sswitch 
        : bool -> self(Impminor).expression -> list (Z * nat) -> nat -> statement
     | Sgoto: label -> statement

  family Semantics {
    Inductive cont: Type :=
      | Kstop: cont (* stop program execution *)
      | Kseq: self(Impminor).statement -> cont -> cont (* execute stmt, then cont *)
      | Kblock: cont -> cont (* exit a block, then do cont *)
      | Kcall: option ident -> function -> val -> env -> cont -> cont    

    Inductive state: Type :=
      | State : (* Execution within a function *)
          forall (f: function) (* currently executing function *)
                 (s: stmt) (* statement under consideration *)
                 (k: cont) (* its continuation -- what to do next *)
                 (sp: val) (* current stack pointer *)
                 (e: env), (* current local environment *)
          state
      | Callstate : (* Invocation of a function *)
          forall (f: fundef) (* function to invoke *)
                 (args: list val) (* arguments provided by caller *)
                 (k: cont), (* what to do next *)
          state
      | Returnstate : (* Return from a function *)
          forall (v: val) (* Return value *)
                 (k: cont), (* what to do next *)
          state. 

    Inductive eval_expr: expr -> val -> Prop :=
      | eval_Evar: forall id v,
          PTree.get id e = Some v ->
          eval_expr (Evar id) v
      | eval_Econst: forall cst v,
          eval_constant sp cst = Some v ->
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
                                                            
    Inductive step: self(Semantics).state -> trace -> self(Semantics).state -> Prop := 
       | step_skip_seq: forall f s k sp e m,
           step (State f Sskip (Kseq s k) sp e m)
             E0 (State f s k sp e m)
       | step_skip_block: forall f k sp e m,
           step (State f Sskip (Kblock k) sp e m)
             E0 (State f Sskip k sp e m)
       | step_skip_call: forall f k sp e m m',
           is_call_cont k ->
           Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
           step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
             E0 (Returnstate Vundef k m')
     
       | step_assign: forall f id a k sp e m v,
           eval_expr sp e m a v ->
           step (State f (Sassign id a) k sp e m)
             E0 (State f Sskip k sp (PTree.set id v e) m)  
       | step_seq: forall f s1 s2 k sp e m,
           step (State f (Sseq s1 s2) k sp e m)
             E0 (State f s1 (Kseq s2 k) sp e m)
     
       | step_ifthenelse: forall f a s1 s2 k sp e m v b,
           eval_expr sp e m a v ->
           Val.bool_of_val v b ->
           step (State f (Sifthenelse a s1 s2) k sp e m)
             E0 (State f (if b then s1 else s2) k sp e m)     
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

     Inductive initial_state (p: program): state -> Prop :=
       | initial_state_intro: forall b f m0,
           let ge := Genv.globalenv p in
           Genv.init_mem p = Some m0 ->
           Genv.find_symbol ge p.(prog_main) = Some b ->
           Genv.find_funct_ptr ge b = Some f ->
           funsig f = signature_main ->
           initial_state p (Callstate f nil Kstop m0).  
     
    Inductive final_state: state -> int -> Prop :=
      | final_state_intro: forall r m,
          final_state (Returnstate (Vint r) Kstop m) r.

     Definition semantics (p: program) :=
       Semantics step (initial_state p) final_state (Genv.globalenv p).
  }
}

(* Translation from Impsharpminor -> Impminor *)
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
