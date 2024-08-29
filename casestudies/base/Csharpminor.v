family Csharpminor extends ClightVariant {        
     Inductive statement : Type :=
        | Sskip: statement
        | Sset : ident -> expr -> statement                
        | Sseq: statement -> statement -> statement
        | Sifthenelse: expr -> statement -> statement -> statement
        | Sloop: statement -> statement
        | Sblock: statement -> statement
        | Sexit: nat -> statement
        | Sswitch: bool -> expr -> lbl_statement -> statement
        | Slabel: label -> statement -> statement
        | Sgoto: label -> statement

        with lbl_statement : Type :=
          | LSnil: lbl_statement
          | LScons: option Z -> statement -> lbl_statement -> lbl_statement.
     

     family Semantics {
       Inductive cont: Type :=
         | Kstop: cont (* stop program execution *)
         | Kseq: stmt -> cont -> cont (* execute stmt, then cont *)
         | Kblock: cont -> cont (* exit a block, then do cont *)
         | Kcall: option ident -> function -> env -> temp_env -> cont -> cont

       Inductive state: Type :=
         | State:(* Execution within a function *)
             forall (f: function)(* currently executing function *)
                    (s: stmt)(* statement under consideration *)
                    (k: cont)(* its continuation -- what to do next *)
                    (e: env)(* current local environment *)
                    (le: temp_env),(* current temporary environment *)                    
             state
         | Callstate:(* Invocation of a function *)
             forall (f: fundef)(* function to invoke *)
                    (args: list val)(* arguments provided by caller *)
                    (k: cont), (* what to do next *)
             state
         | Returnstate:(* Return from a function *)
             forall (v: val)(* Return value *)
                    (k: cont), (* what to do next *)
             state

      Inductive eval_expr: expr -> val -> Prop :=
         | eval_Evar: forall id v,
             le!id = Some v ->
             eval_expr (Evar id) v
         | eval_Eaddrof: forall id b,
             eval_var_addr e id b ->
             eval_expr (Eaddrof id) (Vptr b Ptrofs.zero)
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
                                                            
      Inductive step: state -> trace -> state -> Prop :=
        | step_skip_seq: forall f s k e le m,
            step (State f Sskip (Kseq s k) e le m)
              E0 (State f s k e le m)
        | step_skip_block: forall f k e le m,
            step (State f Sskip (Kblock k) e le m)
              E0 (State f Sskip k e le m)         
        | step_set: forall f id a k e le m v,
            eval_expr e le m a v ->
            step (State f (Sset id a) k e le m)
              E0 (State f Sskip k e (PTree.set id v le) m)                
       | step_seq: forall f s1 s2 k e le m,
           step (State f (Sseq s1 s2) k e le m)
             E0 (State f s1 (Kseq s2 k) e le m)
     
       | step_ifthenelse: forall f a s1 s2 k e le m v b,
           eval_expr e le m a v ->
           Val.bool_of_val v b ->
           step (State f (Sifthenelse a s1 s2) k e le m)
             E0 (State f (if b then s1 else s2) k e le m)
     
       | step_loop: forall f s k e le m,
           step (State f (Sloop s) k e le m)
             E0 (State f s (Kseq (Sloop s) k) e le m)
     
       | step_block: forall f s k e le m,
           step (State f (Sblock s) k e le m)
             E0 (State f s (Kblock k) e le m)
     
       | step_exit_seq: forall f n s k e le m,
           step (State f (Sexit n) (Kseq s k) e le m)
             E0 (State f (Sexit n) k e le m)
       | step_exit_block_0: forall f k e le m,
           step (State f (Sexit O) (Kblock k) e le m)
             E0 (State f Sskip k e le m)
       | step_exit_block_S: forall f n k e le m,
           step (State f (Sexit (S n)) (Kblock k) e le m)
             E0 (State f (Sexit n) k e le m)

       | step_switch: forall f islong a cases k e le m v n,
           eval_expr e le m a v ->
           switch_argument islong v n ->
           step (State f (Sswitch islong a cases) k e le m)
             E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m)
     
       | step_return_0: forall f k e le m m',
           Mem.free_list m (blocks_of_env e) = Some m' ->
           step (State f (Sreturn None) k e le m)
             E0 (Returnstate Vundef (call_cont k) m')
       | step_return_1: forall f a k e le m v m',
           eval_expr e le m a v ->
           Mem.free_list m (blocks_of_env e) = Some m' ->
           step (State f (Sreturn (Some a)) k e le m)
             E0 (Returnstate v (call_cont k) m')
       | step_label: forall f lbl s k e le m,
           step (State f (Slabel lbl s) k e le m)
             E0 (State f s k e le m)
     
       | step_goto: forall f lbl k e le m s' k',
           find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
           step (State f (Sgoto lbl) k e le m)
             E0 (State f s' k' e le m)     
       | step_return: forall v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (Cminor.set_optvar optid v le) m).      

      
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

(* Translation from Imp -> Impsharpminor *)
family Impzero.Impshmgen extends ImpfrontendTransform {
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



