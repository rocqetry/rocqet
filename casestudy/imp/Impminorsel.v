family Impzero.ImpMinorSel extends MinorLanguage {         
  Inductive expression : Type :=
    | Evar : ident -> expression
    | Eop : operation -> exprlist -> expression    
    | Econdition : condexpr -> expression -> expression -> expression
    | Elet : expression -> expression -> expression
    | Eletvar : nat -> expression    

  with exprlist : Type :=
   | Enil: exprlist
   | Econs: expression -> exprlist -> exprlist
                                 
  with condexpr : Type :=
    | CEcond : Asm.Op.condition -> exprlist -> condexpr
    | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
    | CElet: expression -> condexpr -> condexpr

  Inductive exitexpr : Type :=
     | XEexit: nat -> exitexpr
     | XEjumptable: expression -> list nat -> exitexpr
     | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
     | XElet: expression -> exitexpr -> exitexpr

  
  Inductive statement : Type :=
     | Sskip: statement
     | Sassign : ident -> expression -> statement
     | Sstore : memory_chunk -> addressing -> exprlist -> expression -> statement
     | Scall : option ident -> signature -> expression + ident -> exprlist -> statement
     | Stailcall: signature -> expression + ident -> exprlist -> statement
     | Sbuiltin : builtin_res ident -> external_function -> list (builtin_arg expression) -> statement
     | Sseq: statement -> statement -> statement
     | Sifthenelse: condexpr -> statement -> statement -> statement
     | Sloop: statement -> statement
     | Sblock: statement -> statement
     | Sexit: nat -> statement
     | Sswitch: exitexpr -> statement
     | Sreturn: option expression -> statement
     | Slabel: label -> statement -> statement
     | Sgoto: label -> statement.
  
                              
  family Semantics {
    Inductive cont: Type :=
       | Kstop: cont (* stop program execution *)
       | Kseq: stmt -> cont -> cont (* execute stmt, then cont *)
       | Kblock: cont -> cont (* exit a block, then do cont *)
       | Kcall: option ident -> function -> val -> env -> cont -> cont.

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
    

    Inductive eval_expr: letenv -> expr -> val -> Prop :=
       | eval_Evar: forall le id v,
           PTree.get id e = Some v ->
           eval_expr le (Evar id) v
       | eval_Eop: forall le op al vl v,
           eval_exprlist le al vl ->
           eval_operation ge sp op vl m = Some v ->
           eval_expr le (Eop op al) v
       | eval_Eload: forall le chunk addr al vl vaddr v,
           eval_exprlist le al vl ->
           eval_addressing ge sp addr vl = Some vaddr ->
           Mem.loadv chunk m vaddr = Some v ->
           eval_expr le (Eload chunk addr al) v
       | eval_Econdition: forall le a b c va v,
           eval_condexpr le a va ->
           eval_expr le (if va then b else c) v ->
           eval_expr le (Econdition a b c) v
       | eval_Elet: forall le a b v1 v2,
           eval_expr le a v1 ->
           eval_expr (v1 :: le) b v2 ->
           eval_expr le (Elet a b) v2
       | eval_Eletvar: forall le n v,
           nth_error le n = Some v ->
           eval_expr le (Eletvar n) v
       | eval_Ebuiltin: forall le ef al vl v,
           eval_exprlist le al vl ->
           external_call ef ge vl m E0 v m ->
           eval_expr le (Ebuiltin ef al) v
       | eval_Eexternal: forall le id sg al b ef vl v,
           Genv.find_symbol ge id = Some b ->
           Genv.find_funct_ptr ge b = Some (External ef) ->
           ef_sig ef = sg ->
           eval_exprlist le al vl ->
           external_call ef ge vl m E0 v m ->
           eval_expr le (Eexternal id sg al) v

      with eval_exprlist: letenv -> exprlist -> list val -> Prop :=
        | eval_Enil: forall le,
            eval_exprlist le Enil nil
        | eval_Econs: forall le a1 al v1 vl,
            eval_expr le a1 v1 -> eval_exprlist le al vl ->
            eval_exprlist le (Econs a1 al) (v1 :: vl)
      
      with eval_condexpr: letenv -> condexpr -> bool -> Prop :=
        | eval_CEcond: forall le cond al vl vb,
            eval_exprlist le al vl ->
            eval_condition cond vl m = Some vb ->
            eval_condexpr le (CEcond cond al) vb
        | eval_CEcondition: forall le a b c va v,
            eval_condexpr le a va ->
            eval_condexpr le (if va then b else c) v ->
            eval_condexpr le (CEcondition a b c) v
        | eval_CElet: forall le a b v1 v2,
            eval_expr le a v1 ->
            eval_condexpr (v1 :: le) b v2 ->
            eval_condexpr le (CElet a b) v2.

   Inductive eval_exitexpr: letenv -> exitexpr -> nat -> Prop :=
      | eval_XEexit: forall le x,
          eval_exitexpr le (XEexit x) x
      | eval_XEjumptable: forall le a tbl n x,
          eval_expr le a (Vint n) ->
          list_nth_z tbl (Int.unsigned n) = Some x ->
          eval_exitexpr le (XEjumptable a tbl) x
      | eval_XEcondition: forall le a b c va x,
          eval_condexpr le a va ->
          eval_exitexpr le (if va then b else c) x ->
          eval_exitexpr le (XEcondition a b c) x
      | eval_XElet: forall le a b v x,
          eval_expr le a v ->
          eval_exitexpr (v :: le) b x ->
          eval_exitexpr le (XElet a b) x.
      
     Inductive step: state -> trace -> state -> Prop :=
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
           eval_expr sp e m nil a v ->
           step (State f (Sassign id a) k sp e m)
             E0 (State f Sskip k sp (PTree.set id v e) m)          
       | step_seq: forall f s1 s2 k sp e m,
           step (State f (Sseq s1 s2) k sp e m)
             E0 (State f s1 (Kseq s2 k) sp e m)
     
       | step_ifthenelse: forall f c s1 s2 k sp e m b,
           eval_condexpr sp e m nil c b ->
           step (State f (Sifthenelse c s1 s2) k sp e m)
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
     
       | step_switch: forall f a k sp e m n,
           eval_exitexpr sp e m nil a n ->
           step (State f (Sswitch a) k sp e m)
             E0 (State f (Sexit n) k sp e m)
     
       | step_return_0: forall f k sp e m m',
           Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
           step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
             E0 (Returnstate Vundef (call_cont k) m')
       | step_return_1: forall f a k sp e m v m',
           eval_expr (Vptr sp Ptrofs.zero) e m nil a v ->
           Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
           step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
             E0 (Returnstate v (call_cont k) m')

        | step_label: forall f lbl s k sp e m,
            step (State f (Slabel lbl s) k sp e m)
              E0 (State f s k sp e m)
      
        | step_goto: forall f lbl k sp e m s' k',
            find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
            step (State f (Sgoto lbl) k sp e m)
              E0 (State f s' k' sp e m)
               
        | step_return: forall v optid f sp e k m,
            step (Returnstate v (Kcall optid f sp e k) m)
              E0 (State f Sskip k sp (set_optvar optid v e) m).

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

(* Instruction Selection *)
(* Translation from Impminor -> ImpminorSel *)
family Impzero.ImpSelection extends ImpfrontendTransform {
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
