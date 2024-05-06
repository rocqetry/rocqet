(* Implight IR *)
family Impzero.Implight extends SourceLanguage {
    Inductive expression : Type :=
      | Econst_int: int -> type -> expression(* integer literal *)
      | Econst_float: float -> type -> expression(* double float literal *)
      | Econst_single: float32 -> type -> expression(* single float literal *)
      | Econst_long: int64 -> type -> expression(* long integer literal *)
      | Evar: ident -> type -> expression(* variable *)
      | Etempvar: ident -> type -> expression(* temporary variable *)      
      | Eunop: unary_operation -> expression -> type -> expression(* unary operation *)      
      
  Inductive statement : Type :=
     | Sskip : statement(* do nothing *)     
     | Sset : ident -> expression -> statement(* assignment tempvar = rvalue *)
     | Scall: option ident -> expression -> list expression -> statement(* function call *)     
     | Ssequence : statement -> statement -> statement(* sequence *)
     | Sifthenelse : expression -> statement -> statement -> statement(* conditional *)
     | Sloop: statement -> statement -> statement(* infinite loop *)
     | Sbreak : statement(* break statement *)
     | Scontinue : statement(* continue statement *)
     | Sreturn : option expression -> statement(* return statement *)
     | Sswitch : expression -> labeled_statements -> statement(* switch statement *)
     | Slabel : label -> statement -> statement
     | Sgoto : label -> statement

   with labeled_statements : Type := (* cases of a switch *)
     | LSnil: labeled_statements
     | LScons: option Z -> statement -> labeled_statements -> labeled_statements.

  family Semantics {
      Inductive cont: Type :=
        | Kstop: cont
        | Kseq: statement -> cont -> cont(* Kseq s2 k = after s1 in s1;s2 *)
        | Kloop1: statement -> statement -> cont -> cont(* Kloop1 s1 s2 k = after s1 in Sloop s1 s2 *)
        | Kloop2: statement -> statement -> cont -> cont(* Kloop2 s1 s2 k = after s2 in Sloop s1 s2 *)
        | Kswitch: cont -> cont(* catches break statements arising out of switch *)
        | Kcall: option ident ->(* where to store result *)
                 function ->(* calling function *)
                 env ->(* local env of calling function *)
                 temp_env ->(* temporary env of calling function *)
                 cont -> cont.

       Inductive eval_expr: expr -> val -> Prop :=
           | eval_Econst_int: forall i ty,
               eval_expr (Econst_int i ty) (Vint i)
           | eval_Econst_float: forall f ty,
               eval_expr (Econst_float f ty) (Vfloat f)
           | eval_Econst_single: forall f ty,
               eval_expr (Econst_single f ty) (Vsingle f)
           | eval_Econst_long: forall i ty,
               eval_expr (Econst_long i ty) (Vlong i)
           | eval_Etempvar: forall id ty v,
               le!id = Some v ->
               eval_expr (Etempvar id ty) v
           | eval_Eaddrof: forall a ty loc ofs,
               eval_lvalue a loc ofs Full ->
               eval_expr (Eaddrof a ty) (Vptr loc ofs)
           | eval_Eunop: forall op a ty v1 v,
               eval_expr a v1 ->
               sem_unary_operation op v1 (typeof a) m = Some v ->
               eval_expr (Eunop op a ty) v
           | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
               eval_expr a1 v1 ->
               eval_expr a2 v2 ->
               sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
               eval_expr (Ebinop op a1 a2 ty) v
       
       Inductive state: Type :=
          | State
              (f: function)
              (s: statement)
              (k: cont)
              (e: env)
              (le: temp_env) : state
          | Callstate
              (fd: fundef)
              (args: list val)
              (k: cont) : state
          | Returnstate
              (res: val)
              (k: cont) : state.

      Inductive step: state -> trace -> state -> Prop :=
         | step_assign: forall f a1 a2 k e le m loc ofs bf v2 v m',
             eval_lvalue e le m a1 loc ofs bf ->
             eval_expr e le m a2 v2 ->
             sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
             assign_loc ge (typeof a1) m loc ofs bf v m' ->
             step (State f (Sassign a1 a2) k e le m)
               E0 (State f Sskip k e le m')
       
         | step_set: forall f id a k e le m v,
             eval_expr e le m a v ->
             step (State f (Sset id a) k e le m)
               E0 (State f Sskip k e (PTree.set id v le) m)
         | step_seq: forall f s1 s2 k e le m,
             step (State f (Ssequence s1 s2) k e le m)
               E0 (State f s1 (Kseq s2 k) e le m)
         | step_skip_seq: forall f s k e le m,
             step (State f Sskip (Kseq s k) e le m)
               E0 (State f s k e le m)
         | step_continue_seq: forall f s k e le m,
             step (State f Scontinue (Kseq s k) e le m)
               E0 (State f Scontinue k e le m)
         | step_break_seq: forall f s k e le m,
             step (State f Sbreak (Kseq s k) e le m)
               E0 (State f Sbreak k e le m)
       
         | step_ifthenelse: forall f a s1 s2 k e le m v1 b,
             eval_expr e le m a v1 ->
             bool_val v1 (typeof a) m = Some b ->
             step (State f (Sifthenelse a s1 s2) k e le m)
               E0 (State f (if b then s1 else s2) k e le m)
       
         | step_loop: forall f s1 s2 k e le m,
             step (State f (Sloop s1 s2) k e le m)
               E0 (State f s1 (Kloop1 s1 s2 k) e le m)
         | step_skip_or_continue_loop1: forall f s1 s2 k e le m x,
             x = Sskip \/ x = Scontinue ->
             step (State f x (Kloop1 s1 s2 k) e le m)
               E0 (State f s2 (Kloop2 s1 s2 k) e le m)
         | step_break_loop1: forall f s1 s2 k e le m,
             step (State f Sbreak (Kloop1 s1 s2 k) e le m)
               E0 (State f Sskip k e le m)
         | step_skip_loop2: forall f s1 s2 k e le m,
             step (State f Sskip (Kloop2 s1 s2 k) e le m)
               E0 (State f (Sloop s1 s2) k e le m)
         | step_break_loop2: forall f s1 s2 k e le m,
             step (State f Sbreak (Kloop2 s1 s2 k) e le m)
               E0 (State f Sskip k e le m)
       
         | step_return_0: forall f k e le m m',
             Mem.free_list m (blocks_of_env e) = Some m' ->
             step (State f (Sreturn None) k e le m)
               E0 (Returnstate Vundef (call_cont k) m')
         | step_return_1: forall f a k e le m v v' m',
             eval_expr e le m a v ->
             sem_cast v (typeof a) f.(fn_return) m = Some v' ->
             Mem.free_list m (blocks_of_env e) = Some m' ->
             step (State f (Sreturn (Some a)) k e le m)
               E0 (Returnstate v' (call_cont k) m')
         | step_skip_call: forall f k e le m m',
             is_call_cont k ->
             Mem.free_list m (blocks_of_env e) = Some m' ->
             step (State f Sskip k e le m)
               E0 (Returnstate Vundef k m')
       
         | step_switch: forall f a sl k e le m v n,
             eval_expr e le m a v ->
             sem_switch_arg v (typeof a) = Some n ->
             step (State f (Sswitch a sl) k e le m)
               E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
         | step_skip_break_switch: forall f x k e le m,
             x = Sskip \/ x = Sbreak ->
             step (State f x (Kswitch k) e le m)
               E0 (State f Sskip k e le m)
         | step_continue_switch: forall f k e le m,
             step (State f Scontinue (Kswitch k) e le m)
               E0 (State f Scontinue k e le m)
       
         | step_label: forall f lbl s k e le m,
             step (State f (Slabel lbl s) k e le m)
               E0 (State f s k e le m)
       
         | step_goto: forall f lbl k e le m s' k',
             find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
             step (State f (Sgoto lbl) k e le m)
               E0 (State f s' k' e le m)

         | step_returnstate: forall v optid f e le k m,
             step (Returnstate v (Kcall optid f e le k) m)
               E0 (State f Sskip k e (set_opttemp optid v le) m).

      
       Inductive initial_state (p: program): state -> Prop :=
         | initial_state_intro: forall b f m0,
             let ge := Genv.globalenv p in
             Genv.init_mem p = Some m0 ->
             Genv.find_symbol ge p.(prog_main) = Some b ->
             Genv.find_funct_ptr ge b = Some f ->
             type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
             initial_state p (Callstate f nil Kstop m0).

      Inductive final_state: state -> int -> Prop :=
         | final_state_intro: forall r m,
             final_state (Returnstate (Vint r) Kstop m) r.
       
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
