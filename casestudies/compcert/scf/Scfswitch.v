
Family Scfswitch extends Scfloop.
    Family C.
      FInductive statement : Type := 
         | Sswitch : expr -> labeled_statements -> statement
      with labeled_statements : Type := (* cases of a switch *)
         | LSnil: labeled_statements
         | LScons: option Z -> statement -> labeled_statements -> labeled_statements.

      FInductive cont: Type :=
         | Kswitch1: labeled_statements -> cont -> cont(* Kswitch1 ls k = after e in switch(e) { ls } *)
         | Kswitch2: cont -> cont(* catches break statements arising out of switch *)
      
      FInductive estep: state -> trace -> state -> Prop :=
         | step_switch: forall f x sl k e m,
            sstep (State f (Sswitch x sl) k e m)
               E0 (ExprState f x (Kswitch1 sl k) e m)
         | step_expr_switch: forall f ty sl k e m v n,
             sem_switch_arg v ty = Some n ->
             sstep (ExprState f (Eval v ty) (Kswitch1 sl k) e m)
                E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m).
   FEnd C.

   Family Clight.
      FInductive statement : Type :=
         | Sswitch : expr -> labeled_statements -> statement
      with labeled_statements : Type :=(* cases of a switch *)
         | LSnil: labeled_statements
         | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
      
      FInductive step: state -> trace -> state -> Prop :=
         | step_switch: forall f a sl k e le m v n,
             eval_expr e le m a v ->
             sem_switch_arg v (typeof a) = Some n ->
             step (State f (Sswitch a sl) k e le m)
               E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m).
   FEnd Clight.
   
   Family Csharpminor.
      FInductive stmt : Type :=
        | Sswitch: bool -> expr -> lbl_stmt -> stmt
      with lbl_stmt : Type :=
        | LSnil: lbl_stmt
        | LScons: option Z -> stmt -> lbl_stmt -> lbl_stmt.
      
      FInductive step: state -> trace -> state -> Prop :=
        | step_switch: forall f islong a cases k e le m v n,
            eval_expr e le m a v ->
            switch_argument islong v n ->
            step (State f (Sswitch islong a cases) k e le m)
              E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m).
   FEnd Csharpminor.
   
   Family Cminor. 
       FInductive stmt : Type := 
         | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt.

       FInductive step: state -> trace -> state -> Prop :=
         | step_switch: forall f islong a cases default k sp e m v n,
             eval_expr sp e m a v ->
             switch_argument islong v n ->
             step (State f (Sswitch islong a cases default) k sp e m)
               E0 (State f (Sexit (switch_target n default cases)) k sp e m)
   FEnd Cminor.

   Family Asm.
      FInductive instruction : Type :=
         | Pbtbl : ireg -> list lable -> instruction. (**r N-way branch through a jump table *)
      
      FRecursion exec_instr.
         Case Pbtbl := (fun r tbl ge f rs m =>
             match rs r with
             | Vint n =>
                 match list_nth_z tbl (Int.unsigned n) with
                 | None => Stuck
                 | Some lbl => goto_label f lbl (rs#X5 <- Vundef #X31 <- Vundef) m
                 end
             | _ => Stuck
             end).
      FEnd exec_instr.
   FEnd Asm.

   Family CminorSel.              
       Inductive exitexpr : Type :=
          | XEexit: nat -> exitexpr
          | XEjumptable: expr -> list nat -> exitexpr
          | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
          | XElet: expr -> exitexpr -> exitexpr.

       FInductive stmt : Type :=
         | Sswitch: exitexpr -> stmt.
       
       FInductive step: state -> trace -> state -> Prop :=
         | step_switch: forall f a k sp e m n,
            eval_exitexpr sp e m nil a n ->
            step (State f (Sswitch a) k sp e m)
              E0 (State f (Sexit n) k sp e m)
   FEnd CminorSel.
  
  
   Family SimplCswitch. 
   FEnd SimplCswitch.

   Family SimplCshmsiwtch. 
   FEnd SimplCshmsiwtch.   

   Family Selectswitch. 
   FEnd Selectswitch.

   Family LTL. 
      FInductive instruction: Type :=
        | Ljumptable : mreg -> list node -> instruction.

      FInductive step: state -> trace -> state -> Prop :=
         | exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs',
            rs (R arg) = Vint n ->
            list_nth_z tbl (Int.unsigned n) = Some pc ->
            rs' = undef_regs (destroyed_by_jumptable) rs ->
            step (Block s f sp (Ljumptable arg tbl :: bb) rs m)
              E0 (State s f sp pc rs' m).      
   FEnd LTL.
   
   Family Lfam.
       FInductive instruction: Type :=
         | Ljumptable: mreg -> list label -> instruction. 

       FInductive step: state -> trace -> state -> Prop :=
         | exec_Ljumptable:
           forall s fb f sp arg tbl c rs m n lbl c' rs',
           rs arg = Vint n ->
           list_nth_z tbl (Int.unsigned n) = Some lbl ->
           Genv.find_funct_ptr ge fb = Some (Internal f) ->
           find_label lbl f.(fn_code) = Some c' ->
           rs' = undef_regs destroyed_by_jumptable rs ->
           step (State s fb sp (Ljumptable arg tbl :: c) rs m)
             E0 (State s fb sp c' rs' m).
   FEnd Lfam.
FEnd Scfswitch.
