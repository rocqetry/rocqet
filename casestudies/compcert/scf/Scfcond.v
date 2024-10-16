Family Scfcond. 
    Family C. 
       FInductive stmt : Type := 
         | Sifthenelse : expr -> stmt -> stmt -> stmt. 
    FEnd C. 

    Family Clight. 
        FInductive stmt : Type := 
         | Sifthenelse : expr -> stmt -> stmt -> stmt. 
    FEnd Clight.

    Family Csharpminor. 
       FInductive stmt : Type := 
         | Sifthenelse : expr -> stmt -> stmt -> stmt. 

        FInductive step : genv -> state -> trace -> state -> Prop :=
             | step_ifthenelse: forall f a s1 s2 k e le m v b,
                eval_expr e le m a v ->
                Val.bool_of_val v b ->
                step (State f (Sifthenelse a s1 s2) k e le m)
                    E0 (State f (if b then s1 else s2) k e le m)
    FEnd Csharpminor. 

    Family Cminor. 
        FInductive stmt : Type := 
         | Sifthenelse : expr -> stmt -> stmt -> stmt. 

        FInductive step : genv -> state -> trace -> state -> Prop :=
             | step_ifthenelse: forall f a s1 s2 k e le m v b,
                eval_expr e le m a v ->
                Val.bool_of_val v b ->
                step (State f (Sifthenelse a s1 s2) k e le m)
                    E0 (State f (if b then s1 else s2) k e le m)
    FEnd Cminor. 

    Family CminorSel. 
         FInductive expr 
         with condexpr : Type :=
          | CEcond : condition -> exprlist -> condexpr
          | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
          | CElet: expr -> condexpr -> condexpr.

         FInductive stmt : Type := 
           | Sifthenelse : condexpr -> stmt -> stmt -> stmt. 

        FInductive eval_expr
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

         FInductive step : genv -> state -> trace -> state -> Prop :=
            | step_ifthenelse: forall f c s1 s2 k sp e m b,
                eval_condexpr sp e m nil c b ->
                step (State f (Sifthenelse c s1 s2) k sp e m)
                    E0 (State f (if b then s1 else s2) k sp e m).

    FEnd CminorSel.

    Family SelectIf. 
    FEnd SelectIf.

    Family Lfam. 
       FInductive instruction: Type :=
        | Lcond: condition -> list mreg -> label -> instruction. 

       FInductive step: genv -> state -> trace -> state -> Prop :=
         | exec_Lcond_true:
            forall s f sp cond args lbl b rs m rs' b',
            eval_condition cond (reglist rs args) m = Some true ->
            rs' = undef_regs (destroyed_by_cond cond) rs ->
            find_label lbl f.(fn_code) = Some b' ->
            step (State s f sp (Lcond cond args lbl :: b) rs m)
                E0 (State s f sp b' rs' m)
        | exec_Lcond_false:
            forall s f sp cond args lbl b rs m rs',
            eval_condition cond (reglist rs args) m = Some false ->
            rs' = undef_regs (destroyed_by_cond cond) rs ->
            step (State s f sp (Lcond cond args lbl :: b) rs m)
                E0 (State s f sp b rs' m).
    FEnd Lfam. 
FEnd Scfcond.
