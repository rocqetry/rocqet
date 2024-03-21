(* Imp source language *)
family Impzero.Imp {
    Inductive expression : Type :=
      | Var : ident -> expression
      | Lit : nat -> expression 
      | Plus : expression -> expression -> expression
      | Minus : expression -> expression -> expression
      | Mult : expression -> expression -> expression

    Inductive statement : Type :=
      | Assign (x : ident) (e : expression)       (* x = e *)
      | Seq    (a b : statement)                  (* a ; b *)
      | If     (i : expression) (t e : statement) (* if (i) then { t } else { e } *)      
      | Skip                                      (* ; *)
    
    family Semantics {            
      Inductive cont : Type :=
        | Kstop : cont
        | Kseq : statement -> cont -> cont        

      Inductive step : state -> state -> Prop = 
         | KS_Ass : forall st i a k n,            (**r Computation for assignments *)
             aeval st a = n ->
             kstep (<{ i := a }>, k, st) (CSkip, k, t_update st i n)
        | KS_Seq : forall st c1 c2 k,  (**r Focusing on the left part of a sequence *)
             kstep (<{ c1 ; c2 }>, k, st) (c1, Kseq c2 k, st)
        | KS_IfTrue : forall st b c1 c2 k,  (**r Computation for conditionals *)
             beval st b = true ->
             kstep (<{ if b then c1 else c2 end }>, k, st) (c1, k, st)
        | KS_IfFalse : forall st b c1 c2 k,
             beval st b = false ->
             kstep (<{ if b then c1 else c2 end }>, k, st) (c2, k, st)
        | KS_SkipSeq: forall c k st,  (**r Resumption on [SKIP] *)
            kstep (CSkip, Kseq c k, st) (c, k, st)
        
     }

    Inductive program := ...
}
