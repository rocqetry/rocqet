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
      | While  (t : expression) (b : statement)   (* while (t) { b } *)
      | Skip                                      (* ; *)
    
    family Semantics {            
      Inductive cont : Type :=
        | Kstop : cont
        | Kseq : statement -> cont -> cont
        | Kwhile : expression -> statement -> cont -> cont      

      Inductive step : state -> state -> Prop = ...                                           
    }

    Inductive program := ...
}
