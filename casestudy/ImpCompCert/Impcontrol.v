(* Imp with control flow statements *)
family Impcontrol extends Impzero { }

family Impcontrol.Imp {
  Inductive statement += 
     | While  (t : expression) (b : statement)   (* while (t) { b } *)

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

family Imploop.Impfrontend { 
    Inductive statement : Type +=
       | Sloop: statement -> statement -> statement (**r infinite loop *)                               
}

family Imploop.Impbackend { }

family Impgoto extends Impzero { }
family Impgoto.Imp {
  Inductive statement += 
      | Label : label -> statement -> statement
      | Goto : label -> statement
}
