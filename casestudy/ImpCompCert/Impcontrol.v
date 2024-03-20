family Impwhile extends Impzero { }

family Impwhile.Imp {
  Inductive statement += 
     | While  (t : expression) (b : statement)   (* while (t) { b } *)

  family Semantics {
    Inductive cont += 
       | Kwhile : expression -> statement -> cont -> cont
  }
}

family Impcontinue extends Impzero { }
family Impcontinue.Imp {
  Inductive statement += 
      | Continue 
}

family Impbreak extends Impzero { }
family Impbreak.Imp {
  Inductive statement += 
      | Break
}

family Impfor extends Impzero { }

family Impgoto extends Impzero { }
family Impgoto.Imp {
  Inductive statement += 
      | Label : label -> statement -> statement
      | Goto : label -> statement
}

(* Imp control is Impwhile + Impgoto + Impfor + Impcontinue + Impbreak *)
family Impcontrol extends Impzero with Impwhile, Impcontinue, Impbreak, Impfor, Impgoto { }
