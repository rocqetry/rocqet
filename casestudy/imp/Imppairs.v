(* Imp with pairs *)
(* TODO: the eval inductive type *)
family Imppairs extends Impzero { }

family Imppairs.Impcommon {                 
  Inductive expression : Type +=
     | Epair : expr -> expr -> expr.  
}  

family Imppairs.Impcommon {
    family Semantics.Values {
        Inductive value: Type +=
          | Vpair: value -> value -> value
    }
}    

family Imppairs.Impcommon {
  family Semantics {
      
  }    
}    
