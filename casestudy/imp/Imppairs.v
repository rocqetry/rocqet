(* Imp with pairs *)
(* TODO: the eval inductive type *)
family Imppairs extends Impzero { }

family Imppairs.Impcommon {                 
  Inductive expression : Type +=
     | Epair : expr -> expr -> expr.
  
  

}  
