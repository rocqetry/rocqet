Require Import NFPOP.Loader.

Family A.
   Family C.
     FInductive expr : Type := 
     | Eaddr : expr.
   FEnd C.
   
   Family Clight.
     FInductive expr : Type := 
     | Emem : expr.
   FEnd Clight.

   (*Family lower_addr.
     Family S extends C. FEnd S.
     Family T extends Clight. FEnd T.
     FRecursion lower about S.expr motive (fun (_ : S.expr) => T.expr) by _rect.
       Case Eaddr := T.Emem.
     FEnd lower.
   FEnd lower_addr.*)
   
   Family SimplExpr.
     Family S extends C. FEnd S.
     Family T extends Clight. FEnd T.
          
     FRecursion lower about S.expr motive (fun (_ : S.expr) => T.expr) by _rect.
       Case Eaddr := T.Emem.
     FEnd lower.
   FEnd SimplExpr.
FEnd A.

Family B extends A.
   Trait C_Esizeof extends C.
     FInductive expr : Type := 
     | Esizeof : expr.
   FEnd C_Esizeof.

   Trait C_Ealignof extends C.
     FInductive expr : Type := 
     | Ealignof : expr.
   FEnd C_Ealignof.

   Family C extends C_Esizeof, C_Ealignof.
   FEnd C.
   
   Trait Remove_Esizeof extends SimplExpr.      
     Family S extends C_Esizeof. FEnd S.
     FRecursion lower.
        Case Esizeof := T.Emem.
      FEnd lower.
   FEnd Remove_Esizeof.

   Trait Remove_Ealignof extends SimplExpr.      
     Family S extends C_Ealignof. FEnd S.
     FRecursion lower.
        Case Ealignof := T.Emem.
      FEnd lower.
   FEnd Remove_Ealignof.            
   
   Family SimplExpr extends Remove_Esizeof, Remove_Ealignof.
      Family S := C. 
      Family T := Clight. 
      
   FEnd SimplExpr.

FEnd B.


