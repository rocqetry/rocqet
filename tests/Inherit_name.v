From NFPOP Require Import Loader.

Definition ident := nat.

Family STLC.
  Family X.
    FInductive ty : Set :=     
     | ty_arrow : ty -> ty -> ty.
  FEnd X.
         
  FRecursion subst : (t : X.ty) -> (k : nat) -> nat.  
     Case ty_arrow n m := (subst m k + subst n k).     
  FEnd subst.    
FEnd STLC.

Family Y extends STLC.   
   Family X.   
     Inherit ty.

     FDefinition alias := ty_arrow.
   FEnd X.
FEnd Y.
