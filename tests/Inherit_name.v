From NFPOP Require Import Loader.

Definition ident := nat.

Family STLC.
  Family X.
    FInductive ty : Set :=     
     | ty_arrow : ty -> ty -> ty.
  FEnd X.
         
  FRecursion subst about X.ty motive (fun (_ : X.ty) => nat -> nat) by _rec.  
     Case ty_arrow n m := (fun k => subst m k + subst n k).     
  FEnd subst.
FEnd STLC.

Family Y extends STLC.   
   Family X.   
     Inherit ty.

     FDefinition alias := ty_arrow.
   FEnd X.
FEnd Y.
