From NFPOP Require Import Loader.

Family X.

Family STLC.  
FInductive ty : Set :=     
| ty_unit : ty
| ty_arrow : ty -> ty -> ty.  
         
  FRecursion subst about ty motive (fun (_: ty) => nat -> nat) by _rect.  
     Case ty_unit := (fun _ => 0).
     Case _ := (fun _ => 0).
  FEnd subst.  

  FRecursion subst2 about ty motive (fun (_: ty) => nat -> nat) by _rect.       
     Case _ := (fun _ => 0).
  FEnd subst2.

FEnd STLC.

Family STLC_bool extends STLC.  
    FInductive ty : Set :=
      | ty_bool : ty.    

  FRecursion subst.
      Case ty_bool := (fun k => 1).
      Case _ := (fun k => 1).
  FEnd subst.

  FRecursion subst2.      
      Case _ := (fun k => 1).
  FEnd subst2.
FEnd STLC_bool.

FEnd X.
