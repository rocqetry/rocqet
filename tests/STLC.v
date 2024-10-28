From NFPOP Require Import Loader.

Definition ident := nat.

Axiom cheat : forall {X}, X.

Family Ix.   
   FInductive ty : Set :=
     | ty_unit : ty.
FEnd Ix.

Family STLC.
  Family X extends Ix.
    FInductive ty : Set :=     
     | ty_arrow : ty -> ty -> ty.
  FEnd X.
         
  FRecursion subst about X.ty motive (fun (_: X.ty) => nat -> nat) by _rect.  
     Case ty_arrow := (fun _ subst_m _ subst_n k => subst_m k + subst_n k).
     Case ty_unit := (fun k => k).
  FEnd subst.  
  
  FInduction subst_size
       about X.ty
       motive (fun (t : X.ty) => subst t 0 = 1).
     FProof.  
     - apply cheat.
     - intros. apply cheat.
     Qed.
  FEnd subst_size.     
FEnd STLC.

Family STLC_bool extends STLC.
  Family X.
    FInductive ty : Set :=
      | ty_bool : ty.          
  FEnd X.  

  FRecursion subst.
      Case ty_bool := (fun k => 1).
  FEnd subst.  

  FInduction subst_size.    
    FProof.
      + apply cheat.
    Qed.
  FEnd subst_size.
FEnd STLC_bool.

Family STLC_prod extends STLC_bool.
  Family X.
    FInductive ty : Set :=
      | ty_prod : ty -> ty -> ty.
  FEnd X.

  FRecursion subst.  
     Case ty_prod := (fun _ subst_n _ subst_m k => subst_m k + subst_n k).
  FEnd subst.

  FInduction subst_size.     
    FProof.
    - intros. apply cheat.
    Qed.
  FEnd subst_size.  
FEnd STLC_prod.

Family STLC_nat. 
  Family X.
    FInductive ty : Set :=
      | ty_nat : ty.
  FEnd X.  
FEnd STLC_nat.

Family all extends STLC, STLC_bool, (*STLC_nat*) STLC_prod.
FEnd all.
