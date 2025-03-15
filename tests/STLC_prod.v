Require Import STLC_base.
Require Import Rocqet.Loader.

Family STLC_prod extends STLC.
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
   Qed. FEnd subst_size.  
FEnd STLC_prod.
