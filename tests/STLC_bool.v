Require Export STLC_base.
Require Export Rocqet.Loader.

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
  Qed. FEnd subst_size.
FEnd STLC_bool.
