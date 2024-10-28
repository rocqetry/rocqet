From NFPOP Require Import Loader.

Definition ident := nat.

Axiom cheat : forall {X}, X.

Family STLC.  
  
  Family X.
    FInductive ty : Set :=     
      | ty_arrow : ty -> ty -> ty
      | ty_unit : ty.
  FEnd X.
         
  FRecursion subst about X.ty motive (fun (_ : X.ty) => nat -> nat) by _rec.  
     Case ty_arrow n m := (fun k => subst m k + subst n k).
     Case ty_unit := (fun k => k).
  FEnd subst.  
  
  FInduction subst_size
       about X.ty
       motive (fun (t : X.ty) => subst t 0 = 0).
     FProof.  
     - intros. fsimpl in *. rewrite -> H. rewrite H0. reflexivity. 
     - intros. fsimpl in *. reflexivity. 
     Qed. FEnd subst_size.  
FEnd STLC.

Family STLC_bool extends STLC.
  
  Trait bool_mixin extends X.  
  FInductive ty : Set :=
  | ty_bool : ty.
  FEnd bool_mixin.    

  Family X extends bool_mixin.  
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
     Case ty_prod n m := (fun k => subst m k + subst n k).
  FEnd subst.

  FInduction subst_size.     
    FProof.
    - intros. apply cheat.
    Qed. FEnd subst_size.  
FEnd STLC_prod.

Family STLC_nat. 
  Family X.
    FInductive ty : Set :=
      | ty_nat : ty.
  FEnd X.  
FEnd STLC_nat.

Family all extends STLC, STLC_bool, (*STLC_nat*) STLC_prod.
FEnd all.
