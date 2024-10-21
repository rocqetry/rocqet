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
         
  FRecursion subst : (t : X.ty) -> (k : nat) -> nat.  
     Case ty_arrow n m := (subst m k + subst n k).
     Case ty_unit := k.
  FEnd subst.  
  
  FInduction subst_size
       about X.ty
       motive (fun (t : X.ty) => subst t 0 = 1).
     FProof.  
     - apply cheat.
     - intros. apply cheat.
     Qed.
  FEnd subst_size.  
  
  (*FInductive tm : Set :=
  | tm_var : self__STLC.ident -> tm
  | tm_app : tm -> tm -> tm
  | tm_val : val -> tm
  with val : Set :=
  | val_abs : self__STLC.ident -> tm -> val
  | val_unit: val. *)
FEnd STLC.

Family STLC_bool extends STLC.
  Family X.
    FInductive ty : Set :=
      | ty_bool : ty.          
  FEnd X.  

  FRecursion subst.
      Case ty_bool := 1.
  FEnd subst.  

  FInduction subst_size.    
    FProof.
      + apply cheat.
    Qed.
  FEnd subst_size.

(*FInductive tm : Set :=
    | tm_if : tm -> tm -> tm -> tm
  with val : Set :=
    | val_true : val
    | val_false : val.

  FDefinition check_handler_bool := subst.*)
FEnd STLC_bool.

Family STLC_prod extends STLC_bool.
  Family X.
    FInductive ty : Set :=
      | ty_prod : ty -> ty -> ty.
  FEnd X.

  FRecursion subst.  
     Case ty_prod n m := (subst m k + subst n k).
  FEnd subst.

  FInduction subst_size.     
    FProof.
    - intros. apply cheat.
    Qed.
  FEnd subst_size.

  (*FInductive tm : Set :=
    | tm_prod : tm -> tm -> tm
    | tm_pi1 : tm -> tm
    | tm_pi2 : tm -> tm
  with val : Set :=
    | val_prod : val -> val -> val.*)
FEnd STLC_prod.

Family STLC_nat. 
  Family X.
    FInductive ty : Set :=
      | ty_nat : ty.
  FEnd X.  
FEnd STLC_nat.

Family all extends STLC, STLC_bool, (*STLC_nat*) STLC_prod.
FEnd all.
