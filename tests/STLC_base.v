Require Import Rocqet.Loader.

Definition ident := nat.

Axiom cheat : forall {X}, X.

Family STLC.
  Family X.
    FInductive ty : Set :=     
      | ty_arrow : ty -> ty -> ty
      | ty_unit : ty.
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
