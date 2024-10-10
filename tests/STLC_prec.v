From NFPOP Require Import Loader.

Definition ident := nat.

Axiom cheat : forall {X}, X.

Inductive ty : Set :=
   | ty_unit : ty
   | ty_arrow : ty -> ty -> ty.

Theorem injective : forall a b c d, ty_arrow a b = ty_arrow c d -> a = c /\ b = d.
Proof.
  intros.
  injection H. eauto.
Qed.

(*
Theorem ty_prect
     : forall (x : ty) (P : ty -> Type), option (P ty_unit) -> option (P x).
Proof.
  intros x; induction x; eauto; eauto using None.
Qed.*)

   (*(fun x : ty =>
    ty_rect
      (fun x0 : ty =>
       forall P : ty -> Type,
       option (P ty_unit) -> option (P x0))
      (fun (P : ty -> Type)
         (arg回9 : option (P ty_unit)) => arg回9) x).*)

(*Check ty_prect.
Check ty_rect.*)

(*Theorem ty_unit_eq : forall P, forall H1, ty_prect ty_unit P H1 = H1.
Proof.
  intros. 
Qed.*)

(* ty_prect
     : forall (x : ty) (P : ty -> Type), option (P ty_unit) -> option (P x) *)
(* ty_rect
     : forall P : ty -> Type, P ty_unit -> forall t : ty, P t *)


Family A.   
   FInductive ty : Set :=
     | ty_unit : ty.

FEnd A.

Family B extends A.
   FInductive ty : Set :=     
     | ty_arrow : ty -> ty -> ty.   

   (*FLemma blah : forall a b, ~ ty_unit = ty_arrow a b.
   FProofLemma.
     intros. unfold not. 
     intros.
     apply (@f_equal self__B.ty (option nat) (fun t => self__B.ty_prect_PrecSuffix回34 t (fun (_ : self__B.ty) => nat) (Some 1) (fun _ _ _ _ => Some 2))) in H.
     rewrite self__B.ty_arrow_eq_PrecSuffix回34 in H.
     rewrite self__B.ty_unit_eq_PrecSuffix回34 in H.
     discriminate.
   Qed.
   CloseFLemma.
      
   Closing Fact injective : forall a b c d, ty_arrow a b = ty_arrow c d -> a = c /\ b = d by { intros; injection H; eauto } .

   FLemma blah0 : forall a b c, ty_arrow a b = ty_arrow a c -> b = c.
   FProofLemma.
     intros.  
     apply self__B.injective in H. destruct H. apply H0.     
   Qed.
   CloseFLemma.*)
     
FEnd B.

Print B.

Family C extends B.
  FInductive ty : Set :=     
     | ty_nat : ty.   

FEnd C.

Print C.

(*Family ABC extends A using B, C.
FEnd ABC.*)

(* Print ABC. *)


Print C.

Print B.



(*
Family STLC.
  Family X extends Ix.
    FInductive ty : Set :=     
     | ty_arrow : ty -> ty -> ty.

    Prect ty.
  FEnd X.

  Test X.ty.
         
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

Family all extends STLC using STLC_bool, (*STLC_nat,*) STLC_prod.
FEnd all.
*)
