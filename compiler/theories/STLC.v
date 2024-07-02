From NFPOP Require Import Loader.

Notation ident := nat.

Family STLC.
  FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.
     
   FRecursion subst about ty motive (fun (_ : ty) => nat) by _rec.
       Case ty_unit := 1.
       Case ty_arrow := (fun _ n _ m => m + n).
   FEnd subst.

  FInductive tm : Set :=
  | tm_var : ident -> tm
  | tm_app : tm -> tm -> tm
  | tm_val : val -> tm
  with val : Set :=
  | val_abs : ident -> tm -> val
  | val_unit: val.
FEnd STLC.

(* Print STLCsubstCases回17.*)

Family STLC_bool extends STLC.
  FInductive ty : Set :=
    | ty_bool : ty.

  FRecursion subst.
      Case ty_bool := 1.
  FEnd subst.    

  FInductive tm : Set :=
    | tm_if : tm -> tm -> tm -> tm
  with val : Set :=
    | val_true : val
    | val_false : val.

  FDefinition check_handler_bool := substty_bool.
FEnd STLC_bool.

Family STLC_prod extends STLC_bool.
  FInductive ty : Set :=
    | ty_prod : ty -> ty -> ty.

  FRecursion subst.
     Case ty_prod := (fun _ n _ m => m + n).
  FEnd subst.
  
  FInductive tm : Set :=
    | tm_prod : tm -> tm -> tm
    | tm_pi1 : tm -> tm
    | tm_pi2 : tm -> tm
  with val : Set :=
    | val_prod : val -> val -> val.
FEnd STLC_prod.
