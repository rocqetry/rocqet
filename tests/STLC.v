From NFPOP Require Import Loader.

Family STLC.
  MetaData _ident.
    Definition ident := nat.
  FEnd _ident.

  FInductive ty : Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.
         
  FRecursion subst : (t : ty) -> (k : nat) -> nat.  
     Case ty_arrow (n, m) := (subst m k + subst n k).
     Case ty_unit := k.
  FEnd subst.

  FInductive tm : Set :=
  | tm_var : self__STLC.ident -> tm
  | tm_app : tm -> tm -> tm
  | tm_val : val -> tm
  with val : Set :=
  | val_abs : self__STLC.ident -> tm -> val
  | val_unit: val.   
FEnd STLC.

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

  FDefinition check_handler_bool := self__STLC_bool.subst.
FEnd STLC_bool.

Family STLC_prod extends STLC_bool.
  FInductive ty : Set :=
    | ty_prod : ty -> ty -> ty.

  FRecursion subst.
     Case ty_prod (n, m) := (subst m k + subst n k).
  FEnd subst.
  
  FInductive tm : Set :=
    | tm_prod : tm -> tm -> tm
    | tm_pi1 : tm -> tm
    | tm_pi2 : tm -> tm
  with val : Set :=
    | val_prod : val -> val -> val.
FEnd STLC_prod.
