Require Import Rocqet.Loader.

Definition ident := nat.

Family STLC.
FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.

FRecord lambda_arg : Type := {
    id : ident;
}.

FInductive tm : Set :=
  | tm_var : ident -> tm    
  | tm_abs : lambda_arg -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_unit: tm.

FEnd STLC.


Family SystemF extends STLC.



FEnd SystemF.
