From NFPOP Require Import Loader.

Notation ident := nat.

Family STLC.
  FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.

  Family ty_size_cases_handler.
    FDefinition motive : self__STLC.ty -> Set := fun _ => nat.
    FDefinition ty_unit :
      self__ty_size_cases_handler.motive self__STLC.ty_unit
      := 1.
    FDefinition ty_arrow :
      forall A B, self__ty_size_cases_handler.motive A ->
      self__ty_size_cases_handler.motive B ->
      self__ty_size_cases_handler.motive (self__STLC.ty_arrow A B)
      := fun _ _ n m => n + m.
  FEnd ty_size_cases_handler.

  (* FRecursor ty_size_cases about ty
    motive ty_size_cases_handler.motive
    using ty_size_cases_handler
    by _rec. *)

  FInductive tm : Set :=
  | tm_var : ident -> tm
  | tm_app : tm -> tm -> tm
  | tm_val : val -> tm
  with val : Set :=
  | val_abs : ident -> tm -> val
  | val_unit: val.
FEnd STLC.

Family STLC_bool extends STLC.
  FInductive ty : Set :=
    | ty_bool : ty.

  FInductive tm : Set :=
    | tm_if : tm -> tm -> tm -> tm
  with val : Set :=
    | val_true : val
    | val_false : val.
FEnd STLC_bool.

Family STLC_prod extends STLC_bool.
  FInductive ty : Set :=
    | ty_prod : ty -> ty -> ty.

  FInductive tm : Set :=
    | tm_prod : tm -> tm -> tm
    | tm_pi1 : tm -> tm
    | tm_pi2 : tm -> tm
  with val : Set :=
    | val_prod : val -> val -> val.
FEnd STLC_prod.
