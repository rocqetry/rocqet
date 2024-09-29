From NFPOP Require Import Loader.

Notation ident := nat.

Family STLC.
FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.


FInductive tm : Set :=
  | tm_var : ident -> tm    
  | tm_abs : ident -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_unit: tm.

FInductive value : tm -> Prop :=
  | vabs   : forall x body , (value (tm_abs x body))
  | vtunit : value tm_unit.

Closing Fact value_not_tm_app : 
  forall x y, ~ value (tm_app x y) by { intros x y H; inversion H; eauto }.
FEnd STLC.

Family X extends STLC.
FEnd X.

Family STLC_bool extends STLC.
  FInductive ty : Set := 
    | ty_bool : ty.

  FInductive tm : Set := 
    | tm_bool : bool -> tm.

  FInductive value : tm -> Prop :=
    | vbool : forall b, value (tm_bool b).
FEnd STLC_bool.

Check STLC_bool.value_not_tm_app.
