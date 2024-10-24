From NFPOP Require Import Loader.

Definition ident := nat.

Axiom cheat : forall {X}, X.

Family STLC.    
FInductive tm : Set :=
| tm_var : ident -> tm
| tm_app : tm -> tm -> tm
| tm_val : val -> tm
with val : Set :=
| val_abs : ident -> tm -> val
| val_unit: val.

(*
  Scheme __internal_tm_tm_val_rect := Induction for __internal_tm 
  Sort Type
  with __internal_val_tm_val_rect := Induction for __internal_val 
  Sort Type.

  Combined Scheme __internal_tm_val_rect from
  __internal_tm_tm_val_rect
  , __internal_val_tm_val_rect.

*)
FEnd STLC.

Check STLC.__internal_tm_tm_val_rect.
(* STLC.__internal_tm_tm_val_rect
     : forall (P : STLC.__internal_tm -> Type) (P0 : STLC.__internal_val -> Type),
       (forall i : ident, P (STLC.__internal_tm_var i)) ->
       (forall __i : STLC.__internal_tm,
        P __i -> forall __i0 : STLC.__internal_tm, P __i0 -> P (STLC.__internal_tm_app __i __i0)) ->
       (forall __i : STLC.__internal_val, P0 __i -> P (STLC.__internal_tm_val __i)) ->
       (forall (i : ident) (__i : STLC.__internal_tm), P __i -> P0 (STLC.__internal_val_abs i __i)) ->
       P0 STLC.__internal_val_unit -> forall __i : STLC.__internal_tm, P __i *)
Check STLC.__internal_val_tm_val_rect.
(* STLC.__internal_val_tm_val_rect
     : forall (P : STLC.__internal_tm -> Type) (P0 : STLC.__internal_val -> Type),
       (forall i : ident, P (STLC.__internal_tm_var i)) ->
       (forall __i : STLC.__internal_tm,
        P __i -> forall __i0 : STLC.__internal_tm, P __i0 -> P (STLC.__internal_tm_app __i __i0)) ->
       (forall __i : STLC.__internal_val, P0 __i -> P (STLC.__internal_tm_val __i)) ->
       (forall (i : ident) (__i : STLC.__internal_tm), P __i -> P0 (STLC.__internal_val_abs i __i)) ->
       P0 STLC.__internal_val_unit -> forall __i : STLC.__internal_val, P0 __i *)
Check STLC.__internal_tm_val_rect.
(* STLC.__internal_tm_val_rect
     : forall (P : STLC.__internal_tm -> Type) (P0 : STLC.__internal_val -> Type),
       (forall i : ident, P (STLC.__internal_tm_var i)) ->
       (forall __i : STLC.__internal_tm,
        P __i -> forall __i0 : STLC.__internal_tm, P __i0 -> P (STLC.__internal_tm_app __i __i0)) ->
       (forall __i : STLC.__internal_val, P0 __i -> P (STLC.__internal_tm_val __i)) ->
       (forall (i : ident) (__i : STLC.__internal_tm), P __i -> P0 (STLC.__internal_val_abs i __i)) ->
       P0 STLC.__internal_val_unit ->
       (forall __i : STLC.__internal_tm, P __i) * (forall __i : STLC.__internal_val, P0 __i) *)



(*Print STLC.*)

(*Family STLC_bool extends STLC.  
FInductive tm : Set :=
| tm_if : tm -> tm -> tm -> tm
with val : Set :=
| val_true : val
| val_false : val.  
FEnd STLC_bool.

Family STLC_prod extends STLC_bool.
FInductive tm : Set :=
| tm_prod : tm -> tm -> tm
| tm_pi1 : tm -> tm
| tm_pi2 : tm -> tm
with val : Set :=
| val_prod : val -> val -> val.
FEnd STLC_prod.

Family all extends STLC, STLC_bool, STLC_prod.
FEnd all.
*)
