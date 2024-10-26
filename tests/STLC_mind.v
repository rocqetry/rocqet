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

FRecursion tm_size about tm motive (fun (_ : tm) => nat) by _rec.
Case tm_var := cheat.
Case tm_app := cheat.
Case tm_val := cheat.
FEnd tm_size.

FRecursion val_size about val motive (fun (_ : val) => nat) by _rec.
Case val_abs := cheat.
Case val_unit := cheat.
FEnd val_size.

FRecursion comb_size_tm about tm motive (fun (_ : tm) => nat)
  with comb_size_val about val motive (fun (_ : val) => nat) by _rect.
Case tm_var := cheat.
Case tm_app := cheat.
Case tm_val := cheat.

Case val_abs := cheat.
Case val_unit := cheat.
FEnd comb_size_tm
with comb_size_val.

FEnd STLC.

(*
  Scheme __internal_tm_tm_val_rect := Induction for __internal_tm 
  Sort Type
  with __internal_val_tm_val_rect := Induction for __internal_val 
  Sort Type.

  Combined Scheme __internal_tm_val_rect from
  __internal_tm_tm_val_rect
  , __internal_val_tm_val_rect.

*)

Check STLC.tm_val_rect.
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


Family STLC_bool extends STLC.  
FInductive tm : Set :=
| tm_if : tm -> tm -> tm -> tm
with val : Set :=
| val_true : val
| val_false : val.  

FRecursion tm_size.
Case tm_if := cheat.
FEnd tm_size.

FRecursion val_size.
Case val_true := cheat.
Case val_false := cheat.
FEnd val_size.

FRecursion comb_size_tm
     with comb_size_val.
Case tm_if := cheat.

Case val_true := cheat.
Case val_false := cheat.
FEnd comb_size_tm
with comb_size_val.

FEnd STLC_bool.


Family STLC_prod extends STLC_bool.
FInductive tm : Set :=
| tm_prod : tm -> tm -> tm
| tm_pi1 : tm -> tm
| tm_pi2 : tm -> tm
with val : Set :=
| val_prod : val -> val -> val.

FRecursion tm_size.
Case tm_prod := cheat.
Case tm_pi1 := cheat.
Case tm_pi2 := cheat.
FEnd tm_size.

FRecursion val_size.
Case val_prod := cheat.
FEnd val_size.

FRecursion comb_size_tm
  with comb_size_val.
Case tm_prod := cheat.
Case tm_pi1 := cheat.
Case tm_pi2 := cheat.

Case val_prod := cheat.
FEnd comb_size_tm
with comb_size_val.

FEnd STLC_prod.

Family all extends STLC, STLC_bool, STLC_prod.
FEnd all.
