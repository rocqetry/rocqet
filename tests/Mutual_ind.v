Require Import Rocqet.Loader.

Definition ident := nat.

Inductive tm : Set :=
  | tm_var : ident -> tm
  | tm_app :  tm  -> tm -> tm 
  | tm_val : val -> tm 
with val :  Set :=
  | val_abs : ident -> tm -> val
  | val_unit: val.  

Scheme tm_mut_rect := Induction for tm Sort Type
with val_mut_rect := Induction for val Sort Type.

Check tm_mut_rect.
Check tm_rect.

tm_rect
     : forall P : tm -> Type,
       (forall i : ident, P (tm_var i)) ->
       (forall t : tm, P t -> forall t0 : tm, P t0 -> P (tm_app t t0)) ->
       (forall v : val, P (tm_val v)) -> forall t : tm, P t

tm_mut_rect
     : forall (P : tm -> Type) (P0 : val -> Type),
       (forall i : ident, P (tm_var i)) ->
       (forall t : tm, P t -> forall t0 : tm, P t0 -> P (tm_app t t0)) ->
       (forall v : val, P0 v -> P (tm_val v)) ->
       (forall (i : ident) (t : tm), P t -> P0 (val_abs i t)) -> P0 val_unit -> forall t : tm, P t

(* Idea: use unit as a dummy argument *)

(*Scheme tm_mut_rect := Induction for tm Sort Set
with val_mut_rect := Induction for val Sort Set
with foo_mut_rect := Induction for foo Sort Set.

Scheme tm_mut_rect := Induction for tm Sort Prop
with val_mut_rect := Induction for val Sort Prop
with foo_mut_rect := Induction for foo Sort Prop.*)

Combined Scheme tm_val_mut_ind from tm_mut_rect, val_mut_rect, foo_mut_rect.

Check tm_val_mut_ind.

Check tm_mut_rect.

(*FRecursion f about val*)

Check tm_rect.

(* 
tm_val_mut_ind
     : forall (P : tm -> Type) (P0 : val -> Type),
       (forall i : ident, P (tm_var i)) ->
       (forall t : tm, P t -> forall t0 : tm, P t0 -> P (tm_app t t0)) ->
       (forall v : val, P0 v -> P (tm_val v)) ->
       (forall (i : ident) (t : tm), P t -> P0 (val_abs i t)) ->
       P0 val_unit -> (forall t : tm, P t) * (forall v : val, P0 v) *)
Family A.
   Family C.
   FEnd C.
FEnd A.

(*    FRecursion f about ind motive (fun _ => 10)
            with g about ind motive (fun _ => 10) by _rect.*)
   
   
