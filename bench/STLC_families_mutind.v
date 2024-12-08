Require Import Rocqet.Loader.
Require Import Rocqet.LibTactics.
From Coq Require Import Nat.
Require Import PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Notation ident := nat.
Set Default Goal Selector "!".

Module STLC_Families_MutInd.

Definition partial_map k := ident -> option k.
Definition empty {A : Type} : partial_map A :=
  fun _ => None.
Definition update {A : Type} (m : partial_map A)
  (x : ident) (v : A) : partial_map A :=
  fun x' => if eqb x x' then Some v else m x'.

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update.
  rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros. apply PeanoNat.Nat.eqb_neq in H.
  unfold update. rewrite H. reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros. apply functional_extensionality. intros y.
  unfold update. destruct (PeanoNat.Nat.eqb_spec x y); auto.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros. apply functional_extensionality. intros y.
  unfold update. rewrite <- H.
  destruct (PeanoNat.Nat.eqb_spec x y); auto.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros. apply functional_extensionality. intros y.
  unfold update.
  destruct (PeanoNat.Nat.eqb_spec x1 y), (PeanoNat.Nat.eqb_spec x2 y);
    try reflexivity.
  - rewrite <- e in e0. contradiction.
Qed.

Family STLC.
FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.


FInductive tm : Set :=
  | tm_var : ident -> tm
  | tm_app : tm -> tm -> tm
  | tm_val : val -> tm
with val : Set :=
  | val_abs : ident -> tm -> val
  | val_unit : val.

(*FScheme tm_prec PRecT about tm.
FScheme val_prec PRecT about val.*)

FRecursion subst_tm about tm motive (fun (_ : tm) => (ident -> tm -> tm))
  with subst_val about val motive (fun (_ : val) => (ident -> tm -> val))
  by _rect.

Case tm_var :=
  (fun y x t =>
    if x =? y then t else (tm_var y)).

Case tm_app :=
  (fun t1 rec_t1 t2 rec_t2 x t =>
    tm_app (rec_t1 x t) (rec_t2 x t)).

Case tm_val :=
  (fun v rec_v x t =>
    tm_val (rec_v x t)).

Case val_abs :=
  (fun y body rec_body x t =>
    val_abs y (if x =? y then body else (rec_body x t))).

Case val_unit :=
  (fun x t =>
    val_unit).

FEnd subst_tm with subst_val.

FDefinition context : Type := partial_map ty.

FInductive step : tm -> tm -> Prop :=
  | st_app0 : forall a a' b,
    (step a a') ->
    (step
      (tm_app a b)
      (tm_app a' b))
  | st_app1 : forall a b b',
    (step b b') ->
    (step
      (tm_app (tm_val a) b)
      (tm_app (tm_val a) b'))
  | st_app2 : forall b x body,
    (step
      (tm_app (tm_val (val_abs x body)) (tm_val b))
      (subst_tm body x (tm_val b))).


Closing Fact not_step_tm_var:
  forall i x',
    ~ step (tm_var i) x'
  by {intros i x' H; inversion H}.

Closing Fact not_step_tm_val:
  forall v x', ~ step (tm_val v) x'
  by {intros v x' H; inversion H}.

Closing Fact step_tm_app_inv:
  forall x y t,
    step (tm_app x y) t ->
    (exists x', step x x'
      /\ t = tm_app x' y)
    \/ ((exists v, x = tm_val v)
        /\ (exists y', step y y' /\ t = tm_app x y'))
    \/ (exists v body, x = tm_val (val_abs v body)
        /\ (exists vy, y = tm_val vy)
        /\ t = subst_tm body v y)
  by { inversion 1;
      try (left; repeat eexists; eauto; fail);
      try (right; left; repeat eexists; eauto; fail);
      try (right; right; repeat eexists; eauto; fail)}.

MetaData steps.
(* We want a non-extensible steps
    such that inversion on it is possible *)
Inductive steps : tm -> tm -> Prop :=
  | sts_refl : forall x, steps x x
  | sts_trans : forall x y z, step x y -> steps y z -> steps x z.
FEnd steps.

FInductive has_type_tm : context -> tm -> ty -> Prop :=
  | ht_var : forall G x T1,
      G x = Some T1 ->
      has_type_tm G (tm_var x) T1
  | ht_app : forall G x y T1 T2,
      has_type_tm G x (ty_arrow T1 T2) ->
      has_type_tm G y T1 ->
      has_type_tm G (tm_app x y) T2
  | ht_val : forall G v T1,
      has_type_val G v T1 ->
      has_type_tm G (tm_val v) T1
with has_type_val : context -> val -> ty -> Prop :=
  | ht_abs : forall G x body T1 T2,
      has_type_tm (x |-> T1; G) body T2 ->
      has_type_val G (val_abs x body) (ty_arrow T1 T2)
  | ht_unit : forall G,
      has_type_val G val_unit ty_unit.
      
Closing Fact ht_inv_tm_val :
  forall G v T1,
    has_type_tm G (tm_val v) T1 ->
    has_type_val G v T1
  by { inversion 1; auto }.

Closing Fact value_arrow_type_abs :
  forall v T1 T2,
    has_type_val empty v (ty_arrow T1 T2) ->
    exists x b, v = val_abs x b
  by { inversion 1; eauto }.

Closing Fact ht_inv_val_abs :
  forall G x body T1 T2,
    has_type_val G (val_abs x body) (ty_arrow T1 T2) ->
    has_type_tm (x |-> T1; G) body T2
  by { inversion 1; auto }.

FInduction progress
  about has_type_tm
  motive
    (fun G t T (H : has_type_tm G t T) =>
      G = empty ->
      (exists v, t = tm_val v) \/ (exists t', step t t')).
FProof.
- intros. subst. inversion e.
- intros. subst. right. destruct H.
  + reflexivity.
  + destruct H. subst.
    apply ht_inv_tm_val in __i.
    apply value_arrow_type_abs in __i as (?&?&?). subst.
    destruct (H0 eq_refl).
    * destruct H. subst. eexists. eapply st_app2.
    * destruct H. eexists. eapply st_app1. eassumption.
  + destruct H. eexists. eapply st_app0. eassumption.
- intros. subst. left. eauto.
Qed. FEnd progress.

FInduction
  subst_tm_lemma about has_type_tm
  motive (fun G1 body T2 (H : has_type_tm G1 body T2) =>
    forall G x k T1,
    G1 = (update G x T1) ->
    (forall G', has_type_tm G' k T1) ->
    has_type_tm G (subst_tm body x k) T2)
  with subst_val_lemma about has_type_val
  motive (fun G1 v T2 (H : has_type_val G1 v T2) =>
    forall G x k T1,
    G1 = (update G x T1) ->
    (forall G', has_type_tm G' k T1) ->
    has_type_val G (subst_val v x k) T2).
FProof.
- intros. fsimpl.
  destruct (PeanoNat.Nat.eqb_spec x0 x); subst.
  + rewrite update_eq in e. injection e as e. subst. apply H0.
  + rewrite update_neq in e.
    * apply ht_var. assumption.
    * assumption.
- intros. fsimpl. fconstructor. 
- intros. fsimpl. 
  apply ht_val. eapply H; eauto.
- intros. fsimpl. 
  destruct (PeanoNat.Nat.eqb_spec x0 x); subst; eapply ht_abs.
  + rewrite update_shadow in __i. assumption.
  + eapply H; eauto. apply update_permute; assumption.
- intros. fsimpl. 
  apply ht_unit.
Qed. FEnd subst_tm_lemma with subst_val_lemma.

FInductive fv_tm : ident -> tm -> Prop :=
  | fv_tm_var : forall x,
      fv_tm x (tm_var x)
  | fv_tm_app1 : forall x a b,
      fv_tm x a -> fv_tm x (tm_app a b)
  | fv_tm_app2 : forall x a b,
      fv_tm x b -> fv_tm x (tm_app a b)
  | fv_tm_val : forall x v,
      fv_val x v -> fv_tm x (tm_val v)
with fv_val : ident -> val -> Prop :=
  | fv_val_abs :  forall x v body,
      fv_tm x body -> x <> v -> fv_val x (val_abs v body).

Closing Fact fv_inv_tm_var :
  forall x x',
    fv_tm x (tm_var x') ->
    x = x'
  by { inversion 1; auto }.

Closing Fact fv_inv_tm_app :
  forall x a b,
    fv_tm x (tm_app a b) ->
    fv_tm x a \/ fv_tm x b
  by { inversion 1; auto }.
  
Closing Fact fv_inv_tm_val :
  forall x v,
    fv_tm x (tm_val v) ->
    fv_val x v
  by { inversion 1; auto }.

Closing Fact fv_inv_val_unit :
  forall x,
  ~ fv_val x val_unit
  by { unfold not; inversion 1; auto }.

Closing Fact fv_inv_val_abs :
  forall x v body,
    fv_val x (val_abs v body) ->
    fv_tm x body /\ x <> v
  by { inversion 1; auto }.

FInduction
  free_var_tm_in_ctx about has_type_tm
  motive (fun G t T (H : has_type_tm G t T) =>
    forall x,
    fv_tm x t ->
    exists U, G x = Some U)
  with free_var_val_in_ctx about has_type_val
  motive (fun G v T (H : has_type_val G v T) =>
    forall x,
    fv_val x v ->
    exists U, G x = Some U).
FProof.
- intros. apply fv_inv_tm_var in H. subst. eauto.
- intros. apply fv_inv_tm_app in H1 as []; eauto.
- intros. apply fv_inv_tm_val in H0. eauto.
- intros. apply fv_inv_val_abs in H0 as [].
  erewrite <- update_neq; eauto.
- intros. apply fv_inv_val_unit in H as [].
Qed. FEnd free_var_tm_in_ctx with free_var_val_in_ctx.

FInduction
  free_var_tm_matters about has_type_tm
  motive (fun G1 t T (H : has_type_tm G1 t T) =>
    forall G2,
    (forall x, fv_tm x t -> G1 x = G2 x) ->
    has_type_tm G2 t T)
  with free_var_val_matters about has_type_val
  motive (fun G1 v T (H : has_type_val G1 v T) =>
    forall G2,
    (forall x, fv_val x v -> G1 x = G2 x) ->
    has_type_val G2 v T).
FProof.
- intros. apply ht_var. rewrite <- e. symmetry.
  auto using fv_tm_var.
- intros. eapply ht_app;
    eauto using fv_tm_app1, fv_tm_app2.
- intros. apply ht_val.
  auto using fv_tm_val.
- intros. apply ht_abs. apply H. intros.
  destruct (PeanoNat.Nat.eqb_spec x x0).
  + subst. repeat rewrite update_eq. reflexivity.
  + repeat rewrite update_neq; auto using fv_val_abs.
- intros. apply ht_unit.
Qed. FEnd free_var_tm_matters with free_var_val_matters.


FLemma weakening_lemma_tm :
  forall k T,
  has_type_tm empty k T ->
  (forall G, has_type_tm G k T).
FProofLemma.
intros. eapply free_var_tm_matters.
- eassumption.
- intros. destruct (free_var_tm_in_ctx _ _ _ H _ H0).
  unfold empty in H1. discriminate.
Qed. CloseFLemma. (* weakening_lemma_tm.*)

FLemma weakening_lemma_val :
  forall k T,
  has_type_val empty k T ->
  (forall G, has_type_val G k T).
FProofLemma.
intros. eapply free_var_val_matters.
- eassumption.
- intros. destruct (free_var_val_in_ctx _ _ _ H _ H0).
  unfold empty in H1. discriminate.
Qed. CloseFLemma. (* FEnd weakening_lemma_val.*)

FInduction preservation
  about has_type_tm
  motive
    (fun G t T (h : has_type_tm G t T) =>
      G = empty ->
      forall t',
      step t t' ->
      has_type_tm empty t' T).
FProof.
- intros. subst. unfold empty in e. discriminate. 
- intros.
  destruct (step_tm_app_inv _ _ _ H2)
    as [[?[]]|[[?[?[? ?]]]|[?[?[?[[? ?]?]]]]]];
    subst; try (eapply ht_app; eauto).
  + eapply subst_tm_lemma.
    * apply ht_inv_tm_val in __i.
      apply ht_inv_val_abs in __i.
      apply __i.
    * reflexivity.
    * intros. apply weakening_lemma_tm. assumption. 
- intros. apply not_step_tm_val in H0 as [].
Qed. FEnd preservation.


FLemma preservation2 :
  forall t t',
    steps t t' ->
    forall T,
    has_type_tm empty t T ->
    has_type_tm empty t' T.
FProofLemma.
intros t t' h. induction h; intros; subst; eauto using preservation.
eapply IHh; eauto. eapply preservation; eauto.
Qed. CloseFLemma. (* FEnd preservation2.*)


FLemma type_safety:
  forall t t' T,
    has_type_tm empty t T ->
    steps t t' ->
    (exists v, t' = tm_val v) \/ (exists t'', step t' t'').
FProofLemma.
intros. eapply progress; eauto using preservation2.
Qed. CloseFLemma. (* FEnd type_safety.*)

FEnd STLC.

Family STLC_bool extends STLC.
FInductive ty : Set :=
  | ty_bool : ty.


FInductive tm : Set :=
  | tm_if : tm -> tm -> tm -> tm
with val : Set :=
  | val_true : val
  | val_false : val.

FRecursion subst_tm with subst_val.
Case val_true :=
  (fun x t => val_true).

Case val_false :=
  (fun x t => val_false).

Case tm_if :=
  (fun cond rec_cond a rec_a b rec_b =>
    fun x t => tm_if (rec_cond x t) (rec_a x t) (rec_b x t)).

FEnd subst_tm with subst_val.


FInductive step : tm -> tm -> Prop :=
  | st_if0 : forall c c' a b,
    (step c c') -> (step (tm_if c a b) (tm_if c' a b))
  | st_if1 : forall a b,
    (step (tm_if (tm_val val_true) a b) a)
  | st_if2 : forall a b,
    (step (tm_if (tm_val val_false) a b) b).

Closing Fact step_tm_if_inv:
  forall c a b t,
  step (tm_if c a b) t ->
    (exists c', (step c c' /\ t = (tm_if c' a b)))
    \/ (c = tm_val val_true /\ t = a)
    \/ (c = tm_val val_false /\ t = b)
  by { inversion 1; eauto }.

FInductive has_type_tm : context -> tm -> ty -> Prop :=
  | ht_if : forall G c a b T,
      has_type_tm G c ty_bool ->
      has_type_tm G a T ->
      has_type_tm G b T ->
      has_type_tm G (tm_if c a b) T
with has_type_val : context -> val -> ty -> Prop :=
  | ht_true : forall G,
      has_type_val G val_true ty_bool
  | ht_false : forall G,
      has_type_val G val_false ty_bool.

Closing Fact value_bool_type_true_false:
  forall v,
  has_type_val empty v ty_bool ->
  (v = val_true \/ v = val_false)
by { inversion 1; eauto }.

FInduction progress.
FProof.
intros. subst. right. destruct (H eq_refl) as [[]|[]]; subst.
- apply ht_inv_tm_val in __i.
  apply value_bool_type_true_false in __i as [|];
    subst; eauto using st_if1, st_if2.
- eauto using st_if0.
Qed. FEnd progress.

FInduction subst_tm_lemma with subst_val_lemma.
FProof.
- intros. fsimpl. fconstructor.
- intros. fsimpl. fconstructor. 
- intros. fsimpl. fconstructor. 
Qed. FEnd subst_tm_lemma with subst_val_lemma.

FInductive fv_tm : ident -> tm -> Prop :=
| fv_if0 : forall x c a b,
    fv_tm x c -> fv_tm x (tm_if c a b)
| fv_if1 : forall x c a b,
    fv_tm x a -> fv_tm x (tm_if c a b)
| fv_if2 : forall x c a b,
    fv_tm x b -> fv_tm x (tm_if c a b)
with fv_val : ident -> val -> Prop := .

Closing Fact fv_inv_tm_if:
forall x c a b,
  fv_tm x (tm_if c a b) ->
  fv_tm x c \/ fv_tm x a \/ fv_tm x b
by { inversion 1; auto }.

Closing Fact fv_inv_val_true :
  forall x,
  ~ fv_val x val_true
  by { unfold not; inversion 1; auto }.
  
Closing Fact fv_inv_val_false :
forall x,
~ fv_val x val_false
by { unfold not; inversion 1; auto }.

FInduction free_var_tm_in_ctx with free_var_val_in_ctx.
FProof.
- intros. apply fv_inv_tm_if in H2 as [|[|]]; eauto.
- intros. apply fv_inv_val_true in H as [].
- intros. apply fv_inv_val_false in H as [].
Qed. FEnd free_var_tm_in_ctx with free_var_val_in_ctx.

FInduction free_var_tm_matters with free_var_val_matters.
FProof.
- intros. apply ht_if;
    eauto using fv_if0, fv_if1, fv_if2.
- intros. apply ht_true.
- intros. apply ht_false.
Qed. FEnd free_var_tm_matters with free_var_val_matters.


FInduction preservation.
FProof.
intros. subst.
apply step_tm_if_inv in H3 as [[?[? ?]]|[[? ?]|[? ?]]];
  subst; eauto using ht_if.
Qed. FEnd preservation.

FEnd STLC_bool.

Family STLC_prod extends STLC.
FInductive ty : Set :=
  | ty_prod : ty -> ty -> ty.



FInductive tm : Set :=
  | tm_prod : tm -> tm -> tm
  | tm_pi1 : tm -> tm
  | tm_pi2 : tm -> tm
with val : Set :=
  | val_prod : val -> val -> val.

FRecursion subst_tm with subst_val.
Case tm_pi1 :=
  (fun a rec_a x t => tm_pi1 (rec_a x t)).

Case tm_pi2 :=
  (fun a rec_a x t => tm_pi2 (rec_a x t)).

Case tm_prod :=
  (fun a rec_a b rec_b x t => tm_prod (rec_a x t) (rec_b x t)).

Case val_prod :=
  (fun a rec_a b rec_b x t => val_prod (rec_a x t) (rec_b x t)).
FEnd subst_tm with subst_val.

FInductive step : tm -> tm -> Prop :=
  | st_prod0 : forall a a' b,
    (step a a') -> (step (tm_prod a b) (tm_prod a' b))
  | st_prod1 : forall a b b',
    (step b b') -> (step (tm_prod (tm_val a) b) (tm_prod (tm_val a) b'))
  | st_prod2 : forall a b,
    (step (tm_prod (tm_val a) (tm_val b)) (tm_val (val_prod a b)))
  | st_pi10 : forall a a',
    step a a' ->
    (step (tm_pi1 a) (tm_pi1 a'))
  | st_pi11 : forall a b,
    (step (tm_pi1 (tm_val (val_prod a b))) (tm_val a))
  | st_pi20 : forall a a',
    step a a' ->
    (step (tm_pi2 a) (tm_pi2 a'))
  | st_pi21 : forall a b,
    (step (tm_pi2 (tm_val (val_prod a b))) (tm_val b)).

    
Closing Fact st_prod_inv:
    forall a b c,
    step (tm_prod a b) c ->
      (exists a', step a a' /\ c = tm_prod a' b)
      \/ ((exists v, a = tm_val v) /\ (exists b', step b b' /\ c = tm_prod a b'))
      \/ (exists va vb, a = tm_val va /\ b = tm_val vb /\ c = tm_val (val_prod va vb))
  by {inversion 1; iauto }.

Closing Fact st_pi1_inv:
    forall a b,
    step (tm_pi1 a) b ->
      (exists a', step a a' /\ b = tm_pi1 a')
      \/ (exists x y, a = (tm_val (val_prod x y)) /\ b = tm_val x)
by { inversion 1; eauto }.

Closing Fact st_pi2_inv:
    forall a b,
    step (tm_pi2 a) b ->
      (exists a', step a a' /\ b = tm_pi2 a')
      \/ (exists x y, a = (tm_val (val_prod x y)) /\ b = tm_val y)
by { inversion 1; eauto }.


FInductive has_type_tm : context -> tm -> ty -> Prop :=
  | ht_pi1 : forall G t A B,
      has_type_tm G t (ty_prod A B) ->
      has_type_tm G (tm_pi1 t) A
  | ht_pi2 : forall G t A B,
      has_type_tm G t (ty_prod A B) ->
      has_type_tm G (tm_pi2 t) B
  | ht_tm_prod : forall G a b A B,
      has_type_tm G a A ->
      has_type_tm G b B ->
      has_type_tm G (tm_prod a b) (ty_prod A B)
with has_type_val : context -> val -> ty -> Prop :=
  | ht_val_prod : forall G a b A B,
      has_type_val G a A ->
      has_type_val G b B ->
      has_type_val G (val_prod a b) (ty_prod A B).

(* Canonical form *)
Closing Fact value_prod_type_inv:
  forall v A B,
  has_type_val empty v (ty_prod A B) ->
  exists a b, v = val_prod a b /\ has_type_val empty a A /\ has_type_val empty b B
by { inversion 1; eauto }.

FInduction progress.
FProof.
- intros. subst. right. destruct (H eq_refl) as [[]|[]]; subst.
  + apply ht_inv_tm_val in __i.
    apply value_prod_type_inv in __i as (?&?&?&?&?). subst.
    eauto using st_pi11.
  + eauto using st_pi10.
- intros. subst. right. destruct (H eq_refl) as [[]|[]]; subst.
  + apply ht_inv_tm_val in __i.
    apply value_prod_type_inv in __i as (?&?&?&?&?). subst.
    eauto using st_pi21.
  + eauto using st_pi20.
- intros. subst. right.
  destruct (H eq_refl) as [[]|[]], (H0 eq_refl) as [[]|[]]; subst.
  + eauto using st_prod2.
  + eauto using st_prod1.
  + eauto using st_prod0.
  + eauto using st_prod0.
Qed. FEnd progress.


FInduction subst_tm_lemma with subst_val_lemma.
FProof.
+ intros. fsimpl. fconstructor.
+ intros. fsimpl. fconstructor.
+ intros. fsimpl. fconstructor.
+ intros. fsimpl. fconstructor.  
Qed. FEnd subst_tm_lemma with subst_val_lemma.

FInductive fv_tm : ident -> tm -> Prop :=
  | fv_tm_prod0 : forall x a b,
      fv_tm x a -> fv_tm x (tm_prod a b)
  | fv_tm_prod1 : forall x a b,
      fv_tm x b -> fv_tm x (tm_prod a b)
  | fv_pi1 : forall x a,
      fv_tm x a -> fv_tm x (tm_pi1 a)
  | fv_pi2 : forall x a,
      fv_tm x a -> fv_tm x (tm_pi2 a)
with fv_val : ident -> val -> Prop :=
  | fv_val_prod0 : forall x a b,
      fv_val x a -> fv_val x (val_prod a b)
  | fv_val_prod1 : forall x a b,
      fv_val x b -> fv_val x (val_prod a b).


Closing Fact fv_inv_tm_prod:
  forall x a b,
  fv_tm x (tm_prod a b) ->
  fv_tm x a \/ fv_tm x b
by { inversion 1; auto }.

Closing Fact fv_inv_tm_pi1:
  forall x a,
  fv_tm x (tm_pi1 a) ->
  fv_tm x a
by { inversion 1; auto }.

Closing Fact fv_inv_tm_pi2:
  forall x a,
  fv_tm x (tm_pi2 a) ->
  fv_tm x a
by { inversion 1; auto }.

Closing Fact fv_inv_val_prod:
  forall x a b,
  fv_val x (val_prod a b) ->
  fv_val x a \/ fv_val x b
by { inversion 1; auto }.

FInduction free_var_tm_in_ctx with free_var_val_in_ctx.
FProof.
- intros. eauto using fv_inv_tm_pi1.
- intros. eauto using fv_inv_tm_pi2.
- intros. apply fv_inv_tm_prod in H1 as []; eauto.
- intros. apply fv_inv_val_prod in H1 as []; eauto.
Qed. FEnd free_var_tm_in_ctx with free_var_val_in_ctx.


FInduction free_var_tm_matters with free_var_val_matters.
FProof.
- intros. eapply ht_pi1. eauto using fv_pi1.
- intros. eapply ht_pi2. eauto using fv_pi2.
- intros. eapply ht_tm_prod.
  + eauto using fv_tm_prod0.
  + eauto using fv_tm_prod1.
- intros. eapply ht_val_prod.
  + eauto using fv_val_prod0.
  + eauto using fv_val_prod1.
Qed. FEnd free_var_tm_matters with free_var_val_matters.


(* Inherit Field weakening_lemma. *)

Closing Fact inject_tm_prod:
  forall a b c d,
  tm_prod a b = tm_prod c d ->
  a = c /\ b = d
by { inversion 1; auto }.

Closing Fact inject_val_prod:
  forall a b c d,
  val_prod a b = val_prod c d ->
  a = c /\ b = d
by { inversion 1; auto }.

FInduction preservation.
FProof.
- intros. subst. apply st_pi1_inv in H1 as [[?[]]|[?[?[]]]]; subst.
  + eauto using ht_pi1.
  + apply ht_inv_tm_val in __i.
    apply value_prod_type_inv in __i as (?&?&?&?&?).
    apply inject_val_prod in H0 as []. subst.
    apply ht_val. assumption.
- intros. subst. apply st_pi2_inv in H1 as [[?[]]|[?[?[]]]]; subst.
  + eauto using ht_pi2.
  + apply ht_inv_tm_val in __i.
    apply value_prod_type_inv in __i as (?&?&?&?&?).
    apply inject_val_prod in H0 as []. subst.
    apply ht_val. assumption.
- intros. subst. apply st_prod_inv in H2 as [[?[]]|[[[][?[]]]|[?[?[?[]]]]]];
    subst; eauto using ht_tm_prod.
  + eauto using ht_val, ht_val_prod, ht_inv_tm_val.
Qed. FEnd preservation.

Time FEnd STLC_prod.



Family STLC_bot extends STLC.

FInductive ty : Set :=
  | ty_bot : ty.


FEnd STLC_bot.

Family STLC_sum extends STLC.
FInductive ty : Set :=
  | ty_sum : ty -> ty -> ty .


FInductive tm : Set :=
  (* sum *)
  | tm_inl : tm -> tm
  | tm_inr : tm -> tm
  | tm_case : tm -> ident -> tm -> tm -> tm
with val : Set :=
  | val_inl : val -> val
  | val_inr : val -> val.


FRecursion subst_tm with subst_val.

Case tm_inl :=
  (fun a rec_a =>
    fun x t =>
    tm_inl (rec_a x t)).

Case tm_inr :=
  (fun a rec_a =>
    fun x t =>
    tm_inr (rec_a x t)).

Case tm_case :=
  (fun cond rec_cond i a rec_a b rec_b =>
    fun x t =>
    if i =? x then
      tm_case (rec_cond x t) i a b
    else
      tm_case (rec_cond x t) i (rec_a x t) (rec_b x t)).

Case val_inl :=
  (fun a rec_a =>
    fun x t =>
    val_inl (rec_a x t)).

Case val_inr :=
  (fun a rec_a =>
    fun x t =>
    val_inr (rec_a x t)).

FEnd subst_tm with subst_val.


(* Closing Fact subst_tm_inl :
forall a,
subst (tm_inl a) = subst_handler.tm_inl a (subst a)
by { intros; eauto }.

Closing Fact subst_tm_inr :
forall a,
subst (tm_inr a) = subst_handler.tm_inr a (subst a)
by { intros; eauto }.

Closing Fact subst_tm_case :
forall cond i lb rb,
subst (tm_case cond i lb rb) = subst_handler.tm_case cond (subst cond) i lb (subst lb) rb (subst rb)
by { intros; eauto }. *)



(* Inherit Field context.*)

FInductive step : tm -> tm -> Prop :=
  | st_inl0 : forall a a',
    step a a' ->
    step (tm_inl a) (tm_inl a')
  | st_inl1 : forall a,
    step (tm_inl (tm_val a)) (tm_val (val_inl a))
  | st_inr0 : forall a a',
    step a a' ->
    step (tm_inr a) (tm_inr a')
  | st_inr1 : forall a,
    step (tm_inr (tm_val a)) (tm_val (val_inr a))
  | st_case0: forall c c' i lb rb,
    step c c' ->
    step (tm_case c i lb rb) (tm_case c' i lb rb)
  | st_case1: forall i lb rb v,
    step (tm_case (tm_val (val_inl v)) i lb rb) (subst_tm lb i (tm_val v))
  | st_case2: forall i lb rb v,
    step (tm_case (tm_val (val_inr v)) i lb rb) (subst_tm rb i (tm_val v)).

(* Inherit Until Field has_type. *)

FInductive has_type_tm : context -> tm -> ty -> Prop :=
  | ht_sum0 : forall G t L R,
      has_type_tm G t L ->
      has_type_tm G (tm_inl t) (ty_sum L R)
  | ht_sum1 : forall G t L R,
      has_type_tm G t R ->
      has_type_tm G (tm_inr t) (ty_sum L R)
  | ht_case : forall G c L R T lb rb i,
      has_type_tm G c (ty_sum L R) ->
      has_type_tm (i |-> L ; G) lb T ->
      has_type_tm (i |-> R ; G) rb T ->
      has_type_tm G (tm_case c i lb rb) T
with has_type_val : context -> val -> ty -> Prop :=
  | ht_val_sum0 : forall G v L R,
      has_type_val G v L ->
      has_type_val G (val_inl v) (ty_sum L R)
  | ht_val_sum1 : forall G v L R,
      has_type_val G v R ->
      has_type_val G (val_inr v) (ty_sum L R).

(* Inherit Until Field progress.*)

Closing Fact value_sum_type_inv:
  forall c L R,
  has_type_val empty c (ty_sum L R) ->
  (exists l, c = val_inl l) \/ (exists r, c = val_inr r)
by { inversion 1; eauto }.

FInduction progress.
FProof.
- intros. right. subst. destruct (H eq_refl) as [[]|[]]; clear H; subst.
  + eauto using st_inl1.
  + eauto using st_inl0.
- intros. right. subst. destruct (H eq_refl) as [[]|[]]; clear H; subst.
  + eauto using st_inr1.
  + eauto using st_inr0.
- intros. right. subst. destruct (H eq_refl) as [[]|[]]; clear H; subst.
  + apply ht_inv_tm_val in __i.
    apply value_sum_type_inv in __i as [[]|[]]; subst.
    * eauto using st_case1.
    * eauto using st_case2.
  + eauto using st_case0.
Qed. FEnd progress.


FInduction subst_tm_lemma with subst_val_lemma.
FProof.
+ intros. fsimpl. fconstructor.
+ intros. fsimpl. fconstructor.
+ intros. fsimpl. destruct (PeanoNat.Nat.eqb_spec i x); subst.
  - rewrite update_shadow in *. eauto using ht_case.
  - eapply ht_case; eauto using update_permute.
+ intros. fsimpl. fconstructor.
+ intros. fsimpl. fconstructor. 
Qed. FEnd subst_tm_lemma with subst_val_lemma.

FInductive fv_tm : ident -> tm -> Prop :=
  | fv_tm_inl : forall x a,
      fv_tm x a ->
      fv_tm x (tm_inl a)
  | fv_tm_inr : forall x a,
      fv_tm x a ->
      fv_tm x (tm_inr a)
  | fv_case : forall x c i lb rb,
      fv_tm x c ->
      fv_tm x (tm_case c i lb rb)
  | fv_case1 : forall x c i lb rb,
      fv_tm x lb ->
      i <> x ->
      fv_tm x (tm_case c i lb rb)
  | fv_case2 : forall x c i lb rb,
      fv_tm x rb ->
      i <> x ->
      fv_tm x (tm_case c i lb rb)
with fv_val : ident -> val -> Prop :=
  | fv_val_inl : forall x a,
      fv_val x a ->
      fv_val x (val_inl a)
  | fv_val_inr : forall x a,
      fv_val x a ->
      fv_val x (val_inr a).

Closing Fact fv_inv_tm_inl:
  forall x t, fv_tm x (tm_inl t) -> fv_tm x t
by { inversion 1; auto }.

Closing Fact fv_inv_tm_inr:
  forall x t, fv_tm x (tm_inr t) -> fv_tm x t
by { inversion 1; auto }.

Closing Fact fv_inv_tm_case:
  forall x c i lb rb,
  fv_tm x (tm_case c i lb rb) ->
    (fv_tm x c)
    \/ (i <> x /\ fv_tm x lb)
    \/ (i <> x /\ fv_tm x rb)
by { inversion 1; auto }.

Closing Fact fv_inv_val_inl:
  forall x v, fv_val x (val_inl v) -> fv_val x v
by { inversion 1; auto }.

Closing Fact fv_inv_val_inr:
  forall x v, fv_val x (val_inr v) -> fv_val x v
by { inversion 1; auto }.


FInduction free_var_tm_in_ctx with free_var_val_in_ctx.
FProof.
+ intros. auto using fv_inv_tm_inl,
    fv_inv_tm_inr,
    fv_inv_val_inl,
    fv_inv_val_inr.
+   intros. auto using fv_inv_tm_inl,
    fv_inv_tm_inr,
    fv_inv_val_inl,
      fv_inv_val_inr.
+ intros. auto using fv_inv_tm_inl,
    fv_inv_tm_inr,
    fv_inv_val_inl,
    fv_inv_val_inr.
   apply fv_inv_tm_case in H2 as [|[[]|[]]];
  auto; try erewrite <- update_neq; eauto.
+ intros. auto using fv_inv_tm_inl,
    fv_inv_tm_inr,
    fv_inv_val_inl,
    fv_inv_val_inr.
+ intros. auto using fv_inv_tm_inl,
    fv_inv_tm_inr,
    fv_inv_val_inl,
    fv_inv_val_inr.
Qed. FEnd free_var_tm_in_ctx with free_var_val_in_ctx.


FInduction free_var_tm_matters with free_var_val_matters.
FProof.
+ intros. eauto using ht_sum0, ht_sum1,
    ht_val_sum0, ht_val_sum1,
    fv_tm_inl, fv_tm_inr,
    fv_val_inl, fv_val_inr.
+   intros. eauto using ht_sum0, ht_sum1,
    ht_val_sum0, ht_val_sum1,
    fv_tm_inl, fv_tm_inr,
      fv_val_inl, fv_val_inr.
+  intros. eapply ht_case.
    - eauto using fv_case.
    -  apply H0. intros x ?. destruct (PeanoNat.Nat.eqb_spec i x).
       ++ subst. repeat rewrite update_eq. reflexivity.
       ++ repeat rewrite update_neq; eauto using fv_case1.
    - apply H1. intros x ?. destruct (PeanoNat.Nat.eqb_spec i x).
  ++ subst. repeat rewrite update_eq. reflexivity.
  ++ repeat rewrite update_neq; eauto using fv_case2.
+   intros. eauto using ht_sum0, ht_sum1,
    ht_val_sum0, ht_val_sum1,
    fv_tm_inl, fv_tm_inr,
      fv_val_inl, fv_val_inr.
+   intros. eauto using ht_sum0, ht_sum1,
    ht_val_sum0, ht_val_sum1,
    fv_tm_inl, fv_tm_inr,
      fv_val_inl, fv_val_inr.        
Qed. FEnd free_var_tm_matters with free_var_val_matters.




(*Inherit Until Field preservation.*)

Closing Fact step_tm_inl_inv:
  forall x y,
  step (tm_inl x) y ->
    (exists x', y = tm_inl x' /\ step x x')
    \/ (exists v, x = tm_val v /\ y = tm_val (val_inl v))
by { inversion 1; eauto }.

Closing Fact step_tm_inr_inv:
  forall x y,
  step (tm_inr x) y ->
    (exists x', y = tm_inr x' /\ step x x')
    \/ (exists v, x = tm_val v /\ y = tm_val (val_inr v))
by { inversion 1; eauto }.

Closing Fact step_tm_case_inv:
  forall c i lb rb y,
  step (tm_case c i lb rb) y ->
    (exists c', y = tm_case c' i lb rb /\ step c c')
    \/ (exists v, c = tm_val (val_inl v) /\ y = (subst_tm lb i (tm_val v)))
    \/ (exists v, c = tm_val (val_inr v) /\ y = (subst_tm rb i (tm_val v)))
by { inversion 1; eauto }.

Closing Fact ht_inl_inv:
  forall G x L R,
  has_type_val G (val_inl x) (ty_sum L R) ->
  has_type_val G x L by
{ inversion 1; eauto }.

Closing Fact ht_inr_inv:
  forall G x L R,
  has_type_val G (val_inr x) (ty_sum L R) ->
  has_type_val G x R by
{ inversion 1; eauto }.

FInduction preservation.
FProof.
- intros. subst. apply step_tm_inl_inv in H1 as [[?[]]|[?[]]]; subst.
  + eauto using ht_sum0.
  + eauto using ht_inv_tm_val, ht_val, ht_val_sum0.
- intros. subst. apply step_tm_inr_inv in H1 as [[?[]]|[?[]]]; subst.
  + eauto using ht_sum1.
  + eauto using ht_inv_tm_val, ht_val, ht_val_sum1.
- intros. subst. apply step_tm_case_inv in H3 as [[?[]]|[[?[]]|[?[]]]]; subst.
  + eauto using ht_case.
  + eapply subst_tm_lemma;
      eauto using ht_val, ht_inv_tm_val,
        ht_inl_inv, weakening_lemma_val.
  + eapply subst_tm_lemma;
      eauto using ht_val, ht_inv_tm_val,
        ht_inr_inv, weakening_lemma_val.
Qed. FEnd preservation.

Time FEnd STLC_sum.

Family STLC_fix extends STLC.


(* Inherit Until Field tm. *)
FInductive tm : Set :=
  | tm_fix : ident -> tm -> tm
with val : Set := .

(* Inherit Until Field subst_handler. *)

FRecursion subst_tm with subst_val.

Case tm_fix
  := (fun s body rec_body =>
    fun x t =>
    if x =? s then
      tm_fix s body
    else
      tm_fix s (rec_body x t)).

FEnd subst_tm with subst_val.




(* Inherit Field context. *)

FInductive step : tm -> tm -> Prop :=
  | st_fix : forall i body,
    step (tm_fix i body) (subst_tm body i (tm_fix i body)).


FInductive has_type_tm : (partial_map ty) -> tm -> ty -> Prop :=
  | ht_fix : forall G x body T,
      has_type_tm (x |-> T; G) body T ->
      has_type_tm G (tm_fix x body) T
with has_type_val : (partial_map ty) -> val -> ty -> Prop := .


(* Closing Fact value_fix_type_inv:
  forall t i T,
  value t ->
  has_type empty t (ty_fix i T) ->
  (exists t', t = tm_fold t' /\ value t')
by {
  intros t i T h h1;
  inversion h; subst; eauto; inversion h1; subst; eauto}.*)

FInduction progress.
FProof.
intros. subst. right. eauto using st_fix.
Qed. FEnd progress.



FInduction subst_tm_lemma with subst_val_lemma.
FProof.
intros. fsimpl. 
destruct (PeanoNat.Nat.eqb_spec x0 x);
  subst; eapply ht_fix.
- rewrite update_shadow in *. eauto.
- eauto using update_permute.
Qed. FEnd subst_tm_lemma with subst_val_lemma.

FInductive fv_tm : ident -> tm -> Prop :=
| fv_fix :  forall x v body,
  fv_tm x body -> x <> v -> fv_tm x (tm_fix v body)
with fv_val : ident -> val -> Prop := .


Closing Fact fv_inv_tm_fix:
forall x v body,
  fv_tm x (tm_fix v body) ->
  fv_tm x body /\ x <> v
by { inversion 1; auto }.




FInduction free_var_tm_in_ctx with free_var_val_in_ctx.
FProof.
intros. apply fv_inv_tm_fix in H0 as [].
erewrite <- update_neq; eauto.
Qed. FEnd free_var_tm_in_ctx with free_var_val_in_ctx.



FInduction free_var_tm_matters with free_var_val_matters.
FProof.
intros. apply ht_fix. apply H. intros.
destruct (PeanoNat.Nat.eqb_spec x0 x).
- subst. repeat rewrite update_eq. reflexivity.
- repeat rewrite update_neq; eauto using fv_fix.
Qed. FEnd free_var_tm_matters with free_var_val_matters.




Closing Fact step_tm_fix_inv:
  forall i body y,
  step (tm_fix i body) y ->
    y = subst_tm body i (tm_fix i body)
by { inversion 1; auto }.


(* Closing Fact step_tm_unfold_inv:
  forall x y,
  step (tm_unfold x) y ->
    (exists x', y = tm_unfold x' /\ step x x') \/
    (exists v, x = tm_fold v /\ value v /\ y = v)
by { intros x y h; inversion h; subst; eauto }. *)

Closing Fact ht_fix_inv:
forall G i body T,
has_type_tm G (tm_fix i body) T ->
has_type_tm (i |-> T ; G) body T
by { inversion 1; auto }.

FInduction preservation.
FProof.
intros. apply step_tm_fix_inv in H1. subst.
eapply subst_tm_lemma; eauto.
intros. apply weakening_lemma_tm.
apply ht_fix. assumption.
Qed. FEnd preservation.

FEnd STLC_fix.

(* each four statement below is a piece together
    the current plugin implementation requires a lot of memory
    so I cannot just run all 12 statements together
  In my machine I can run 4 statements together,
    so I group them into three groups
 *)

Family STLC_all extends STLC, STLC_bool, STLC_prod, STLC_fix, STLC_sum.
FEnd STLC_all.

(*
Family STLC_bool_prod extends STLC
    using STLC_bool using STLC_prod.

Family STLC_bool_prod_sum extends STLC
    using STLC_sum using STLC_bool_prod.

Family STLC_bool_prod_sum_fix extends STLC
    using STLC_bool_prod_sum using STLC_fix.


Family STLC_bool_prod_fix extends STLC
    using STLC_bool_prod using STLC_fix.*)

(* Family STLC_bool_sum extends STLC
    using STLC_bool using STLC_sum.

Family STLC_bool_sum_fix extends STLC
    using STLC_bool_sum using STLC_fix.

Family STLC_bool_fix extends STLC
    using STLC_bool using STLC_fix.

Family STLC_prod_sum extends STLC
    using STLC_prod using STLC_sum.  *)


(* Family STLC_prod_sum extends STLC
    using STLC_prod using STLC_sum.

Family STLC_prod_fix extends STLC
    using STLC_prod using STLC_fix.

Family STLC_prod_sum_fix extends STLC
    using STLC_prod_sum using STLC_fix.

Family STLC_sum_fix extends STLC
    using STLC_sum using STLC_fix.  *)


(* Print STLC_bool_prod_sum_fix.*)

End STLC_Families_MutInd.
