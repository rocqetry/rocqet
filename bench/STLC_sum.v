(* Require Import Coq.Unicode.Utf8. *)
(*
Field
self__STLC
FScheme*)
Require Import Rocqet.Loader.
Require Import Rocqet.LibTactics.
From Coq Require Import Nat.
Require Import PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Notation ident := nat.

Module STLC_Families.
Axiom cheat : forall {X}, X.
    
Ltac destruct_ALL :=
  repeat 
    match goal with
    | [h : _ \/ _ |- _ ] => destruct h; subst; eauto
    | [h : _ /\ _ |- _ ] => destruct h; subst; eauto
    | [h : exists _ , _ |- _ ] => destruct h; subst; eauto
    | [h : Some _ = Some _ |- _] => inversion h; subst; eauto
    | [h : {_} + {_} |- _] => destruct h; subst; eauto
    end.

Ltac forwardALL :=
    repeat (
        match goal with
        | h0 : _ -> _ |- _ =>
            forwards*: h0; generalize dependent h0
        end
    ); intros.

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

Theorem update_shadow:
  forall {A} {x} {T1} {T0} {G : partial_map A},
  (x |-> T1; x |-> T0; G) = (x |-> T1; G).
  unfold update.
  intros. eapply functional_extensionality. intros.
  destruct (PeanoNat.Nat.eq_dec x x0); subst; 
  try repeat rewrite PeanoNat.Nat.eqb_refl; subst; eauto.
  rewrite <- PeanoNat.Nat.eqb_neq in n. rewrite n in *; eauto.
Qed.


Theorem update_permute:
forall {A} {x x0} {T1} {T0} {G : partial_map A},
  x <> x0 ->
  (x |-> T1; x0 |-> T0; G) = (x0 |-> T0; x |-> T1; G).
  unfold update.
  intros. eapply functional_extensionality. intros.
  destruct (PeanoNat.Nat.eq_dec x x1); subst; 
  try repeat rewrite PeanoNat.Nat.eqb_refl; subst; eauto. 
  assert (x0 <> x1) as H0. intro. symmetry in H0. try contradiction.
  rewrite <- PeanoNat.Nat.eqb_neq in H0. rewrite H0 in *; subst; eauto.
  rewrite <- PeanoNat.Nat.eqb_neq in n. rewrite n in *; subst ;eauto.
Qed.

Lemma empty_not_update:
  forall {T} {G : partial_map T} {k} {v},
    empty <> update G k v.
  intros T G k v h. 
  assert (empty k = (update G k v) k) as H0; try rewrite h; eauto.
  unfold update in H0; eauto.
  rewrite PeanoNat.Nat.eqb_refl in H0.
  try discriminate. 
Qed.

Family STLC.
FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.


FInductive tm : Set :=
  | tm_var : ident -> tm    
  | tm_abs : ident -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_unit: tm.


(*FScheme tm_prec PRecT about tm.*)

FInductive value : self__STLC.tm -> Prop :=
  | vabs   : forall x body , (value (self__STLC.tm_abs x body)) (* omit self__STLCTm later*)
  | vtunit : value (self__STLC.tm_unit).


(* This is the only inversion lemma that we will prove manually
*)

FInduction _value_not_tm_var 
  about value
  motive (fun z (h : self__STLC.value z) => forall i,  (self__STLC.tm_var i) = z -> False).
FProof.
+ intros. apply cheat. (*prec_discriminate self__STLC.tm_prec H. *)
+ intros. apply cheat. (*prec_discriminate self__STLC.tm_prec H. *)
Qed. FEnd _value_not_tm_var .

FDefinition value_not_tm_var : forall i,  ~ self__STLC.value (self__STLC.tm_var i) :=
  fun i v => self__STLC._value_not_tm_var (self__STLC.tm_var i) v i eq_refl.


(* Other Simple Inversion Lemma is introduced in this way
    A better way of understanding is, we hold this is an invariant/constraint of the definition
      across all inheritance, i.e. value_not_tm_var never holds under any extension
*)

Closing Fact value_not_tm_app : 
  forall x y, ~ self__STLC.value (self__STLC.tm_app x y) by { intros x y H; inversion H; eauto }.

FRecursion subst 
  about tm 
  motive ((fun (_ : tm) => (ident -> tm -> tm))) by _rec.


Case tm_var  
  := (fun s x t => if (eqb x s) then t else (self__STLC.tm_var s)).

Case tm_abs 
  := (fun s body rec_body => 
     fun x t => 
    if (eqb x s) 
    then (self__STLC.tm_abs s body)
    else (self__STLC.tm_abs s (rec_body x t))).

Case tm_app 
  := (fun t rec_t t0 rec_t0 => 
    fun x t' =>
    self__STLC.tm_app (rec_t x t') (rec_t0 x t')).

Case tm_unit 
  := (fun x t => self__STLC.tm_unit).

FEnd subst.





FDefinition context : Type := partial_map self__STLC.ty.
(* self__STLC --> self$$STLC *)
FInductive step : self__STLC.tm -> self__STLC.tm -> Prop :=
  | st_app0 : forall a a' b,
    (step a a') -> (step (self__STLC.tm_app a b) (self__STLC.tm_app a' b)) 
    (* omit self__STLCTm later*)
  | st_app1 : forall a b b',
    (self__STLC.value a)   -> (step b b') -> (step (self__STLC.tm_app a b) (self__STLC.tm_app a b'))
  | st_app2 : forall b x body,
    (self__STLC.value b) -> (step (self__STLC.tm_app (self__STLC.tm_abs x body) b) (self__STLC.subst body x b)).

Closing Fact not_step_tm_var:
  forall i x',
    ~ step (tm_var i) x' 
  by {intros i x' h; inversion h}.

Closing Fact not_step_tm_abs:
  forall x b x',
    ~ step (tm_abs x b) x' 
  by {intros x b x' h; inversion h}.

Closing Fact not_step_tm_unit:
  forall x',
    ~ step tm_unit x' 
  by { intros x' h; inversion h }.

Closing Fact step_tm_app_inv:
  forall x y t,
    step (tm_app x y) t ->
    ((exists x', step x x'
      /\ t = (tm_app x' y)))
    \/  (value x 
      /\ (exists y', step y y'
      /\ (t = (tm_app x y'))))
    \/  ((exists v body,  x = tm_abs v body 
      /\ value y 
      /\ t =  (subst body v y)))
  by {intros x y t h; inversion h; subst; eauto;
      try (left; repeat eexists; subst; eauto;fail);
      try (right; left; repeat eexists; subst; eauto;fail);
      try (right; right; repeat eexists; subst; eauto;fail)}.

MetaData _steps. 
(* We want a non-extensible steps 
    such that inversion on it is possible *)
Inductive steps : self__STLC.tm -> self__STLC.tm -> Prop:=
  | sts_refl : forall x, steps x x
  | sts_trans : forall x y z, self__STLC.step x y -> steps y z -> steps x z.
FEnd _steps.


FDefinition irreducible : tm -> Prop := fun x => forall x', step x x' -> False.

FInductive has_type : self__STLC.context -> self__STLC.tm -> self__STLC.ty -> Prop :=
  | ht_var : forall G x T1,
      G x = Some T1 ->
      has_type G (self__STLC.tm_var x) T1
  | ht_app : forall G x y T1 T2,
      has_type G x (self__STLC.ty_arrow T1 T2) ->
      has_type G y T1 ->
      has_type G (self__STLC.tm_app x y) T2
  | ht_abs : forall G x body T1 T2,
      has_type (x |-> T1; G) body T2 ->
      has_type G (self__STLC.tm_abs x body) (self__STLC.ty_arrow T1 T2)
  | ht_unit : forall G,
      has_type G self__STLC.tm_unit self__STLC.ty_unit .


Closing Fact not_ht_abs_unit :
  forall g x b,
    ~ has_type g (tm_abs x b) ty_unit
  by { intros g x b h; inversion h}.

Closing Fact ht_abs_inv:
  forall G x body T1 T2,
  has_type G (tm_abs x body) (ty_arrow T1 T2) ->
  has_type (x |-> T1 ; G) body T2
  by {intros G x body T1 T2 h; inversion h; subst; eauto}.



MetaData clean_up_impossibilities.
  Ltac clean_up_impossibilities :=
    match goal with
      | h0: (self__STLC.value (self__STLC.tm_app _ _)) |- _  => destruct (self__STLC.value_not_tm_app _ _ h0)
      | h0: (self__STLC.value (self__STLC.tm_var _ )) |- _  => destruct (self__STLC.value_not_tm_var _ h0)
      | h0: empty _ = Some _ |- _ => inversion h0
      | h0: self__STLC.has_type _ (self__STLC.tm_abs _ _) self__STLC.ty_unit |- _ => destruct (self__STLC.not_ht_abs_unit _ _ _ h0)
      | h0: (self__STLC.step (self__STLC.tm_abs _ _) _) |- _ => destruct (self__STLC.not_step_tm_abs _ _ _ h0)
      | h0: (self__STLC.step (self__STLC.tm_var _) _) |- _ => destruct (self__STLC.not_step_tm_var _ _ h0)
      | h0: (self__STLC.step self__STLC.tm_unit _) |- _ => destruct (self__STLC.not_step_tm_unit _ h0)
      | h0: empty = update _ _ _ |- _ =>
            destruct (empty_not_update h0); eauto
      | h0: update _ _ _ = empty |- _ =>
            symmetry in h0; destruct (empty_not_update h0); eauto
    end.
FEnd clean_up_impossibilities.

Closing Fact value_arrow_type_abs:
  forall t T1 T2,
  value t ->
  has_type empty t (ty_arrow T1 T2) ->
  exists x b, t = tm_abs x b
  by { intros t T1 T2 h1 h2; inversion h1; subst; eauto; inversion h2; subst; eauto }.

Closing Fact value_arrow_type_unit:
  forall t,
  value t ->
  has_type empty t ty_unit ->
  t = tm_unit
  by { intros t h1 h2; inversion h1; subst; eauto; inversion h2; subst; eauto }.

Ltac try_unfold_first := 
  match goal with 
  | [ |- ?h ?t] => try unfold h; try unfold t 
  end.

FInduction progress 
  about has_type
  motive 
  (fun G t T (h : has_type G t T) =>
        G = empty -> (value t) \/ (exists t', step t t')).
FProof.
+  cbn in *; subst; intros G x T h H. subst. inversion h.
+  cbv delta. cbn in *. intros; subst.
right.
forwardALL. clear H0. clear H2.
destruct H1; subst; eauto.
destruct (self__STLC.value_arrow_type_abs _ _ _ H0 __i) as [x' [b HH]]; subst; eauto; destruct_ALL.
eexists. eapply self__STLC.st_app2; eauto.
eexists. eapply self__STLC.st_app1; eauto.
destruct H0 as [t' hh].
eexists. eapply self__STLC.st_app0; eauto.
+ intros; cbn in *. left. eapply  self__STLC.vabs.
+ intros; cbn in *. left. eapply self__STLC.vtunit.
Qed. FEnd progress.

FInduction  subst_lemma
  about has_type
  motive 
  (fun G1 body T2 (h : has_type G1 body T2) =>
  forall G x k T1,
  G1 = (update G x T1) ->
  (forall G', has_type G' k T1) ->
  has_type G (subst body x k) T2).
  FProof.
+ intros; cbn in *. 
  unfold self__STLC.__motiveTsubst_lemma.
  rewrite self__STLC.subst_tm_var_eq.
  unfold self__STLC.substtm_var.
  intros.
  (* frec_eval self__STLC.subst. *)
  (* unfold self__STLC.subst_handler.tm_var. *)
  destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;
try rewrite PeanoNat.Nat.eqb_refl in *; eauto. unfold update in e.
rewrite PeanoNat.Nat.eqb_refl in *; eauto. inversion e; subst; eauto.
rewrite <- PeanoNat.Nat.eqb_neq in n; subst; eauto. 
unfold update in e. rewrite n in *; cbn in *; eauto. eapply self__STLC.ht_var; eauto.
+ intros; cbn in *.
  unfold self__STLC.__motiveTsubst_lemma.
  intros.
  rewrite self__STLC.subst_tm_app_eq.
  unfold self__STLC.substtm_app.
  eapply self__STLC.ht_app;eauto.
+ intros; cbn in *;subst; eauto.
  unfold self__STLC.__motiveTsubst_lemma.
  intros.
  rewrite self__STLC.subst_tm_abs_eq.
  unfold self__STLC.substtm_abs.
  destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;
    try rewrite PeanoNat.Nat.eqb_refl in *; eauto.
  ++ eapply self__STLC.ht_abs; eauto.
     (* here *) clear H.
     rewrite update_shadow in __i ; eauto.
  ++ assert ((x0 =? x) = false) as H0. eapply PeanoNat.Nat.eqb_neq; eauto.
     rewrite H0 in *. eapply self__STLC.ht_abs; eauto.
     eapply H; subst; eauto. eapply update_permute; eauto.
+ intros; cbn in *;subst; eauto. 
  unfold self__STLC.__motiveTsubst_lemma.
  intros.
  rewrite self__STLC.subst_tm_unit_eq.
  unfold self__STLC.substtm_unit.
  eapply self__STLC.ht_unit.
Qed. FEnd subst_lemma  .

FInductive fv : ident -> self__STLC.tm -> Prop :=
  | fv_var : forall x,
        fv x (self__STLC.tm_var x) 
  | fv_app1 : forall x a b,
        fv x a -> fv x (self__STLC.tm_app a b)
  | fv_app2 : forall x a b,
        fv x b -> fv x (self__STLC.tm_app a b)
  | fv_abs :  forall x v body,
        fv x body -> x <> v -> fv x (self__STLC.tm_abs v body).
       
  Closing Fact fv_inv_tm_var:
    forall x x',
      fv x (tm_var x') ->
      x = x' 
    by { intros x x' h; inversion h; subst; eauto }.
  
  Closing Fact fv_inv_tm_app:
    forall x a b,
      fv x (tm_app a b) ->
      fv x a \/ fv x b
    by { intros x a b h; inversion h; subst; eauto }.
  
  Closing Fact fv_inv_tm_unit:
    forall x,
    ~ fv x tm_unit
    by {intros x h; inversion h; subst; eauto}.
  
  Closing Fact fv_inv_tm_abs:
    forall x v body,
      fv x (tm_abs v body) ->
      fv x body /\ x <> v
    by {intros x v body h; repeat split; inversion h; subst; eauto}.

FInduction free_var_in_ctx
  about has_type
  motive (
    fun G t T (h : self__STLC.has_type G t T) =>
    forall x,
    fv x t ->
    exists U, G x = Some U
  ).
FProof. repeat split; repeat (intro; intros); cbn in * .
+ forwards*: self__STLC.fv_inv_tm_var. subst; eauto.
+ unfold self__STLC.__motiveTfree_var_in_ctx. intros.
  forwards*: self__STLC.fv_inv_tm_app.
  destruct_ALL; eauto.
+ unfold self__STLC.__motiveTfree_var_in_ctx. intros.
  forwards*: self__STLC.fv_inv_tm_abs; destruct_ALL; subst; eauto.
forwards*: H; eauto; destruct_ALL; subst; eauto. unfold update in H3.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto.
+ unfold self__STLC.__motiveTfree_var_in_ctx. intros.
  destruct (self__STLC.fv_inv_tm_unit _ H).
Qed. FEnd free_var_in_ctx.

FInduction 
  free_var_matters
  about has_type
  motive 
  (fun G1 t T (h : self__STLC.has_type G1 t T ) =>
  forall G2,
  (forall x,
  self__STLC.fv x t -> G1 x = G2 x) ->
  self__STLC.has_type G2 t T).
FProof.
+ repeat split; repeat (intro; intros); cbn in *; eauto.
  eapply self__STLC.ht_var; eauto. erewrite <- H; eauto. eapply self__STLC.fv_var.
+ repeat split; repeat (intro; intros); cbn in *; eauto.
  eapply self__STLC.ht_app; eauto; eauto using self__STLC.fv_app1,self__STLC.fv_app2.
+ repeat split; repeat (intro; intros); cbn in *; eauto.
  eapply self__STLC.ht_abs; eauto. eapply H; eauto.
  intros; subst; eauto. unfold update. 
  destruct (PeanoNat.Nat.eq_dec x x0); subst; try rewrite PeanoNat.Nat.eqb_refl; subst; eauto. 
  assert ((x =? x0) = false) as hh. eapply PeanoNat.Nat.eqb_neq; eauto.  rewrite hh in *.
  eapply H0; eauto using self__STLC.fv_abs.
+ repeat split; repeat (intro; intros); cbn in *; eauto using self__STLC.ht_unit.
Qed. FEnd free_var_matters.


FLemma weakening_lemma:
      forall k T,
      self__STLC.has_type empty k T ->
      (forall G, self__STLC.has_type G k T).
FProofLemma.
  intros k T h. intros. 
  eapply self__STLC.free_var_matters; try (exact h). intros x H.
  destruct  (self__STLC.free_var_in_ctx _ _ _ h _ H); try self__STLC.clean_up_impossibilities.
Qed. CloseFLemma.
  
FInduction preservation
  about has_type
  motive 
  (fun G t T (h : has_type G t T) =>
  G = empty ->
  forall t',
  step t t' ->
  has_type empty t' T).
FProof.
- repeat split; repeat (intro; intros); cbn in *; 
    try (subst; cbn in *; self__STLC.clean_up_impossibilities).
- repeat split; repeat (intro; intros); cbn in *; 
    try (subst; cbn in *; self__STLC.clean_up_impossibilities).
  (* Case tm_app *) subst; cbn in *. 
  destruct (self__STLC.step_tm_app_inv _ _ _ H2); destruct_ALL; eauto; 
    try eapply self__STLC.ht_app; subst; eauto; try self__STLC.clean_up_impossibilities.
  eapply self__STLC.subst_lemma; eauto. eapply self__STLC.ht_abs_inv; eauto.
intros. eapply self__STLC.weakening_lemma; eauto.
- repeat split; repeat (intro; intros); cbn in *; 
    try (subst; cbn in *; self__STLC.clean_up_impossibilities).
- repeat split; repeat (intro; intros); cbn in *; 
    try (subst; cbn in *; self__STLC.clean_up_impossibilities).
Qed. FEnd preservation.


FLemma preservation2 :
  forall t t',
    self__STLC.steps t t' ->
    forall T,
    has_type empty t T ->
    has_type empty t' T.
FProofLemma.
intros t t' h. induction h; intros; subst; eauto using self__STLC.preservation.
eapply IHh; eauto. eapply self__STLC.preservation; eauto.
Qed. CloseFLemma.
  

FLemma type_safety:
  forall t t' T,
    has_type empty t T ->
    self__STLC.steps t t' ->
    value t' \/ (exists t'', step t' t'').
FProofLemma.
intros.
eapply self__STLC.progress; eauto using self__STLC.preservation2.
Qed. CloseFLemma.

FEnd STLC.

Family STLC_sum extends STLC.
FInductive ty : Set :=
  | ty_sum : ty -> ty -> ty .


FInductive tm : Set :=
  (* sum *)
  | tm_inl : tm -> tm 
  | tm_inr : tm -> tm 
  | tm_case : tm -> ident -> tm -> tm -> tm.

(* Inherit Until Field value. *)

FInductive value : self__STLC_sum.tm -> Prop :=
  | vinl : forall v, value v -> value (self__STLC_sum.tm_inl v)
  | vinr : forall v, value v -> value (self__STLC_sum.tm_inr v).

FInduction _value_not_tm_var.
FProof.
+ intros. apply cheat. (* prec_discriminate self__STLC_sum.tm_prec H0. *)
+ intros. apply cheat. (* prec_discriminate self__STLC_sum.tm_prec H0. *)
Qed. FEnd _value_not_tm_var.



FRecursion subst.

Case tm_inl 
  := (fun a rec_a =>
      fun x t => 
      self__STLC_sum.tm_inl (rec_a x t)).
Case tm_inr 
  := (fun a rec_a =>
      fun x t => 
      self__STLC_sum.tm_inr (rec_a x t)).

Case tm_case
  := (fun cond rec_cond i a rec_a b rec_b =>
      fun x t => 
      if (eqb i x) then 
      self__STLC_sum.tm_case (rec_cond x t) i a b 
      else 
      self__STLC_sum.tm_case (rec_cond x t) i (rec_a x t) (rec_b x t)).

FEnd subst.

(* Inherit Field subst. *)

(* Closing Fact subst_tm_inl :
forall a,
self__STLC_sum.subst (self__STLC_sum.tm_inl a) = self__STLC_sum.subst_handler.tm_inl a (self__STLC_sum.subst a)
by { intros; eauto }.

Closing Fact subst_tm_inr :
forall a,
self__STLC_sum.subst (self__STLC_sum.tm_inr a) = self__STLC_sum.subst_handler.tm_inr a (self__STLC_sum.subst a)
by { intros; eauto }.

Closing Fact subst_tm_case :
forall cond i lb rb,
self__STLC_sum.subst (self__STLC_sum.tm_case cond i lb rb) = self__STLC_sum.subst_handler.tm_case cond (self__STLC_sum.subst cond) i lb (self__STLC_sum.subst lb) rb (self__STLC_sum.subst rb)
by { intros; eauto }. *)



Inherit context.

FInductive step : self__STLC_sum.tm -> self__STLC_sum.tm -> Prop :=
  | st_inl: forall a a',
    step a a' ->
    step (self__STLC_sum.tm_inl a) (self__STLC_sum.tm_inl a')
  | st_inr: forall a a',
    step a a' ->
    step (self__STLC_sum.tm_inr a) (self__STLC_sum.tm_inr a')
  | st_case0: forall c c' i lb rb,
    step c c' ->
    step (self__STLC_sum.tm_case c i lb rb) (self__STLC_sum.tm_case c' i lb rb)
  | st_case1: forall i lb rb v,
    self__STLC_sum.value v ->
    step (self__STLC_sum.tm_case (self__STLC_sum.tm_inl v) i lb rb) (self__STLC_sum.subst lb i v)
  | st_case2: forall i lb rb v,
    self__STLC_sum.value v ->
    step (self__STLC_sum.tm_case (self__STLC_sum.tm_inr v) i lb rb) (self__STLC_sum.subst rb i v).

(* Inherit Until Field has_type. *)

FInductive has_type : self__STLC_sum.context -> self__STLC_sum.tm -> self__STLC_sum.ty -> Prop :=
  | ht_sum0 : forall G t L R,
      has_type G t L ->
      has_type G (self__STLC_sum.tm_inl t) (self__STLC_sum.ty_sum L R) 
  | ht_sum1 : forall G t L R,
      has_type G t R ->
      has_type G (self__STLC_sum.tm_inr t) (self__STLC_sum.ty_sum L R)
  | ht_case : forall G c L R T lb rb i,
      has_type G c (self__STLC_sum.ty_sum L R) ->
      has_type (i |-> L ; G) lb T ->
      has_type (i |-> R ; G) rb T ->
      has_type G (self__STLC_sum.tm_case c i lb rb) T.

(* 
commented out by me
Inherit Until Field progress. *)

Closing Fact value_sum_type_inv:
    forall c L R, 
    value c ->
    has_type empty c (ty_sum L R) ->
    (exists l, c = tm_inl l /\ value l)
    \/ (exists r, c = tm_inr r /\ value r) 
by {
  intros c L R h1 h2;
  inversion h1; subst; eauto;
  inversion h2; subst; eauto
}.

FInduction progress. 
FProof.
+ unfold self__STLC_sum.__motiveTprogress. intros.
  try
(forwardALL; destruct_ALL;
try (left; eauto using self__STLC_sum.vinl, self__STLC_sum.vinr; fail);
try (right; eauto using self__STLC_sum.st_inl, self__STLC_sum.st_inr;fail); fail);(repeat intro;intros).
+ unfold self__STLC_sum.__motiveTprogress. intros.
  try
(forwardALL; destruct_ALL;
try (left; eauto using self__STLC_sum.vinl, self__STLC_sum.vinr; fail);
try (right; eauto using self__STLC_sum.st_inl, self__STLC_sum.st_inr;fail); fail);(repeat intro;intros).
+ unfold self__STLC_sum.__motiveTprogress. intros.
   try
(forwardALL; destruct_ALL;
try (left; eauto using self__STLC_sum.vinl, self__STLC_sum.vinr; fail);
try (right; eauto using self__STLC_sum.st_inl, self__STLC_sum.st_inr;fail); fail);(repeat intro;intros).
  clear H1; clear H0. right.
  forwardALL; destruct_ALL; eauto using self__STLC_sum.st_case0,self__STLC_sum.st_case1,self__STLC_sum.st_case2.
forwards*: self__STLC_sum.value_sum_type_inv; destruct_ALL; subst; eauto using self__STLC_sum.st_case0,self__STLC_sum.st_case1,self__STLC_sum.st_case2.
Qed. FEnd progress.

FInduction subst_lemma.
FProof.
- repeat split; __unfold_ftheorem_motive; (repeat intro;intros); subst.
  rewrite self__STLC_sum.subst_tm_inl_eq.
  unfold self__STLC_sum.substtm_inl.
  eapply self__STLC_sum.ht_sum0;eauto.
- repeat split; __unfold_ftheorem_motive; (repeat intro;intros); subst.
  rewrite self__STLC_sum.subst_tm_inr_eq.
  unfold self__STLC_sum.substtm_inr.
  eapply self__STLC_sum.ht_sum1;eauto.
- (* repeat split; __unfold_ftheorem_motive; (repeat intro;intros); subst. *)
  unfold self__STLC_sum.__motiveTsubst_lemma. intros.
  rewrite self__STLC_sum.subst_tm_case_eq.
  unfold self__STLC_sum.substtm_case.
  (* ht_case *)
  destruct (Nat.eq_dec i x); subst; eauto; try rewrite Nat.eqb_refl; subst.
  eapply self__STLC_sum.ht_case; try rewrite update_shadow in __i0;try rewrite update_shadow in __i1; eauto.
  rewrite <- PeanoNat.Nat.eqb_neq in n; rewrite n. rewrite Nat.eqb_neq in n.
  eapply self__STLC_sum.ht_case; eauto; [try eapply H0 | try eapply H1]; eauto using update_permute.
Qed. FEnd subst_lemma.  

FInductive fv  : ident -> self__STLC_sum.tm -> Prop :=
  | fv_inl : forall x a, 
      fv x a ->
      fv x (self__STLC_sum.tm_inl a)
  | fv_inr : forall x a, 
      fv x a ->
      fv x (self__STLC_sum.tm_inr a)
  | fv_case : forall x c i lb rb,
      fv x c ->
      fv x (self__STLC_sum.tm_case c i lb rb)
  | fv_case1 : forall x c i lb rb,
      fv x lb ->
      i <> x ->
      fv x (self__STLC_sum.tm_case c i lb rb)
  | fv_case2 : forall x c i lb rb,
      fv x rb ->
      i <> x ->
      fv x (self__STLC_sum.tm_case c i lb rb).

Closing Fact fv_inv_tm_inl:
  forall x t, fv x (tm_inl t) -> fv x t
by {intros x t h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_inr:
  forall x t, fv x (tm_inr t) -> fv x t
by {intros x t h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_case:
  forall x c i lb rb,
  fv x (tm_case c i lb rb) -> 
    (fv x c) 
    \/
    (i <> x /\ fv x lb)
    \/
    (i <> x /\ fv x rb)
by { intros x c i lb rb h; inversion h; subst; eauto }.

(* Inherit Until Field free_var_in_ctx. *)
FInduction free_var_in_ctx.
FProof.
- repeat split;
(repeat intro;intros); cbn in *; eauto; subst; eauto;
    eauto using self__STLC_sum.fv_inv_tm_inl, self__STLC_sum.fv_inv_tm_inr, self__STLC_sum.fv_inv_tm_case.
- repeat split;
(repeat intro;intros); cbn in *; eauto; subst; eauto;
    eauto using self__STLC_sum.fv_inv_tm_inl, self__STLC_sum.fv_inv_tm_inr, self__STLC_sum.fv_inv_tm_case.
- repeat split;
(repeat intro;intros); cbn in *; eauto; subst; eauto;
eauto using self__STLC_sum.fv_inv_tm_inl, self__STLC_sum.fv_inv_tm_inr, self__STLC_sum.fv_inv_tm_case.
forwards*: self__STLC_sum.fv_inv_tm_case;
destruct_ALL; subst; eauto. rewrite <- Nat.eqb_neq in H3.
forwards*: H0; destruct_ALL; subst; eauto. unfold update in H5. rewrite H3 in *. eauto.
rewrite <- Nat.eqb_neq in H3.
forwards*: H1; destruct_ALL; subst; eauto. unfold update in H5. rewrite H3 in *. eauto.

Qed. FEnd free_var_in_ctx.

(* Inherit Until Field free_var_matters. *)

FInduction free_var_matters.
FProof.
- repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto using 
self__STLC_sum.ht_sum0,self__STLC_sum.ht_sum1, self__STLC_sum.ht_case, self__STLC_sum.fv_inl,self__STLC_sum.fv_inr.
- repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto using 
                                                                 self__STLC_sum.ht_sum0,self__STLC_sum.ht_sum1, self__STLC_sum.ht_case, self__STLC_sum.fv_inl,self__STLC_sum.fv_inr.
- repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto using 
self__STLC_sum.ht_sum0,self__STLC_sum.ht_sum1, self__STLC_sum.ht_case, self__STLC_sum.fv_inl,self__STLC_sum.fv_inr.
eapply self__STLC_sum.ht_case; eauto using self__STLC_sum.fv_case, self__STLC_sum.fv_case1, self__STLC_sum.fv_case2. 
(*  *)
eapply H0. intros. unfold update. destruct (Nat.eq_dec i x); subst; try rewrite Nat.eqb_refl; eauto. rewrite <- Nat.eqb_neq in n; rewrite n; rewrite Nat.eqb_neq in n. eapply H2; eauto using  self__STLC_sum.fv_case1, self__STLC_sum.fv_case2. 

eapply H1. intros. unfold update. destruct (Nat.eq_dec i x); subst; try rewrite Nat.eqb_refl; eauto. rewrite <- Nat.eqb_neq in n; rewrite n; rewrite Nat.eqb_neq in n. eapply H2; eauto using  self__STLC_sum.fv_case1, self__STLC_sum.fv_case2.
Qed. FEnd free_var_matters.




(* Commented out by me
Inherit Until Field preservation. *)

Closing Fact step_tm_inl_inv:
  forall x y,
  step (tm_inl x) y ->
    (exists x', y = tm_inl x' /\ step x x')
by { intros x y h; inversion h; subst; eauto }.

Closing Fact step_tm_inr_inv:
  forall x y,
  step (tm_inr x) y ->
    (exists x', y = tm_inr x' /\ step x x')
by { intros x y h; inversion h; subst; eauto }.

Closing Fact step_tm_case_inv:
  forall c i lb rb y,
  step (tm_case c i lb rb) y ->
    (exists c', y = tm_case c' i lb rb/\ step c c')
    \/ 
    (exists v, value v /\ c = tm_inl v /\ y = (subst lb i v))
    \/ 
    (exists v, value v /\ c = tm_inr v /\ y = (subst rb i v )) by 
{intros c i lb rb y h; inversion h; subst; eauto;
try (left ;eauto; fail);
try (right; left; eauto; fail);
try (right; right ; eauto; fail)}.

Closing Fact ht_inl_inv:
  forall G x L R,
  has_type G (tm_inl x) (ty_sum L R) ->
  has_type G x L by 
{intros G x L R h; inversion h; subst; eauto}.


Closing Fact ht_inr_inv:
  forall G x L R,
  has_type G (tm_inr x) (ty_sum L R) ->
  has_type G x R by 
{intros G x L R h; inversion h; subst; eauto}.


FInduction preservation.
FProof.
- repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
  forwards*: self__STLC_sum.step_tm_inl_inv; destruct_ALL; subst; eauto using self__STLC_sum.ht_sum0.
- repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
forwards*: self__STLC_sum.step_tm_inr_inv; destruct_ALL; subst; eauto using self__STLC_sum.ht_sum1.
- repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
  forwards*: self__STLC_sum.step_tm_case_inv; destruct_ALL; subst; eauto using self__STLC_sum.ht_case.
eapply self__STLC_sum.subst_lemma; eauto. intros. forwards*: self__STLC_sum.ht_inl_inv; eauto using self__STLC_sum.weakening_lemma.

eapply self__STLC_sum.subst_lemma; eauto. intros. forwards*: self__STLC_sum.ht_inr_inv; eauto using self__STLC_sum.weakening_lemma.
Qed. FEnd preservation.

Time FEnd STLC_sum.
