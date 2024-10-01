(* Require Import Coq.Unicode.Utf8. *)
(*
Field
self__STLC
FScheme*)
Require Import NFPOP.Loader.
Require Import NFPOP.LibTactics.
From Coq Require Import Nat.
Require Import PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Notation ident := nat.

Module STLC_Families.

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
+ intros. prec_discriminate self__STLC.tm_prec H. 
+ intros. prec_discriminate self__STLC.tm_prec H. 
Qed. FEnd _value_not_tm_var .

Field value_not_tm_var : forall i, ~ self__STLC.value (self__STLC.tm_var i) :=
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





(*Field context : Type := partial_map self__STLC.ty.*)
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


(*Field irreducible : tm -> Prop := fun x => forall x', step x x' -> False.*)

Inductive has_type : self__STLC.context -> self__STLC.tm -> self__STLC.ty -> Prop.

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
+ intros; cbn in *. frec_eval self__STLC.subst. 
unfold self__STLC.subst_handler.tm_var. 
destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;
try rewrite PeanoNat.Nat.eqb_refl in *; eauto. unfold update in e.
rewrite PeanoNat.Nat.eqb_refl in *; eauto. inversion e; subst; eauto.
rewrite <- PeanoNat.Nat.eqb_neq in n; subst; eauto. 
unfold update in e. rewrite n in *; cbn in *; eauto. eapply self__STLC.ht_var; eauto.
+ intros; cbn in *. 
frec_eval self__STLC.subst.
subst; eauto. unfold self__STLC.subst_handler.tm_app. 
eapply self__STLC.ht_app;eauto.

+  intros; cbn in *;subst; eauto.
frec_eval self__STLC.subst. unfold self__STLC.subst_handler.tm_abs.
destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;
try rewrite PeanoNat.Nat.eqb_refl; cbn in *; subst; eauto.
++ eapply self__STLC.ht_abs; eauto. rewrite update_shadow in __i; eauto.
++ assert ((x0 =? x) = false) as H0. eapply PeanoNat.Nat.eqb_neq; eauto.
  rewrite H0 in *. eapply self__STLC.ht_abs; eauto.
  eapply H; subst; eauto. eapply update_permute; eauto.

+ intros; cbn in *;subst; eauto. 
frec_eval self__STLC.subst. unfold self__STLC.subst_handler.tm_unit. eapply self__STLC.ht_unit.
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
  about self__STLC.has_type
  motive (
    fun G t T (h : self__STLC.has_type G t T) =>
    forall x,
    fv x t ->
    exists U, G x = Some U
  ).
StartFProofAll. repeat split; repeat (intro; intros); cbn in * .
+ forwards*: self__STLC.fv_inv_tm_var. subst; eauto.
+ forwards*: self__STLC.fv_inv_tm_app. destruct_ALL; eauto.
+ forwards*: self__STLC.fv_inv_tm_abs; destruct_ALL; subst; eauto.
forwards*: H; eauto; destruct_ALL; subst; eauto. unfold update in H3.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto.
+ destruct (self__STLC.fv_inv_tm_unit _ H).
Qed. FEnd free_var_in_ctx.

FInduction 
  free_var_matters
  about self__STLC.has_type
  motive 
  (fun G1 t T (h : self__STLC.has_type G1 t T ) =>
  forall G2,
  (forall x,
  self__STLC.fv x t -> G1 x = G2 x) ->
  self__STLC.has_type G2 t T).
StartFProofAll. repeat split; repeat (intro; intros); cbn in *; eauto using self__STLC.ht_unit.
+ eapply self__STLC.ht_var; eauto. erewrite <- H; eauto. eapply self__STLC.fv_var.
+ eapply self__STLC.ht_app; eauto; eauto using self__STLC.fv_app1,self__STLC.fv_app2.
+ eapply self__STLC.ht_abs; eauto. eapply H; eauto.
intros; subst; eauto. unfold update. 
destruct (PeanoNat.Nat.eq_dec x x0); subst; try rewrite PeanoNat.Nat.eqb_refl; subst; eauto. 
assert ((x =? x0) = false) as hh. eapply PeanoNat.Nat.eqb_neq; eauto.  rewrite hh in *.
eapply H0; eauto using self__STLC.fv_abs.
Qed. FEnd free_var_matters.


  Field weakening_lemma:
      forall k T,
      self__STLC.has_type empty k T ->
      (forall G, self__STLC.has_type G k T).
  FProof.
  intros k T h. intros. 
  eapply self__STLC.free_var_matters; try (exact h). intros x H.
  destruct  (self__STLC.free_var_in_ctx _ _ _ h _ H); try self__STLC.clean_up_impossibilities.
  Qed. FEnd weakening_lemma.
  
FInduction preservation
  about has_type
  motive 
  (fun G t T (h : has_type G t T) =>
  G = empty ->
  forall t',
  step t t' ->
  has_type empty t' T).
StartFProofAll. repeat split; repeat (intro; intros); cbn in *; 
try (subst; cbn in *; self__STLC.clean_up_impossibilities).
(* Case tm_app *) subst; cbn in *. 
destruct (self__STLC.step_tm_app_inv _ _ _ H2); destruct_ALL; eauto; 
try eapply self__STLC.ht_app; subst; eauto; try self__STLC.clean_up_impossibilities.
eapply self__STLC.subst_lemma; eauto. eapply self__STLC.ht_abs_inv; eauto.
intros. eapply self__STLC.weakening_lemma; eauto.
Qed. FEnd preservation.


Field preservation2 :
  forall t t',
    self__STLC.steps t t' ->
    forall T,
    has_type empty t T ->
    has_type empty t' T.
FProof.
intros t t' h. induction h; intros; subst; eauto using self__STLC.preservation.
eapply IHh; eauto. eapply self__STLC.preservation; eauto.
Qed. FEnd preservation2.
  

Field type_safety:
  forall t t' T,
    has_type empty t T ->
    self__STLC.steps t t' ->
    value t' \/ (exists t'', step t' t'').
FProof.
intros. eapply self__STLC.progress; eauto using self__STLC.preservation2.
Qed. FEnd type_safety.

FEnd STLC.

Family STLC_bool extends STLC.
FInductive ty : Set :=
  | ty_bool : ty.


FInductive tm : Set :=
  | tm_true : tm 
  | tm_false : tm 
  | tm_if : tm -> tm -> tm -> tm.

(* Inherit Until Field value. *)

FInductive value : self__STLC_bool.tm -> Prop :=
  | vtrue : value (self__STLC_bool.tm_true)
  | vfalse : value (self__STLC_bool.tm_false).

FInduction _value_not_tm_var.
FProof.
+ intros. prec_discriminate self__STLC_bool.tm_prec H.
+ intros. prec_discriminate self__STLC_bool.tm_prec H.
Qed. FEnd _value_not_tm_var.

(* Inherit Field value_not_tm_app. *)

FRecursion subst.
Case tm_true 
  := (fun x t => tm_true).

Case tm_false 
  := (fun x t => tm_false).

Case tm_if 
  := (fun cond rec_cond a rec_a b rec_b =>
      fun x t => 
    tm_if (rec_cond x t) (rec_a x t) (rec_b x t)).

FEnd subst.


(* Closing Fact subst_tm_true :
self__STLC_bool.subst self__STLC_bool.tm_true = self__STLC_bool.subst_handler.tm_true
by { intros; eauto }.

Closing Fact subst_tm_false :
self__STLC_bool.subst self__STLC_bool.tm_false = self__STLC_bool.subst_handler.tm_false
by { intros; eauto }.

Closing Fact subst_tm_if :
  forall c a b,
self__STLC_bool.subst (self__STLC_bool.tm_if c a b) = 
  self__STLC_bool.subst_handler.tm_if c (self__STLC_bool.subst c) a (self__STLC_bool.subst a) b (self__STLC_bool.subst b)
  by { intros; eauto }. *)



FInductive step : self__STLC_bool.tm -> self__STLC_bool.tm -> Prop :=
  | st_if0 : forall c c' a b,
    (step c c') -> (step (self__STLC_bool.tm_if c a b) (self__STLC_bool.tm_if c' a b)) 
  | st_if1 : forall a b,
    (step (self__STLC_bool.tm_if self__STLC_bool.tm_true a b) a)
  | st_if2 : forall a b,
    (step (self__STLC_bool.tm_if self__STLC_bool.tm_false a b) b).


Closing Fact not_step_tm_true:
  forall x',
    ~ step tm_true x' 
  by { intros x' h; inversion h }.
Closing Fact not_step_tm_false:
  forall x',
    ~ step tm_false x' 
  by { intros x' h; inversion h }.

Closing Fact step_tm_if_inv:
  forall c a b t,
  step (tm_if c a b) t ->
    (exists c', (step c c'
           /\ t = (tm_if c' a b)))
    \/ (c = tm_true /\ t = a)
    \/ (c = tm_false /\ t = b)
  by {
    intros c a b t h; inversion h; subst; eauto;
    try (left; repeat eexists; subst; eauto;fail);
    try (right; left; subst; eauto;fail);
    try (right; right; subst; eauto;fail)}.



FInductive has_type : self__STLC_bool.context -> self__STLC_bool.tm -> self__STLC_bool.ty -> Prop :=
  | ht_true : forall G,
      has_type G self__STLC_bool.tm_true self__STLC_bool.ty_bool 
  | ht_false : forall G,
      has_type G self__STLC_bool.tm_false self__STLC_bool.ty_bool
  | ht_if : forall G c a b T,
      has_type G c self__STLC_bool.ty_bool ->
      has_type G a T ->
      has_type G b T ->
      has_type G (self__STLC_bool.tm_if c a b) T.

Inherit Field clean_up_impossibilities.

MetaData clean_up_impossibilities2.

Ltac clean_up_impossibilities2 :=
  self__STLC_bool.clean_up_impossibilities ||
  match goal with
    | h0: (self__STLC_bool.step self__STLC_bool.tm_true _) |- _ => destruct (self__STLC_bool.not_step_tm_true _ h0)
    | h0: (self__STLC_bool.step self__STLC_bool.tm_false _) |- _ => destruct (self__STLC_bool.not_step_tm_false _ h0)
  end.
FEnd clean_up_impossibilities2.


(* Inherit Field value_arrow_type_unit. *)

Closing Fact value_bool_type_true_false:
  forall t,
  value t ->
  has_type empty t (ty_bool) ->
  (t = tm_true \/ t = tm_false)
by {
  intros t h h1;
  inversion h; subst; eauto; inversion h1; subst; eauto;
  try (left; eauto; fail);
  try (right; eauto; fail)}.

FInduction progress. 
StartFProofAll. repeat split; 
(repeat intro; intros); cbn in *; subst; eauto; try (left; eauto using self__STLC_bool.vtrue, self__STLC_bool.vfalse; fail).
(* case tm_if *) right.
forwards*: H; subst; eauto. destruct_ALL; subst; eauto using self__STLC_bool.st_if0.
forwards*: self__STLC_bool.value_bool_type_true_false. destruct_ALL; subst; eauto using self__STLC_bool.st_if1,self__STLC_bool.st_if2.
Qed. FEnd progress.


FInduction subst_lemma.
StartFProofAll. repeat split; repeat (intro; intros); cbn in *; eauto; subst; eauto; frec_eval self__STLC_bool.subst;  eauto using self__STLC_bool.ht_true, self__STLC_bool.ht_false, self__STLC_bool.ht_if.
Qed. FEnd subst_lemma.

FInductive fv : ident -> self__STLC_bool.tm -> Prop :=
| fv_if0 : forall x c a b,
    fv x c -> fv x (self__STLC_bool.tm_if c a b)
| fv_if1 : forall x c a b,
    fv x a -> fv x (self__STLC_bool.tm_if c a b)
| fv_if2 : forall x c a b,
    fv x b -> fv x (self__STLC_bool.tm_if c a b).


Closing Fact fv_inv_tm_true:
  forall x, ~ fv x tm_true
by {intros x h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_false:
  forall x, ~ fv x tm_false
by {intros x h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_iff:
forall x c a b,
  fv x (tm_if c a b) ->
  fv x c \/ fv x a \/ fv x b
by { intros x c a b h; inversion h; subst; eauto }.

(* Inherit Field fv_inv_tm_abs. *)

FInduction free_var_in_ctx.
StartFProofAll. repeat split;
repeat (intro; intros); cbn in *; eauto; subst; eauto; 
try ((edestruct (self__STLC_bool.fv_inv_tm_true); eauto; fail) || edestruct (self__STLC_bool.fv_inv_tm_false); eauto; fail).
forwards*: self__STLC_bool.fv_inv_tm_iff; destruct_ALL; eauto.
Qed. FEnd free_var_in_ctx.

FInduction free_var_matters.
StartFProofAll. repeat split; (repeat intro; intros); cbn in *; eauto; subst; eauto; eauto using self__STLC_bool.ht_true, self__STLC_bool.ht_false. 
(* case tm_if *) eapply self__STLC_bool.ht_if;
eauto using self__STLC_bool.fv_if0, self__STLC_bool.fv_if1, self__STLC_bool.fv_if2.
Qed. FEnd free_var_matters.

(* Inherit Field weakening_lemma. *)

FInduction preservation.
StartFProofAll. repeat split; (repeat intro; intros); cbn in *; eauto; subst; eauto; try self__STLC_bool.clean_up_impossibilities2.
(* case tm_if *) forwards*: self__STLC_bool.step_tm_if_inv; destruct_ALL; subst; eauto using self__STLC_bool.ht_if.
Qed. FEnd preservation.

FEnd STLC_bool.

Family STLC_prod extends STLC.
FInductive ty : Set :=
  | ty_prod : ty -> ty -> ty.



FInductive tm : Set :=
  | tm_prod : tm -> tm -> tm  
  | tm_pi1 : tm -> tm  
  | tm_pi2 : tm -> tm.

(* Inherit Until Field value. *)

FInductive value : self__STLC_prod.tm -> Prop :=
  | vprod : forall a b, value a -> value b -> value (self__STLC_prod.tm_prod a b ).

FInduction _value_not_tm_var.
FProof.
+ intros. prec_discriminate self__STLC_prod.tm_prec H1.
Qed. FEnd _value_not_tm_var.

(* Inherit Field value_not_tm_app. *)

Closing Fact vprod_inv:
  (forall a b,
  value (tm_prod a b) -> value a /\ value b)
  by {intros a b h; 
  repeat split; 
  inversion h; subst; eauto}.

FRecursion subst.
Case tm_pi1 
  := (fun a rec_a x t => tm_pi1 (rec_a x t)).

Case tm_pi2 
  := (fun a rec_a x t => tm_pi2 (rec_a x t)).

Case tm_prod 
  := (fun a rec_a b rec_b x t => 
      tm_prod (rec_a x t) (rec_b x t)).

FEnd subst.

(* Inherit Field subst. *)

(* Closing Fact subst_tm_pi1 : forall a, 
self__STLC_prod.subst (self__STLC_prod.tm_pi1 a) = 
self__STLC_prod.subst_handler.tm_pi1 a (self__STLC_prod.subst a) 
by { intros; eauto }.

Closing Fact subst_tm_pi2 : forall a, 
self__STLC_prod.subst (self__STLC_prod.tm_pi2 a) = 
self__STLC_prod.subst_handler.tm_pi2 a (self__STLC_prod.subst a) 
by { intros; eauto }.

Closing Fact subst_tm_prod :
  forall a b,
  self__STLC_prod.subst (self__STLC_prod.tm_prod a b) = 
  self__STLC_prod.subst_handler.tm_prod a (self__STLC_prod.subst a) b (self__STLC_prod.subst b) 
by { intros; eauto }. *)



(* Inherit Field context. *)

FInductive step : self__STLC_prod.tm -> self__STLC_prod.tm -> Prop :=
  | st_prod0 : forall a a' b,
    (step a a') -> (step (self__STLC_prod.tm_prod a b) (self__STLC_prod.tm_prod a' b)) 
  | st_prod1 : forall a b b',
    self__STLC_prod.value a ->
    (step b b') -> (step (self__STLC_prod.tm_prod a b) (self__STLC_prod.tm_prod a b')) 
  | st_pi10 : forall a a',
    step a a' ->
    (step (self__STLC_prod.tm_pi1 a) (self__STLC_prod.tm_pi1 a')) 
  | st_pi11 : forall a b,
    self__STLC_prod.value a ->
    self__STLC_prod.value b ->
    (step (self__STLC_prod.tm_pi1 (self__STLC_prod.tm_prod a b)) a) 
  | st_pi20 : forall a a',
    step a a' ->
    (step (self__STLC_prod.tm_pi2 a) (self__STLC_prod.tm_pi2 a')) 
  | st_pi21 : forall a b,
    self__STLC_prod.value a ->
    self__STLC_prod.value b ->
    (step (self__STLC_prod.tm_pi2 (self__STLC_prod.tm_prod a b)) b).




Closing Fact st_prod_inv:
    forall a b c,
    step (tm_prod a b) c -> 
      (exists a', step a a' /\ c = tm_prod a' b)
      \/ (exists b', value a /\ step b b' /\ c = tm_prod a b') by 
  {intros a b c h0;
    inversion h0; subst; eauto;
    try (left; repeat eexists; repeat split; eauto; fail);
    try (right; repeat eexists; repeat split; eauto; fail); auto}.
  
Closing Fact st_pi1_inv:
    forall a b,
    self__STLC_prod.step (tm_pi1 a) b -> 
      (exists a', step a a' /\ b = tm_pi1 a')
      \/ (exists x y, value x /\ value y /\ a = tm_prod x y /\ x = b)
by {intros a b h0; 
    inversion h0; subst; eauto;
    try (left; repeat eexists; repeat split; eauto; fail);
    try (right; repeat eexists; repeat split; eauto; fail); auto}.

  
Closing Fact st_pi2_inv:
    forall a b,
    step (tm_pi2 a) b -> 
      (exists a', step a a' /\ b = tm_pi2 a')
      \/ (exists x y, value x /\ value y /\ a = tm_prod x y /\ y = b)
by {intros a b h0; 
    inversion h0; subst; eauto;
    try (left; repeat eexists; repeat split; eauto; fail);
    try (right; repeat eexists; repeat split; eauto; fail); auto}.


(* Inherit Field irreducible. *)


FInductive has_type : self__STLC_prod.context -> self__STLC_prod.tm -> self__STLC_prod.ty -> Prop :=
  | ht_pi1 : forall G t A B,
      has_type G t (self__STLC_prod.ty_prod A B) ->
      has_type G (self__STLC_prod.tm_pi1 t) A
  | ht_pi2 : forall G t A B,
      has_type G t (self__STLC_prod.ty_prod A B) ->
      has_type G (self__STLC_prod.tm_pi2 t) B
  | ht_prod : forall G a b A B,
      has_type G a A ->
      has_type G b B ->
      has_type G (self__STLC_prod.tm_prod a b) (self__STLC_prod.ty_prod A B).

(* Inherit Field value_arrow_type_unit. *)

(* Canonical form *)
Closing Fact value_prod_type_inv:
  forall t A B,
  value t ->
  has_type empty t (ty_prod A B) ->
  exists a b, t = tm_prod a b /\ value a /\ value b /\ has_type empty a A /\ has_type empty b B
by { intros t A B h0 h1; inversion h1; subst; eauto;
     inversion h0; subst; eauto; repeat eexists; repeat split; eauto }.

FInduction progress. 
FProof. 
+ intros G t A B h0 h1 h2; cbn in *; eauto; subst; eauto. 
  destruct (h1 eq_refl); right;
  [forwards*: self__STLC_prod.value_prod_type_inv; 
    destruct_ALL;
    subst; 
    eauto
    |  destruct_ALL
  ]; eauto using self__STLC_prod.st_pi10, self__STLC_prod.st_pi11.
+  intros G t A B h0 h1 h2;intros; cbn in *; subst;eauto. 
destruct (h1 eq_refl); right;
[forwards*: self__STLC_prod.value_prod_type_inv; 
  destruct_ALL;
  subst; 
  eauto
  |  destruct_ALL
]; eauto using self__STLC_prod.st_pi20, self__STLC_prod.st_pi21.

+  intros G a b A B h0 h1 h2 h3 _h4; cbn in *; subst; eauto.
destruct (h1 eq_refl); 
destruct (h3 eq_refl);
  eauto using self__STLC_prod.vprod;
destruct_ALL; 
try (right; repeat eexists; eauto using self__STLC_prod.st_prod0, self__STLC_prod.st_prod1 ; fail).

Qed. FEnd progress.


FInduction subst_lemma.
StartFProofAll. repeat split; 
(repeat intro; intros); cbn in *; eauto; subst; eauto; frec_eval self__STLC_prod.subst;
eauto using self__STLC_prod.ht_pi1, self__STLC_prod.ht_pi2, self__STLC_prod.ht_prod.
Qed. FEnd subst_lemma.

FInductive fv : ident -> self__STLC_prod.tm -> Prop :=
| fv_prod0 : forall x a b,
    fv x a -> fv x (self__STLC_prod.tm_prod a b)
| fv_prod1 : forall x a b,
    fv x b -> fv x (self__STLC_prod.tm_prod a b)
| fv_pi1 : forall x a,
    fv x a -> fv x (self__STLC_prod.tm_pi1 a)
| fv_pi2 : forall x a,
    fv x a -> fv x (self__STLC_prod.tm_pi2 a).


Closing Fact fv_inv_tm_prod:
forall x a b,
fv x (tm_prod a b) ->
fv x a \/ fv x b
by {intros x a b h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_pi1:
forall x a,
fv x (tm_pi1 a) ->
fv x a
by {intros x a h; inversion h; subst; eauto}.


Closing Fact fv_inv_tm_pi2:
forall x a,
fv x (tm_pi2 a) ->
fv x a
by {intros x a h; inversion h; subst; eauto}.



(* Inherit Field fv_inv_tm_abs. *)

FInduction free_var_in_ctx.
StartFProofAll. repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto. 
+ forwards* : self__STLC_prod.fv_inv_tm_pi1; destruct_ALL; eauto.
+ forwards* : self__STLC_prod.fv_inv_tm_pi2; destruct_ALL; eauto.
+ forwards* : self__STLC_prod.fv_inv_tm_prod; destruct_ALL; eauto.
Qed. FEnd free_var_in_ctx.


FInduction free_var_matters.
StartFProofAll. repeat split;
(repeat intro;intros); cbn in *; eauto; subst; 
eauto using self__STLC_prod.ht_pi1, self__STLC_prod.fv_pi1, self__STLC_prod.ht_pi2, self__STLC_prod.fv_pi2.
(* Case tm_prod *) eapply self__STLC_prod.ht_prod; eauto using self__STLC_prod.fv_prod0, self__STLC_prod.fv_prod1.
Qed. FEnd free_var_matters.


(* Inherit Field weakening_lemma. *)

Closing Fact inject_tm_prod:
  forall a b c d,
  tm_prod a b = tm_prod c d ->
  a = c /\ b = d
by {intros a b c d h; inversion h; subst; eauto}.

FInduction preservation.
FProof.
+ intros G t A B H H0 H1 t' H2; intros; cbn in *; eauto; subst; eauto. 
forwards*: self__STLC_prod.st_pi1_inv; destruct_ALL; 
eauto using (H0 eq_refl),  self__STLC_prod.ht_pi1.
forwards*: (self__STLC_prod.vprod _ _ H1 H3) .
forwards*: (self__STLC_prod.value_prod_type_inv _ _ _ H4 H); destruct_ALL; eauto.
forwards*: self__STLC_prod.inject_tm_prod; destruct_ALL; subst; eauto.

+ intros G t A B H H0 H1 t' H2; intros; cbn in *; eauto; subst; eauto. 
forwards*: self__STLC_prod.st_pi2_inv; destruct_ALL; 
eauto using (H0 eq_refl),  self__STLC_prod.ht_pi2.
forwards*: (self__STLC_prod.vprod _ _ H1 H3) .
forwards*: (self__STLC_prod.value_prod_type_inv _ _ _ H4 H); destruct_ALL; eauto.
forwards*: self__STLC_prod.inject_tm_prod; destruct_ALL; subst; eauto.
+  intros G a b A B h0 h1 h2 h3 h4 t' h5; cbn in *; eauto; subst; eauto.
forwards*: self__STLC_prod.st_prod_inv; destruct_ALL; eauto.
forwards*: (h1 eq_refl); eauto using self__STLC_prod.ht_prod.
forwards*: (h3 eq_refl); eauto using self__STLC_prod.ht_prod.
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
  | tm_case : tm -> ident -> tm -> tm -> tm.

(* Inherit Until Field value. *)

FInductive value : self__STLC_sum.tm -> Prop :=
  | vinl : forall v, value v -> value (self__STLC_sum.tm_inl v)
  | vinr : forall v, value v -> value (self__STLC_sum.tm_inr v).

FInduction _value_not_tm_var.
FProof.
+ intros. prec_discriminate self__STLC_sum.tm_prec H0.
+ intros. prec_discriminate self__STLC_sum.tm_prec H0.
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



Inherit Field context.

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

Inherit Until Field progress.

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
StartFProofAll.
repeat split; __unfold_ftheorem_motive; (repeat intro;intros); 
subst; eauto; try
(forwardALL; destruct_ALL;
try (left; eauto using self__STLC_sum.vinl, self__STLC_sum.vinr; fail);
try (right; eauto using self__STLC_sum.st_inl, self__STLC_sum.st_inr;fail); fail);(repeat intro;intros).
(* tm_case *)
clear H1; clear H0.
right.
forwardALL; destruct_ALL; eauto using self__STLC_sum.st_case0,self__STLC_sum.st_case1,self__STLC_sum.st_case2.
forwards*: self__STLC_sum.value_sum_type_inv; destruct_ALL; subst; eauto using self__STLC_sum.st_case0,self__STLC_sum.st_case1,self__STLC_sum.st_case2.

Qed. FEnd progress.


FInduction subst_lemma.
StartFProofAll. repeat split; __unfold_ftheorem_motive; (repeat intro;intros); subst; frec_eval self__STLC_sum.subst; eauto using self__STLC_sum.ht_sum0, self__STLC_sum.ht_sum1, self__STLC_sum.ht_case; cbn in *; eauto.
(* ht_case *)
unfold self__STLC_sum.subst_handler.tm_case.
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
StartFProofAll. repeat split;
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
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto using 
self__STLC_sum.ht_sum0,self__STLC_sum.ht_sum1, self__STLC_sum.ht_case, self__STLC_sum.fv_inl,self__STLC_sum.fv_inr.

eapply self__STLC_sum.ht_case; eauto using self__STLC_sum.fv_case, self__STLC_sum.fv_case1, self__STLC_sum.fv_case2. 
(*  *)
eapply H0. intros. unfold update. destruct (Nat.eq_dec i x); subst; try rewrite Nat.eqb_refl; eauto. rewrite <- Nat.eqb_neq in n; rewrite n; rewrite Nat.eqb_neq in n. eapply H2; eauto using  self__STLC_sum.fv_case1, self__STLC_sum.fv_case2. 

eapply H1. intros. unfold update. destruct (Nat.eq_dec i x); subst; try rewrite Nat.eqb_refl; eauto. rewrite <- Nat.eqb_neq in n; rewrite n; rewrite Nat.eqb_neq in n. eapply H2; eauto using  self__STLC_sum.fv_case1, self__STLC_sum.fv_case2.
Qed. FEnd free_var_matters.




Inherit Until Field preservation.

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
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
forwards*: self__STLC_sum.step_tm_inl_inv; destruct_ALL; subst; eauto using self__STLC_sum.ht_sum0.
forwards*: self__STLC_sum.step_tm_inr_inv; destruct_ALL; subst; eauto using self__STLC_sum.ht_sum1.
forwards*: self__STLC_sum.step_tm_case_inv; destruct_ALL; subst; eauto using self__STLC_sum.ht_case.
eapply self__STLC_sum.subst_lemma; eauto. intros. forwards*: self__STLC_sum.ht_inl_inv; eauto using self__STLC_sum.weakening_lemma.

eapply self__STLC_sum.subst_lemma; eauto. intros. forwards*: self__STLC_sum.ht_inr_inv; eauto using self__STLC_sum.weakening_lemma.
Qed. FEnd preservation.

Time FEnd STLC_sum.

Family STLC_fix extends STLC.


(* Inherit Until Field tm. *)
FInductive tm : Set :=
  | tm_fix : ident -> tm  -> tm.



(* Inherit Until Field subst_handler. *)

FRecursion subst.

Case tm_fix
  := (fun s body rec_body => 
    fun x t => 
    if (eqb x s) 
    then (self__STLC_fix.tm_fix s body)
    else (self__STLC_fix.tm_fix s (rec_body x t))).

FEnd subst.




(* Inherit Field context. *)

FInductive step : self__STLC_fix.tm -> self__STLC_fix.tm -> Prop :=
  | st_fix : forall i body, 
    step (self__STLC_fix.tm_fix i body) (self__STLC_fix.subst body i (self__STLC_fix.tm_fix i body)).


FInductive has_type : (partial_map self__STLC_fix.ty) -> self__STLC_fix.tm -> self__STLC_fix.ty -> Prop :=
  | ht_fix : forall G x body T,
  has_type (x |-> T; G) body T ->
  has_type G (self__STLC_fix.tm_fix x body) T.



(* Closing Fact value_fix_type_inv:
  forall t i T,
  self__STLC_fix.value t ->
  self__STLC_fix.has_type empty t (self__STLC_fix.ty_fix i T) ->
  (exists t', t = self__STLC_fix.tm_fold t' /\ self__STLC_fix.value t')
by {
  intros t i T h h1;
  inversion h; subst; eauto; inversion h1; subst; eauto}.*)

FInduction progress. 
StartFProofAll. 
repeat split; (repeat intro;intros); subst; eauto.

try (right; eauto using self__STLC_fix.st_fix;fail).
Qed. FEnd progress. 



FInduction subst_lemma.
StartFProofAll. repeat split; (repeat intro;intros); subst; frec_eval self__STLC_fix.subst; eauto using self__STLC_fix.ht_fix.  
unfold self__STLC_fix.subst_handler.tm_fix.
destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;try rewrite PeanoNat.Nat.eqb_refl; cbn in *; subst; eauto.
+ eapply self__STLC_fix.ht_fix; eauto. erewrite <- update_shadow; eauto.
+   assert ((x0 =? x) = false) as H0. eapply PeanoNat.Nat.eqb_neq; eauto.
  rewrite H0 in *. eapply self__STLC_fix.ht_fix; eauto.
  eapply H; subst; eauto. eapply update_permute; eauto. 

Qed. FEnd subst_lemma.  

FInductive fv  : ident -> self__STLC_fix.tm -> Prop :=
| fv_fix :  forall x v body,
fv x body -> x <> v -> fv x (self__STLC_fix.tm_fix v body).


Closing Fact fv_inv_tm_fix:
forall x v body,
fv x (tm_fix v body) ->
fv x body /\ x <> v
by {intros x v body h; repeat split; inversion h; subst; eauto}.




FInduction free_var_in_ctx.
StartFProofAll. repeat split;
(repeat intro;intros); cbn in *; eauto; subst; eauto;
eauto using self__STLC_fix.fv_inv_tm_fix. 
destruct (self__STLC_fix.fv_inv_tm_fix _ _ _ H0); eauto.
forwards: (H x0); destruct_ALL; eauto. unfold update in H3.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto.

Qed. FEnd free_var_in_ctx.



FInduction free_var_matters.
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
eapply  self__STLC_fix.ht_fix; eauto. unfold update in *. eapply H; eauto. intros.
destruct (Nat.eq_dec x x0);subst; simpl; eauto; try discriminate; try contradiction. 
rewrite Nat.eqb_refl; eauto.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto. eapply H0; eauto using  self__STLC_fix.fv_fix.

Qed. FEnd free_var_matters.




Closing Fact step_tm_fix_inv:
  forall i body y,
  step (tm_fix i body) y ->
    (y = subst body i (tm_fix i body))
by { intros i body y h; inversion h; subst; eauto }. 


(* Closing Fact step_tm_unfold_inv:
  forall x y,
  self__STLC_fix.step (self__STLC_fix.tm_unfold x) y ->
    (exists x', y = self__STLC_fix.tm_unfold x' /\ self__STLC_fix.step x x') \/ 
    (exists v, x = self__STLC_fix.tm_fold v /\ self__STLC_fix.value v /\ y = v)
by { intros x y h; inversion h; subst; eauto }. *)

Closing Fact ht_fix_inv:
forall G i body T,
has_type G (tm_fix i body) T ->
has_type (i |-> T ; G) body T
by {intros G i body T h; inversion h; subst; eauto}.

FInduction preservation.
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
forwards*: self__STLC_fix.step_tm_fix_inv; destruct_ALL; subst.
eapply self__STLC_fix.subst_lemma; intros; eauto.
eapply self__STLC_fix.weakening_lemma; intros; eauto.

eauto using self__STLC_fix.ht_fix.

Qed. FEnd preservation.

FEnd STLC_fix.

(* each four statement below is a piece together
    the current plugin implementation requires a lot of memory
    so I cannot just run all 12 statements together
  In my machine I can run 4 statements together, 
    so I group them into three groups
    *)

Family STLC_bool_prod extends STLC 
    using STLC_bool using STLC_prod.

Family STLC_bool_prod_sum extends STLC 
    using STLC_sum using STLC_bool_prod.

Family STLC_bool_prod_sum_fix extends STLC 
    using STLC_bool_prod_sum using STLC_fix.


Family STLC_bool_prod_fix extends STLC 
    using STLC_bool_prod using STLC_fix.

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


Print STLC_bool_prod_sum_fix.

End STLC_Families.
