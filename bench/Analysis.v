Require Import NFPOP.Loader.
Require Import NFPOP.LibTactics.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Equalities Orders.
Require Import FSets FMaps.
Require Import Coq.FSets.FMapWeakList.
Require Import String.

From Coq Require Import Nat.
Require Import Coq.Init.Datatypes.

Import Notations.
Import ListNotations.

Module Analysis_showcase.

Definition ident := nat.

Axiom non_implement : forall {T : Type}, T.

Ltac destruct_ALL :=
  repeat
    match goal with
    | [h : _ \/ _ |- _ ] => destruct h; subst; eauto
    | [h : _ + _ |- _ ] => destruct h; subst; eauto
    | [h : _ * _ |- _ ] => destruct h; subst; eauto
    | [h : _ /\ _ |- _ ] => destruct h; subst; eauto
    | [h : exists _ , _ |- _ ] => destruct h; subst; eauto
    | [h : {_ & _} |- _ ] => destruct h; subst; eauto
    | [h : {_ & _ & _} |- _ ] => destruct h; subst; eauto
    | [h : Some _ = Some _ |- _] => inversion h; subst; eauto
    | [h : {_} + {_} |- _] => destruct h; subst; eauto
    end.

Module Type LATTICE.

Parameter t : Type.
Parameter join : t -> t -> t.
Parameter le : t -> t -> Prop.
Parameter le_refl : forall x, le x x.
Parameter le_trans : forall x y z, le x y -> le y z -> le x z.
Parameter join_le_left:
  forall x y, le x (join x y).
Parameter join_le_right:
  forall x y, le y (join x y).

Parameter join_monoton:
  forall x y l,
    le x y ->
    le (join l x) (join l y).

Parameter le_antisymm :
  forall x y,
    le x y ->
    le y x ->
    x = y.
End LATTICE.

Module Type StrictDecidableType (E : DecidableType).
Parameter streq :
  E.eq  = eq.
End StrictDecidableType.

Module Map_LATTICE (E:DecidableType) (SE : StrictDecidableType E) (L : LATTICE).

Module M := FMapWeakList.Make(E).

Module MProp := WProperties_fun E M.
Module MFact := WFacts_fun E M.

Include SE.

Definition t := M.t L.t.

Definition le (m1 : t) (m2 : t) :=
  forall k v,
  M.MapsTo k v m1 ->
  exists v', M.MapsTo k v' m2 /\ L.le v v'.

Axiom Equal_as_quotient:
  forall (x y : t),
    M.Equal x y <-> x = y.

Lemma Map_to_unique:
  forall k v0 v1 (x : t),
    M.MapsTo k v0 x ->
    M.MapsTo k v1 x ->
     v0 = v1.
  intros. forwards*: M.find_1. clear H0.
  forwards*: M.find_1. clear H.
  rewrite H1 in *. injection H0; subst; eauto.
Qed.

Ltac unify_map_to :=
  match goal with
  | [H : M.MapsTo ?k _ ?m, H1 : M.MapsTo ?k _ ?m |- _] =>
    forwards*: (Map_to_unique _ _ _ _ H H1);subst; clear H1
  end.

Lemma le_antisymm :
  forall x y,
  le x y ->
  le y x ->
  x = y.

unfold le. intros x y H H0.
rewrite <- Equal_as_quotient. intro k.
destruct (M.find (elt:=L.t) k x) eqn:heq1.
forwards*: M.find_2.
forwards*: H. destruct_ALL.
forwards*: H0. destruct_ALL.
unify_map_to.
forwards*: L.le_antisymm; subst; eauto. symmetry. eauto using M.find_1.
destruct (M.find (elt:=L.t) k y) eqn:heq2; eauto.
forwards*: M.find_2.
forwards*: H0. destruct_ALL.
forwards*: M.find_1. rewrite heq1 in *; try discriminate.
Qed.


Theorem le_refl:
  forall x,
    le x x.
  unfold le. intros. eexists. eauto using L.le_refl.
Qed.

Theorem le_trans : forall x y z, le x y -> le y z -> le x z.
unfold le. intros x y z h1 h2. intros.
forwards*: h1; destruct_ALL.
forwards*: h2; destruct_ALL.
eexists; eauto using L.le_trans.
Qed.

(* Print M. *)

Definition single_join (k : M.key) (v : L.t) (m : M.t L.t)  : M.t L.t :=
  match M.find k m with
  | None => M.add k v m
  | Some v' => M.add k (L.join v v') m
  end.

Lemma find_single_join_neq :
  forall x k v m,
  x <> k ->
  M.find x (single_join k v m) = M.find x m.
  intros. unfold single_join.
  destruct (M.find (elt:=L.t) k m) eqn:heq;
  rewrite MFact.add_neq_o; eauto; rewrite streq; eauto.
Qed.




Definition Ljoin' (l : L.t) (r : option L.t) : L.t :=
  match r with
  | Some r => L.join l r
  | None => l
  end.
Lemma find_single_join_eq :
  forall k v m ,
  M.find k (single_join k v m) = Some (Ljoin' v (M.find k m)).
intros. unfold single_join.
destruct (M.find (elt:=L.t) k m) eqn:heq;
rewrite MFact.add_eq_o; eauto.
Qed.

Theorem Eeqdec:
  forall (x y : E.t),
  {x = y} + {x <> y}.
generalize (E.eq_dec). intros.
rewrite streq in *. eauto.
Qed.

(* Print MProp.map_induction. *)
Lemma single_join_commutative:
  forall a (k0 k' : E.t) (e e' : L.t),
  ~ E.eq k0 k' ->
  single_join k0 e (single_join k' e' a) =
  single_join k' e' (single_join k0 e a).
  rewrite streq.
  intros.
  rewrite <- Equal_as_quotient. intro k.
  destruct (Eeqdec k k0) eqn:heq1;
  destruct (Eeqdec k k') eqn:heq2; subst; eauto; try contradiction.
  + rewrite find_single_join_eq. rewrite find_single_join_neq; eauto.
  rewrite find_single_join_neq; eauto. rewrite find_single_join_eq; eauto.
  + rewrite find_single_join_neq; eauto. rewrite find_single_join_eq.
    rewrite find_single_join_eq. rewrite find_single_join_neq; eauto.
  + repeat (rewrite find_single_join_neq); eauto.
Qed.



Lemma le_single_join:
  forall m k v,
    le m (single_join k v m).
intros m k v k0 v0 H.
destruct (Eeqdec k k0) eqn:heq1; subst; eauto.
exists (L.join v v0); split ;eauto using L.join_le_right.
eapply M.find_2. rewrite find_single_join_eq. erewrite M.find_1; eauto. cbn in *; eauto.
exists v0. split; eauto using L.le_refl.
eapply M.find_2. rewrite find_single_join_neq; eauto. eapply M.find_1; eauto.
Qed.




Lemma m_add_single_join:
forall k v y1 y2,
 ~ M.In (elt:=L.t) k y1 ->
  MProp.Add k v y1 y2 ->
single_join k v y1 = y2.
intros.
eapply Equal_as_quotient. intro k'.
unfold MProp.Add in *.
rewrite H0.
unfold single_join. destruct (M.find (elt:=L.t) k y1) eqn:h1; eauto.
rewrite MFact.not_find_in_iff in *. rewrite H in *; try discriminate.
Qed.


Lemma single_join_monotonicity:
  forall x y,
    le x y ->
    forall k v,
    le (single_join k v x) (single_join k v y).
unfold le in *. intros.
(* if k0 in x, then we have one in y *)
destruct (MFact.In_dec x k0).
rewrite MFact.in_find_iff in *. destruct (M.find (elt:=L.t) k0 x) eqn:h1; subst; eauto; try contradiction.
destruct (Eeqdec k0 k); subst; eauto.
+ eexists. rewrite MFact.find_mapsto_iff. rewrite find_single_join_eq. split; eauto.
forwards*: M.find_2. forwards*: H. destruct_ALL. rewrite MFact.find_mapsto_iff in H2. rewrite H2. cbn in *.  rewrite MFact.find_mapsto_iff in H0. rewrite find_single_join_eq in H0. injection H0; intros; subst; eauto. rewrite h1; cbn in *. eapply L.join_monoton; eauto.
+  forwards*: M.find_2. forwards*: H. destruct_ALL. rewrite MFact.find_mapsto_iff in H2.
eexists. rewrite MFact.find_mapsto_iff. rewrite find_single_join_neq; eauto. rewrite H2. split; eauto. rewrite MFact.find_mapsto_iff in H0. rewrite find_single_join_neq in H0; eauto. rewrite H0 in h1; injection h1; intros; subst; eauto.
+ generalize n. rewrite MFact.not_find_in_iff . intros. rewrite MFact.find_mapsto_iff in H0.
destruct (Eeqdec k0 k); subst; eauto.
++ rewrite find_single_join_eq in *. rewrite n0 in *. eexists. rewrite MFact.find_mapsto_iff.  rewrite find_single_join_eq. split; eauto. cbn in *. inversion H0; subst; eauto. unfold Ljoin'. destruct (M.find (elt:=L.t) k y); eauto using L.le_refl, L.join_le_left.

++ rewrite find_single_join_neq in *; eauto. rewrite H0 in *; try discriminate.
Qed.




(* Definition join_ x :=
  List.fold_right
  (fun p m =>
    match p with
    | (k, v) => (single_join k v m)
    end)  (M.empty _) x.

Lemma join_single_join:
  forall k v l,
    join_ ((k, v) :: l) = single_join k v (join_ l).
  cbn in *. unfold join_. eauto.
Qed. *)

(* Print M.fold. *)

Definition join (m1 : t) (m2 : t) : t :=
  M.fold (fun k v t => single_join k v t) m1 m2.

Lemma join_empty:
  forall (m : M.t L.t) y,
  M.Empty (elt:=L.t) m -> join m y = y.
intros. unfold join. rewrite MProp.fold_Empty; eauto.
Qed.



Lemma join_add:
  forall k v m m' y,
  ~ M.In (elt:=L.t) k m ->
  MProp.Add k v m m' -> join m' y = single_join k v (join m y).
intros. unfold join. rewrite MProp.fold_Add; eauto.
rewrite streq. solve_proper.
intro; intros. eauto using single_join_commutative.
Qed.

Lemma empty_unique:
  forall x,
    M.Empty (elt:=L.t) x ->
    x = (M.empty _ ).
intros. eapply Equal_as_quotient. intro k.

cbn in *.   destruct (M.find (elt:=L.t) k x) eqn:h1; eauto.
rewrite MProp.elements_Empty in *.
rewrite MFact.elements_o in *. rewrite H in *. cbn in *. try discriminate.
Qed.



Lemma join_empty2:
  forall (m : M.t L.t) y,
  M.Empty (elt:=L.t) m -> join y m = y.
intros m y. generalize dependent m.
induction y using MProp.map_induction; intros; cbn in *. rewrite (join_empty); eauto.
repeat (rewrite empty_unique); eauto using empty_unique.
erewrite join_add; eauto. rewrite IHy1; eauto.
eapply m_add_single_join; eauto.
Qed.



Lemma  join_le_right:
  forall x y, le y (join x y).
intros x y. generalize dependent x.
eapply  MProp.map_induction; cbn in *; intros; cbn in *;
[rewrite join_empty | erewrite join_add]; eauto using le_refl.
eapply le_trans;[ | eapply le_single_join]; eauto.
Qed.



Lemma join_le_right_monoton:
  forall x y1 y2,
    le y1 y2 ->
    le (join x y1) (join x y2).
intros x. induction x using MProp.map_induction.
intros ; repeat rewrite join_empty; eauto.
intros. erewrite join_add; eauto. erewrite (join_add _ _ _ x2); eauto.
eapply single_join_monotonicity; eauto.
Qed.


Theorem join_le_left:
  forall x y, le x (join x y).
intros x y. generalize dependent x. induction y using MProp.map_induction; intros.
rewrite join_empty2; eauto using le_refl.
eapply le_trans;[ | eapply join_le_right_monoton]; eauto.
forwards* : m_add_single_join. rewrite <- H1.
eapply le_single_join.
Qed.



Theorem InA_streq:
  forall p l,
  InA (M.eq_key_elt (elt:=L.t)) p l <->
  InA eq p l.
unfold M.eq_key_elt, M.Raw.PX.eqke. rewrite streq.
split. intros h. induction h; subst; destruct_ALL; cbn in *; subst; eauto.
intros h. induction h; subst; destruct_ALL; cbn in *; subst; eauto.
Qed.

Theorem join_monoton:
  forall x y l,
    le x y ->
    le (join l x) (join l y).
intros x y l. generalize dependent x. generalize dependent y.
induction l using MProp.map_induction.
intros. repeat rewrite join_empty; eauto.
intros. (erewrite join_add; eauto). erewrite (join_add _ _ _ _ _ H H0); eauto.
eapply single_join_monotonicity; eauto.
Qed.

End Map_LATTICE.

Module ident_DEC <: DecidableType.

Definition t := ident.
Definition eq : t -> t -> Prop := fun x y => x = y.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
unfold eq.
repeat decide equality. Qed.

 (* Instance eq_equiv : Equivalence eq.
 split; cbv delta in *; cbn in *; eauto; intros; subst; eauto.
 Qed.  *)
 Theorem eq_refl : forall x : t, eq x x. unfold eq. auto. Qed.
 Theorem eq_sym : forall x y : t, eq x y -> eq y x. unfold eq. auto. Qed.
 Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq. intros. auto. subst. auto. Qed.

Definition streq : eq = eq. auto. Qed.

End ident_DEC.

Module ident_Map := FMapWeakList.Make(ident_DEC).
Module ident_Map_Fact := WFacts_fun ident_DEC ident_Map.

Family Lang.

FInductive exp : Set :=
  | var : ident -> exp
  | boolcst : bool -> exp
  | strcst : string -> exp
  | concat : exp -> exp -> exp.

FRecursion is_strcst_do_impl
  about exp
  motive (fun (_ : exp) => (string -> option exp) -> option exp)
  by _rec.
Case strcst := (fun n f => f n).
Case _ := (fun _ => None).
FEnd is_strcst_do_impl.

FDefinition is_strcst_do : option exp -> (string -> option exp) -> option exp
  := fun e f =>
      match e with
      | Some e => is_strcst_do_impl e f
      | None => None
      end.

(* probably unneeded since we can fsimpl... *)
Closing Fact is_strcst_do_axiom :
  forall n f,
  self__Lang.is_strcst_do (Some (self__Lang.strcst n)) f = (f n)
by {auto}.

Closing Fact is_strcst_do_axiom2 :
  forall e f v,
  self__Lang.is_strcst_do e f = Some v ->
  exists s, e = Some (self__Lang.strcst s)
by {intros [[]|] f v H; try discriminate; eauto}.

Closing Fact exp_eq_dec :
  forall (x y : self__Lang.exp), {x = y} + {x <> y}
by {intros; fold not; repeat decides_equality}.

FDefinition Memory : Type := ident_Map.t exp.
FDefinition update : Memory -> ident -> exp -> Memory :=
  fun orig k v => ident_Map.add k v orig.

FDefinition lookup : Memory -> ident -> option exp :=
  fun mem k => ident_Map.find k mem.

FLemma lookup_update:
forall mem k1 k2 v,
  lookup (update mem k1 v) k2 =
  if (ident_DEC.eq_dec k1 k2) then Some v else lookup mem k2.
FProofLemma.
  eapply ident_Map_Fact.add_o.
Qed. CloseFLemma.

FRecursion exp_eval
  about exp
  motive (fun (_ : exp) => Memory -> option exp)
  by _rect.
Case var := (fun i env => lookup env i).
Case boolcst := (fun b env => Some (boolcst b)).
Case strcst := (fun n env => Some (strcst n)).
Case concat := (fun e1 rec1 e2 rec2 env =>
  is_strcst_do
    (rec1 env)
    (fun n1 =>
      is_strcst_do
        (rec2 env)
        (fun n2 => Some (strcst (n1 ++ n2)))
    )
).
FEnd exp_eval.

FDefinition bexp_eval : Memory -> exp -> option bool :=
  fun env e =>
  let b := (exp_eval e env) in
  match b with
  | None => None
  | Some b =>
    match exp_eq_dec b (boolcst true) with
    | left _ => Some true
    | _ => match exp_eq_dec b (boolcst false) with
      | left _ => Some false
      | _ => None
    end
  end
  end.

FInductive stmt : Set :=
  | assign : ident -> exp -> stmt
  | seq    : stmt  -> stmt  -> stmt
  (* Only allow ident in the condition
      makes things easier *)
  | while  : exp -> stmt -> stmt
  | nop    : stmt
  | ifte   : exp -> stmt -> stmt -> stmt.

Closing Fact stmt_eq_dec :
  forall (x y : self__Lang.stmt), {x = y} + {x <> y}
by {intros; fold not;
     repeat decide equality}.

(* We will just not call it continuation *)

FDefinition stack : Type := list stmt.

(* Program Counter * Stack, but for first order language
    like ours, this is exactly program counter *)
FDefinition PCS : Type := stmt * stack.

FLemma PCS_eqdec :
  forall (x y : PCS),
  {x = y} + {~ x = y}.
FProofLemma.
repeat decide equality;
apply self__Lang.stmt_eq_dec.
Qed. CloseFLemma.

MetaData PCS_DEC_mod.
Module PCS_DEC <: DecidableType.

Definition t := self__Lang.PCS.
Definition eq : t -> t -> Prop := fun x y => x = y.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := self__Lang.PCS_eqdec.

(* Instance eq_equiv : Equivalence eq.
split; cbv delta in *; cbn in *; eauto; intros; subst; eauto.
Qed.  *)
Theorem eq_refl : forall x : t, eq x x. unfold eq. auto. Qed.
Theorem eq_sym : forall x y : t, eq x y -> eq y x. unfold eq. auto. Qed.
Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq. intros. subst. auto. Qed.

Lemma eq_dec_id:
  forall x, exists y, eq_dec x x = left _ y.
Proof.
  intros.
  destruct (eq_dec x x).
  - eauto.
  - destruct (n (eq_refl x)).
Qed.

Definition streq : eq = eq. auto. Qed.

End PCS_DEC.
FEnd PCS_DEC_mod.

FDefinition State : Type := PCS * Memory.

FRecursion eval__
  about stmt
  motive (fun (_ : stmt) => stack -> Memory -> State)
  by _rect.
Case assign := (fun i e stk mem =>
  match exp_eval e mem with
  | Some v => (nop, stk, (update mem i v))
  | None => (assign i e, stk, mem)
  end).
Case seq := (fun s1 _ s2 _ stk mem =>
  (s1, s2 :: stk, mem)).
Case while := (fun cond sstm _ stk mem =>
  ((ifte cond (seq sstm (while cond sstm)) nop), stk, mem)).
Case ifte := (fun cond stm1 _ stm2 _ stack mem =>
  let cond_val := bexp_eval mem cond in
  match cond_val with
  | Some true => (stm1, stack, mem)
  | Some false => (stm2, stack, mem)
  | None => (ifte cond stm1 stm2, stack, mem)
  end).
Case nop := (fun stk mem =>
  match stk with
  | [] => (nop, [], mem)
  | h::tail => (h, tail, mem)
  end).
FEnd eval__.

FDefinition eval_ : State -> State :=
  fun st =>
    match st with
    | ((stm, stack), mem) => eval__ stm stack mem
    end.

FDefinition eval : nat -> State -> State :=
  fix eval n st :=
    match n with
    | 0 => st
    | S n =>
      let st' := eval_ st in
      eval n st'
    end.

FDefinition test : exp := var 0.

FEnd Lang.

Family LangwAbs extends Lang.

Inherit eval.

Family AI.

FOpaque Definition absExp : Type := non_implement.
FOpaque Definition AEjoin : absExp -> absExp -> absExp := non_implement.
FOpaque Definition AEle : absExp -> absExp -> Prop := non_implement.

Family AbsExpData.

FDefinition t : Type := self__AI.absExp.
FDefinition join : t -> t -> t := self__AI.AEjoin.
FDefinition le : t -> t -> Prop := self__AI.AEle.

FOpaque Definition le_refl : forall x, le x x := non_implement.
FOpaque Definition le_trans : forall x y z, le x y -> le y z -> le x z := non_implement.
FOpaque Definition join_le_left :
  forall x y, le x (join x y) := non_implement.
FOpaque Definition join_le_right :
  forall x y, le y (join x y) := non_implement.

FOpaque Definition le_antisymm :
forall x y, le x y -> le y x -> x = y := non_implement.

FOpaque Definition join_monoton:
forall x y l,
  le x y ->
  le (join l x) (join l y) := non_implement.

FEnd AbsExpData.

MetaData _MAP_LATTICES_DECLARE.

Module ABSMemory := Map_LATTICE ident_DEC ident_DEC self__AI.AbsExpData.

Module ABSState := Map_LATTICE self__LangwAbs.PCS_DEC self__LangwAbs.PCS_DEC ABSMemory.

Module PCS_Map := ABSState.M.

Module PCS_Map_Properties := WProperties_fun self__LangwAbs.PCS_DEC PCS_Map.

Module ABSMemoryMap_Fact := WFacts_fun ident_DEC ABSMemory.M.

Module PCS_Map_Fact := WFacts_fun self__LangwAbs.PCS_DEC PCS_Map.

FEnd _MAP_LATTICES_DECLARE.

FDefinition absMemory : Type := self__AI.ABSMemory.t.

FDefinition aupdate : self__AI.absMemory -> ident -> self__AI.AbsExpData.t  -> self__AI.absMemory :=
  fun orig k v => self__AI.ABSMemory.M.add k v orig.

FDefinition alookup : self__AI.absMemory -> ident -> option self__AI.AbsExpData.t :=
  fun mem k  => self__AI.ABSMemory.M.find k mem.

FLemma alookup_aupdate :
    forall mem k1 k2 v,
    self__AI.alookup (self__AI.aupdate mem k1 v) k2 =
      if (ident_DEC.eq_dec k1 k2) then Some v else self__AI.alookup mem k2.
FProofLemma.
apply self__AI.ABSMemoryMap_Fact.add_o.
Qed. CloseFLemma.

FOpaque Definition RExp : exp -> absExp -> Prop := non_implement.

FOpaque Definition RExp_monoton :
  forall x a b,
    RExp x a ->
    AbsExpData.le a b ->
    RExp x b := non_implement.

FDefinition RMemory : Memory -> absMemory -> Prop :=
  fun mem amem =>
  forall k v,
    lookup mem k = Some v ->
    exists a, alookup amem k = Some a /\ RExp v a.

FOpaque Definition exp_analyze : exp -> absMemory ->  absExp
  := non_implement.

FOpaque Definition exp_analyze_sound :
  forall e mem amem v,
    RMemory mem amem ->
    exp_eval e mem = Some v ->
    RExp v (exp_analyze e amem) := non_implement.

FDefinition absState : Type := self__AI.ABSState.t.

FDefinition RState : State -> absState -> Prop :=
  fun st ast =>
    let (pc, mem) := st in
    match self__AI.PCS_Map.find pc ast with
    | None => False
    | Some amem => self__AI.RMemory mem amem
    end.

FLemma Rupdate :
  forall x y mem amem i,
  RMemory mem amem ->
  RExp x y ->
  RMemory (self__LangwAbs.update mem i x) (aupdate amem i y).
FProofLemma.
unfold self__AI.RMemory.
intros x y mem amem i H H1 k v H2.
rewrite self__LangwAbs.lookup_update in *.
rewrite self__AI.alookup_aupdate in *.
destruct (ident_DEC.eq_dec i k); subst; eauto.
inversion H2; subst; eauto.
Qed. CloseFLemma.

FDefinition injSt : self__LangwAbs.PCS -> absMemory -> absState :=
  fun pcs amem =>
  self__AI.PCS_Map.add pcs amem (self__AI.PCS_Map.empty _).

FLemma Relate_inj_st:
  forall x y z,
  RMemory y z ->
  RState (x, y) (injSt x z).
FProofLemma.
cbn in *. intros.
destruct (self__LangwAbs.PCS_DEC.eq_dec x x).
- assumption.
- destruct (n (eq_refl x)).
Qed. CloseFLemma.

FDefinition joinSt : absState -> absState -> absState :=
  self__AI.ABSState.join.

FRecursion analyze___
  about stmt
  motive (fun (_ : stmt) => stack -> absMemory -> absState)
  by _rect.
Case assign := (fun i e stk amem =>
  let v := exp_analyze e amem in
  joinSt
    (injSt (nop, stk) (aupdate amem i v))
    (injSt (assign i e, stk) amem)).
Case seq := (fun s1 _ s2 _ stk mem =>
  injSt (s1, s2 :: stk) (mem)).
Case while := (fun cond sstm _ stk mem =>
  injSt ((ifte cond (seq sstm (while cond sstm)) nop), stk) mem).
Case ifte := (fun cond stm1 _ stm2 _ stack mem =>
  joinSt
    (joinSt
      (injSt (stm1, stack) mem)
      (injSt (stm2, stack) mem))
  (injSt (ifte cond stm1 stm2, stack) mem)).
Case nop := (fun stk mem =>
  match stk with
  | [] => injSt (nop, []) mem
  | h::tail => injSt (h, tail) mem
  end).
FEnd analyze___.

FLemma RMemory_monoton:
  forall m x y,
    self__AI.RMemory m x ->
    self__AI.ABSMemory.le x y ->
    self__AI.RMemory m y.
FProofLemma.
unfold self__AI.RMemory, self__AI.ABSMemory.le.
intros.
forwards*: H; destruct_ALL.
unfold self__AI.alookup in *.
forwards*: self__AI.ABSMemory.M.find_2.
forwards*: H0; destruct_ALL.
clear H4. forwards*: self__AI.ABSMemory.M.find_1.
eexists; split; eauto.
eapply self__AI.RExp_monoton; eauto.
Qed. CloseFLemma.

FDefinition le_ast : absState -> absState -> Prop :=
  self__AI.ABSState.le.

FLemma RState_monoton:
  forall x y z,
  self__AI.RState x y ->
  self__AI.le_ast y z ->
  self__AI.RState x z.
FProofLemma.
unfold self__AI.RState, self__AI.le_ast, self__AI.ABSState.le. intros.
destruct x.
destruct (self__AI.PCS_Map.find (elt:=self__AI.ABSMemory.t) p y) eqn:h1; try contradiction.
forwards*: self__AI.ABSState.M.find_2. forwards*: H0. destruct_ALL.
forwards*: self__AI.ABSState.M.find_1. rewrite H4.
eapply self__AI.RMemory_monoton; eauto.
Qed. CloseFLemma.

FLemma join_le_ast_left:
  forall x y z,
    le_ast x y ->
    le_ast x (joinSt y z).
FProofLemma.
intros.
eapply self__AI.ABSState.le_trans;
  [ idtac | eapply self__AI.ABSState.join_le_left];
  eauto.
Qed. CloseFLemma.

FLemma join_le_ast_right:
  forall x y z,
    le_ast x z ->
    le_ast x (joinSt y z).
FProofLemma.
intros.
eapply self__AI.ABSState.le_trans;
  [ idtac | eapply self__AI.ABSState.join_le_right];
  eauto.
Qed. CloseFLemma.

MetaData __clear_PCS_DEC_eq_dec.
Ltac clear_PCS_DEC_eq_dec :=
match goal with
| [|- context G [self__LangwAbs.PCS_DEC.eq_dec ?x ?x]] => destruct (self__LangwAbs.PCS_DEC.eq_dec x x); subst; eauto; try contradiction
end.
FEnd __clear_PCS_DEC_eq_dec.

FDefinition analyze__ : PCS * absMemory -> absState :=
  fun ast =>
    match ast with
    | ((stm, stk), amem) => analyze___ stm stk amem
    end.

FInduction sync_eval__analyze__
about stmt
motive (
  fun stm =>
  forall stk mem amem,
  self__AI.RMemory mem amem ->
  self__AI.RState (self__LangwAbs.eval_ (stm, stk, mem)) (self__AI.analyze__ ((stm, stk), amem))
).
FProof.
- intros. cbn. repeat fsimpl.
  destruct (self__LangwAbs.exp_eval e mem) eqn:h1.
  + eapply self__AI.RState_monoton.
    * eapply self__AI.Relate_inj_st. eapply self__AI.Rupdate; eauto.
      eapply self__AI.exp_analyze_sound; eauto.
    * eapply self__AI.join_le_ast_left. eapply self__AI.ABSState.le_refl.
  + eapply self__AI.RState_monoton.
    * eapply self__AI.Relate_inj_st; eauto.
    * eapply self__AI.join_le_ast_right; eapply self__AI.ABSState.le_refl.
- intros. repeat (fsimpl; cbn). self__AI.clear_PCS_DEC_eq_dec. destruct (n (eq_refl _)).
- intros. repeat (fsimpl; cbn). self__AI.clear_PCS_DEC_eq_dec. destruct (n (eq_refl _)).
- intros. repeat (fsimpl; cbn). destruct stk; eauto using self__AI.Relate_inj_st.
- intros. cbn. repeat fsimpl. destruct (self__LangwAbs.bexp_eval mem e).
  destruct b; eapply self__AI.RState_monoton; eauto using self__AI.Relate_inj_st.
  + eapply self__AI.join_le_ast_left. eapply self__AI.join_le_ast_left. eapply self__AI.ABSState.le_refl.
  + eapply self__AI.join_le_ast_left. eapply self__AI.join_le_ast_right. eapply self__AI.ABSState.le_refl.
  + eapply self__AI.RState_monoton; eauto using self__AI.Relate_inj_st. eapply self__AI.join_le_ast_right. eapply self__AI.ABSState.le_refl.
Qed. FEnd sync_eval__analyze__.

FDefinition analyze_ : absState -> absState :=
  fun ast =>
    List.fold_right
      (fun p ast => self__AI.joinSt ast (self__AI.analyze__ p))
      (self__AI.PCS_Map.empty _)
      (self__AI.PCS_Map.elements ast).

FLemma point_wise_analyze_:
  forall x y,
    InA eq x y ->
    le_ast
      (analyze__ x)
      (fold_right
        (fun p0 (ast0 : absState) => joinSt ast0 (analyze__ p0))
        (self__AI.PCS_Map.empty _)
        y).
FProofLemma.
intros x y h.
induction h; subst; eauto.
- destruct y; subst; eauto.
  eapply self__AI.join_le_ast_right. eapply self__AI.ABSState.le_refl.
- eauto using self__AI.join_le_ast_left, self__AI.join_le_ast_right.
Qed. CloseFLemma.

FLemma sync_eval_analyze_ :
  forall st ast,
    self__AI.RState st ast ->
    self__AI.RState (self__LangwAbs.eval_ st) (self__AI.analyze_ ast).
FProofLemma.
destruct st. intros ast h. cbn in h.
destruct (self__AI.PCS_Map.find (elt:=self__AI.ABSMemory.t) p ast ) eqn:h1; try contradiction.
unfold self__LangwAbs.eval_. destruct p.
eapply self__AI.RState_monoton. eapply self__AI.sync_eval__analyze__; eauto.
unfold self__AI.analyze_.
rewrite <- self__AI.PCS_Map_Fact.find_mapsto_iff in h1.
rewrite self__AI.PCS_Map_Fact.elements_mapsto_iff in h1.
eapply self__AI.point_wise_analyze_; eauto. rewrite self__AI.ABSState.InA_streq in h1. eauto.
Qed. CloseFLemma.

FDefinition analyze : nat -> absState -> absState :=
  fix f fuel st :=
    match fuel with
    | 0 => st
    | S fuel =>
      let st' := analyze_ st in
      f fuel st'
    end.

FLemma analyze_partial_correct:
  forall fuel st ast,
    RState st ast ->
    RState (self__LangwAbs.eval fuel st) (analyze fuel ast).
FProofLemma.
induction fuel; eauto using self__AI.sync_eval_analyze_.
Qed. CloseFLemma.

FEnd AI.
FEnd LangwAbs.

Family LangCP extends LangwAbs.

FInductive exp : Set :=
| natcst : nat -> exp
| add : exp -> exp -> exp.

Closing Fact natcst_inj:
  forall n m,
    self__LangCP.natcst n = self__LangCP.natcst m ->
    n = m
  by {inversion 1; auto}.

FRecursion is_strcst_do_impl.
Case _ := (fun _ => None).
FEnd is_strcst_do_impl.

FRecursion is_natcst_do_impl
  about exp
  motive (fun (_ : exp) => (nat -> option exp) -> option exp)
  by _rec.
Case natcst := (fun n f => f n).
Case _ := (fun _ => None).
FEnd is_natcst_do_impl.

FDefinition is_natcst_do : option exp -> (nat -> option exp) -> option exp
  := fun e f =>
      match e with
      | Some e => is_natcst_do_impl e f
      | None => None
      end.

Closing Fact is_natcst_do_axiom :
  forall n f,
  self__LangCP.is_natcst_do (Some (self__LangCP.natcst n)) f = (f n)
by {auto}.

Closing Fact is_natcst_do_axiom2 :
  forall e f v,
  self__LangCP.is_natcst_do e f = Some v ->
  exists s, e = Some (self__LangCP.natcst s)
by {intros [[]|] f v H; try discriminate; eauto}.

FRecursion exp_eval.
Case natcst :=
  (fun n env => Some (natcst n)).
Case add :=
  (fun e1 rec1 e2 rec2 env =>
    is_natcst_do
      (rec1 env)
      (fun n1 =>
        is_natcst_do
          (rec2 env)
          (fun n2 => Some (natcst (n1 + n2))))).
FEnd exp_eval.

Family AI.

MetaData _literals.
Inductive literals : Type :=
| natlit : nat -> literals
| otherv : literals.
FEnd _literals.

FOverride Definition absExp := self__AI.literals.

FOverride Definition AEjoin := (fun e1 e2 =>
  match e1, e2 with
  | self__AI.natlit a, self__AI.natlit b => if eq_nat_dec a b then self__AI.natlit a else self__AI.otherv
  | _, _ => self__AI.otherv
  end).

FOverride Definition AEle :=
  fun s1 s2 =>
    (exists n, s1 = self__AI.natlit n /\ s1 = s2)
    \/ (s2 = self__AI.otherv).

Family AbsExpData.

FOverride Lemma le_refl.
FProofLemma.
unfold self__AbsExpData.le, self__AI.AEle.
destruct x; eauto.
Qed. CloseFLemma.

FOverride Lemma le_trans.
FProofLemma.
unfold self__AbsExpData.le, self__AI.AEle.
intros; destruct_ALL.
Qed. CloseFLemma.

FOverride Lemma join_le_left.
FProofLemma.
unfold self__AbsExpData.le, self__AI.AEle,
  self__AbsExpData.join, self__AI.AEjoin.
intros. destruct x, y; eauto.
- destruct (eq_nat_dec n n0); eauto.
Qed. CloseFLemma.

FOverride Lemma join_le_right.
FProofLemma.
unfold self__AbsExpData.le, self__AI.AEle,
  self__AbsExpData.join, self__AI.AEjoin.
intros. destruct x, y; eauto.
- destruct (eq_nat_dec n n0); eauto.
Qed. CloseFLemma.

FOverride Lemma le_antisymm.
FProofLemma.
unfold self__AbsExpData.le, self__AI.AEle.
intros x y h1 h2.
destruct h1, h2; destruct_ALL; subst; eauto.
Qed. CloseFLemma.

FOverride Lemma join_monoton.
FProofLemma.
unfold self__AbsExpData.le, self__AI.AEle, self__AbsExpData.join.
intros. destruct l, H; destruct_ALL; subst; eauto; cbn in *.
destruct (PeanoNat.Nat.eq_dec n x0); subst; eauto.
Qed. CloseFLemma.

FEnd AbsExpData.

FOverride Definition RExp := fun e ae =>
  (forall n, e = natcst n -> ae = self__AI.natlit n \/ ae = self__AI.otherv).

FOverride Lemma RExp_monoton.
FProofLemma.
unfold self__AI.RExp, self__AI.AbsExpData.le, self__AI.AEle.
intros; destruct_ALL.
Qed. CloseFLemma.

Inherit RMemory.

MetaData _exp_analyze_handlers.
Definition _motive : self__LangCP.exp -> Type :=
  fun e =>
    forall (amem : self__AI.absMemory),
      {ae : self__AI.absExp |
        forall mem v,
          self__AI.RMemory mem amem ->
          self__LangCP.exp_eval e mem = Some v ->
          self__AI.RExp v ae
      }.

Definition _var : forall (i : ident), _motive (self__LangCP.var i).
unfold _motive. intros.
destruct (self__AI.alookup amem i) eqn:h1.
- exists t. fsimpl. intros. unfold self__AI.RMemory in *.
  forwards*: H; destruct_ALL. rewrite h1 in H1. inversion H1; subst; eauto.
- exists self__AI.otherv. fsimpl. intros. unfold self__AI.RMemory in *.
  forwards*: H; destruct_ALL. rewrite h1 in H1; discriminate.
Qed.

Definition _boolcst : forall (b : bool), _motive (self__LangCP.boolcst b).
intros x mem. exists self__AI.otherv. unfold self__AI.RMemory.
fsimpl. unfold self__AI.RExp. intros. inversion H0; subst; eauto.
Qed.

Definition _strcst : forall n : string, _motive (self__LangCP.strcst n).
intros n mem. exists self__AI.otherv. unfold self__AI.RMemory.
fsimpl. unfold self__AI.RExp. intros. inversion H0; subst; eauto.
Qed.

Definition _concat :
forall (e1 : self__LangCP.exp) (rec1 : _motive e1)
       (e2 : self__LangCP.exp) (rec2 : _motive e2), _motive (self__LangCP.concat e1 e2).
intros. intro. exists self__AI.otherv. unfold self__AI.RMemory.
fsimpl. unfold self__AI.RExp. intros; subst; eauto.
Qed.

Definition _natcst :
  forall n : nat, _motive (self__LangCP.natcst n).
intros n mem. exists (self__AI.natlit n). unfold self__AI.RMemory.
fsimpl. unfold self__AI.RExp. intros. subst. injection H0.
auto using self__LangCP.natcst_inj.
Qed.

Definition _add :
  forall e1 (rec1 : _motive e1) e2 (rec2 : _motive e2), _motive (self__LangCP.add e1 e2).
unfold _motive.
intros.  forwards*:(rec1 amem). forwards*: (rec2 amem).
destruct H. destruct H0. destruct x eqn:h1; destruct x0 eqn:h2.
exists (self__AI.natlit (n + n0)).
intros. fsimpl in *.
+ forwards*: self__LangCP.is_natcst_do_axiom2; destruct_ALL.
  rewrite H1 in H0. rewrite self__LangCP.is_natcst_do_axiom in H0.
  forwards*: self__LangCP.is_natcst_do_axiom2; destruct_ALL.
  rewrite H2 in H0. rewrite self__LangCP.is_natcst_do_axiom in H0.
  unfold self__AI.RExp in *. intros. subst; eauto.
  inversion H0.
  forwards*: r. forwards*: r0.
  destruct H3; destruct H5; try discriminate. inversion H3; inversion H5; subst; inversion H4; eauto. forwards*: self__LangCP.natcst_inj.
+ exists self__AI.otherv. intros. unfold self__AI.RExp. auto.
+ exists self__AI.otherv. intros. unfold self__AI.RExp. auto.
+ exists self__AI.otherv. intros. unfold self__AI.RExp. auto.
Qed.
FEnd _exp_analyze_handlers.

FRecursion exp_analyze_
  about exp
  motive self__AI._motive
  by _rect.
Case var := self__AI._var.
Case boolcst := self__AI._boolcst.
Case strcst := self__AI._strcst.
Case concat := self__AI._concat.
Case natcst := self__AI._natcst.
Case add := self__AI._add.
FEnd exp_analyze_.

FOverride Definition exp_analyze :=
  fun e amem => proj1_sig (exp_analyze_ e amem).

FOverride Lemma exp_analyze_sound.
FProofLemma.
unfold self__AI.exp_analyze. intros.
destruct (self__AI.exp_analyze_ e amem). eauto.
Qed. CloseFLemma.

FEnd AI.

FEnd LangCP.
