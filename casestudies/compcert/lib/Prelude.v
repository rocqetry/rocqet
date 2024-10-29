Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
From NFPOP Require Import Coqlib.
From NFPOP Require Import AST.
Require Import Coq.ZArith.ZArith.

Axiom cheat : forall {X}, X.

Module VarOrder <: TotalLeBool.
  Definition t := (ident * Z)%type.
  Definition leb (v1 v2: t) : bool := zle (snd v1) (snd v2).
  Theorem leb_total: forall v1 v2, leb v1 v2 = true \/ leb v2 v1 = true.
  Proof.
    unfold leb; intros.
    assert (snd v1 <= snd v2 \/ snd v2 <= snd v1) by lia.
    unfold proj_sumbool. destruct H; [left|right]; apply zle_true; auto.
  Qed.
End VarOrder.

Module VarSort := Mergesort.Sort(VarOrder).
