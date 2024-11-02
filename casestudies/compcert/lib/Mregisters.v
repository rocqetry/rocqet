Require Import Coqlib.
Require Import AST.
Require Import Maps.
Require Import Ordered.
Require Import Machregs.
Require FSetAVL.
Require Import Values.

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).
