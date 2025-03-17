Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
From Rocqet Require Import Coqlib.
From Rocqet Require Import AST.
From Rocqet Require Import Maps.
From Rocqet Require Import Values.
From Rocqet Require Import Integers. 
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


(* Registers for Asm *)

Inductive ireg: Type :=
  | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
  | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
  | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
  | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
  | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
  | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
  | X31: ireg.

Inductive ireg0: Type :=
  | X0: ireg0 | X: ireg -> ireg0.

Coercion X: ireg >-> ireg0.

(** Floating-point registers *)

Inductive freg: Type :=
  | F0: freg  | F1: freg  | F2: freg  | F3: freg
  | F4: freg  | F5: freg  | F6: freg  | F7: freg
  | F8: freg  | F9: freg  | F10: freg | F11: freg
  | F12: freg | F13: freg | F14: freg | F15: freg
  | F16: freg | F17: freg | F18: freg | F19: freg
  | F20: freg | F21: freg | F22: freg | F23: freg
  | F24: freg | F25: freg | F26: freg | F27: freg
  | F28: freg | F29: freg | F30: freg | F31: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma ireg0_eq: forall (x y: ireg0), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.
  
(** We model the following registers of the RISC-V architecture. *)

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision float registers *)
  | PC: preg.                           (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

Declare Scope asm.
Notation "'SP'" := X2 (only parsing) : asm.
Notation "'RA'" := X1 (only parsing) : asm.

Open Scope asm.
Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR X31 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.

Definition get0w (rs: Pregmap.t val) (r: ireg0) : val :=
  match r with
  | X0 => Vint Int.zero
  | X r => rs r
  end.

Definition get0l (rs: Pregmap.t val) (r: ireg0) : val :=
  match r with
  | X0 => Vlong Int64.zero
  | X r => rs r
  end.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a ## b" := (get0w a b) (at level 1) : asm.
Notation "a ### b" := (get0l a b) (at level 1) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.
