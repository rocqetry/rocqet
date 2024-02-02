(*

Compiler Correctness a la: 

McCarthy, J. & Painter, J. (1967) Correctness of a compiler for
arithmetic expressions.

Robin Milner & Richard Weyhrauch (1972). Proving compiler correctness
in a mechanized logic

*) 
Require Import Arith.

(* The language  *)
Inductive expr :=
  | const (n: nat)
  | plus (a: expr) (b: expr).

Definition value := nat.

(* A tree-walking interpreter *)
Fixpoint eval (e : expr) : value :=
  match e with
  | const n => n
  | plus e1 e2 => eval e1 + eval e2
  end.

(* A stack-based IL *)
Inductive instr := 
  | push (n : nat) 
  | add.

(* An IR *)
Definition ir := list instr.

Require Import List.
Import ListNotations.

Definition a : ir := [add; push 10].

(* A compiler to the IR *)
Fixpoint compile (e : expr) : ir :=
  match e with
  | const n => [push n]
  | plus e1 e2 => compile e1 ++ compile e2 ++ [add]
  end.

Definition stack := list value.

(* A simple VM for the ir *)
 Fixpoint exec (instrs: ir) (s: stack): stack  := 
  match instrs, s with 
  | [], _ => s 
  | push n :: instrs, _ => exec instrs (n :: s)
  | add :: instrs, x :: y :: s =>  exec instrs (y + x:: s)  
  | _, _ => [] (* error *)
  end.

Lemma app_assoc2 : forall (A : Type) (l1 l2 l3 : list A),
   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma app_assoc : forall (A : Type) (l1 l2 l3 : list A),
   l1 ++ l2 ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  induction l1.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma distributivity_lemma : forall c d s, exec (c ++ d) s = exec d (exec c s).
Proof.
  intros c d s.
Admitted.

Theorem compiler_correctness 
  : forall (e : expr) (s: stack), exec (compile e) s = eval e :: s.
Proof.
  intros e. 
  induction e. 
  - simpl. reflexivity.
  -  intros s. 
     simpl. 
     rewrite -> distributivity_lemma.
     rewrite -> IHe1.
     rewrite -> distributivity_lemma.
     rewrite -> IHe2. 
     simpl.
     reflexivity.
Qed.
