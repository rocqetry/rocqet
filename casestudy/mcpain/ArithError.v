(* Arithmetic Expressions with a notion of a failed execution *)
Require Import Arith.

(* The language  *)
Inductive expr : Type :=
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

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition bind (n : natoption) (f : nat -> natoption) : natoption :=
  match n with
  | Some n => f n
  | None => None
  end.

Definition stack := list value.

Fixpoint exec (code: ir) (s : stack) : natoption :=
  match code, s with
  | [], result :: _ => Some result
  | push n :: code, s => exec code (n :: s)
  | add :: code, x :: y :: s => exec code (y + x :: s)
  | _, _ => None
  end.

Check eval.
Check exec.

Lemma exec_nothing : forall s x s', x :: s' = s -> exec [] s = Some x.
Proof.
  intros.
  induction s.
  - discriminate H.
  - simpl.
    injection H as H0.
    f_equal.
    symmetry.
    apply H0.
Qed.


Lemma exec_step : forall e xs s,
    exec (compile e ++ xs) s = exec xs (eval e :: s).
Proof.
  intros e.
  induction e.
  - simpl. reflexivity.
  - simpl.  rewrite -> app_assoc.
    intros xs s.
    assert ( (((compile e1 ++ compile e2) ++ [add]) ++ xs) = ((compile e1 ++ compile e2) ++ [add] ++ xs)) as H.
    { rewrite -> app_assoc_reverse. reflexivity. }
    rewrite -> H.
    rewrite -> app_assoc_reverse.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
Qed.
  
  
Theorem compiler_correctness : forall (e: expr),
    Some (eval e) = exec (compile e) [].
Proof.
  intros e.
  induction e.
  - (* e = const n *)
    simpl.
    reflexivity.
  - (* e = add *)
    simpl.
    rewrite -> exec_step.
    rewrite -> exec_step.
    simpl.
    reflexivity.
Qed.
