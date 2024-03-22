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

Module Reuse.

Inductive value := 
  | VInt : nat -> value.

Inductive expr :=
  | EAdd : expr -> expr -> expr
  | EMul : expr -> expr -> expr
  | EInt : nat -> expr.

Fixpoint eval (e: expr) : value := 
  match e with 
  | EInt (i) => VInt i
  | EAdd e1 e2 => 
      match eval e1, eval e2 with 
      | VInt v1, VInt v2  => VInt (v1 + v2)
      end
  | EMul e1 e2 => 
      match eval e1, eval e2 with 
      | VInt v1, VInt v2  => VInt (v1 * v2)
      end
   end.

  Definition opt_id (e: expr) : expr := 
    match e with 
    | EInt (i) => EInt i
    | EAdd e1 e2 => EAdd e1 e2
    | EMul e1 e2 =>  EMul e1 e2
    end.
  
  Theorem opt_id_preserves_semantics : forall e,
      eval (opt_id e) = eval e.
  Proof.
    intros.
    induction e.
    - (* add *) simpl. destruct (eval e1). destruct (eval e2). reflexivity.
    - reflexivity.
    - reflexivity.
   Qed.

   Definition opt_add_0 (e: expr) : expr := 
      match e with 
      | EInt (i) => EInt i
      | EAdd e1 (EInt 0) => e1
      | EAdd e1 e2 => EAdd e1 e2
      | EMul e1 e2 =>  EMul e1 e2
      end.
   
   Theorem opt_add_0_preserves_semantics : forall e,
      eval (opt_add_0 e) = eval e.
   Proof.
    intros.
    induction e.
    -  

simpl. destruct e2.
      + (* a + 0 case *) destruct (eval e1). destruct (eval (EAdd e2_1 e2_2)).
        simpl. destruct (eval e1). destruct (eval e2_1). destruct (eval e2_2).
        simpl.
