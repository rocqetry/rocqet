(* Arithmetic Expressions *)
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

Fixpoint compile' (e: expr) (c: ir) : ir :=
  match e with
  | const n => push n :: c
  | plus x y => compile' x (compile' y (add :: c))
  end.                         

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition stack := list value.

(* A simple VM for the ir *)
 Fixpoint exec (instrs: ir) (s: stack): stack  := 
  match instrs, s with 
  | [], s => s 
  | push n :: instrs, s => exec instrs (n :: s)
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
  destruct l1.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma app_cons : forall (A : Type) (x: A) (xs ys: list A),
    (x :: xs) ++ ys = x :: (xs ++ ys).
Proof.  
  intros. 
  destruct xs.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

  
Lemma distributivity_lemma : forall c d s, exec (c ++ d) s = exec d (exec c s).
Proof.
  intros c.
  induction c as [| c' cs' IHcs' ].
  - simpl. reflexivity.
  -  destruct c' eqn:E. 
     (* Push *)
     + intros d s. simpl. rewrite <- IHcs'. reflexivity.
     (* Add *)
     (* + intros d s.rewrite -> app_cons.
       destruct d.
       ++ destruct s.
          -- simpl. reflexivity.
          -- rewrite <- app_nil_end. simpl. reflexivity.
       ++ destruct s.
          -- simpl. *)


Admitted.

       
(*

  n : nat
  cs', d : list instr
  IHcs' : forall s : stack, exec (cs' ++ d) s = exec d (exec cs' s)
  s : stack
  ============================
  exec (cs' ++ d) (n :: s) = exec d (exec cs' (n :: s))


*)
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


(* Another formulation of compiler correctness *)
Theorem compiler_correctness'
  : forall e s c, exec (compile' e c) s = exec c (eval e :: s).
Proof.
  intros e. 
  induction e.
  - simpl. reflexivity.
  - simpl. intros c. intros s. rewrite -> IHe1.
    rewrite -> IHe2. simpl. reflexivity.
Qed.
