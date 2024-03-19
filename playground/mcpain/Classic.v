(* Based exactly on the paper by McCarthy & Painter *)

Definition id := nat.

Definition value := nat.

Definition store := id -> value.

Inductive expr :=
  | EVal : nat -> expr
  | EVar : id -> expr               
  | EAdd : expr -> expr -> expr.
        
Inductive instruction :=
  | LoadI (* load immediate *)
  | Load (* load *)
  | Store (* store *)
  | Add.

Fixpoint value_of (e : expr) (env : store) : value :=
  match e with
  | EVal n => n
  | EVar id => env id
  | EAdd s1 s2 => value_of s1 env + value_of s2 env
  end.                                       


Inductive state_vector :=
  | Empty : state_vector
  | Extend : id -> value -> state_vector.

Require Import Coq.Arith.EqNat.

Check beq_nat.

(* Fixpoint lookup (x : id) (env : state_vector) : value :=
  match env with
  | Empty => 
*)

















      




