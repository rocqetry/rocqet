(* Arithmetic Expressions + Variables *)
Require Import Arith.

(* The language  *)
Inductive expr : Type :=
  | Val (n: nat)
  | Add (a: expr) (b: expr).
