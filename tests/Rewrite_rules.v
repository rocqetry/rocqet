
Symbol pplus : nat -> nat -> nat.
Infix "++" := pplus.
Rewrite Rules pplus_rew :=
| 0 ++ ?n => ?n | S ?m ++ ?n => S (?m ++ ?n)
| ?m ++ 0 => ?m | ?m ++ S ?n => S (?m ++ ?n).


Symbol expr : Type.
Symbol Var : nat -> expr.
Symbol Abs : nat -> expr -> expr.
Symbol App : expr -> expr -> expr.

Symbol size : expr -> nat.

Rewrite Rules size_rew :=
| size (Var ?x) => 0
| size (Abs ?x ?y) => 1 + size ?y
| size (App ?x ?y) => size ?x + size ?y.

Lemma blah : forall n:nat, size (Var n) = 0.
Proof.
  intros. simpl. reflexivity.
Qed.

Require Extraction.

Extraction size.
  
