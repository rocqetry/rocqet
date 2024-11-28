
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

Definition size_Var_handler := fun (x:nat) => 0.
Definition size_Abs_handler := fun (x:nat) (x: expr) (size_x: nat) => 1 + size_x.
Definition size_App_handler := fun (x: expr) (size_x: nat) (y: expr) (size_y: nat) => size_x + size_y.

Rewrite Rules size_rew :=
| size (Var ?x) => size_Var_handler ?x
| size (Abs ?x ?y) => size_Abs_handler ?x ?y (size ?y)
| size (App ?x ?y) => size_App_handler ?x (size ?x) ?y (size ?y).

Lemma blah : forall n:nat, size (Var n) = 0.
Proof.
  intros. simpl. reflexivity.
Qed.

Require Extraction.

Extraction size.
  
