
Symbol pplus : nat -> nat -> nat.
Infix "++" := pplus.
Rewrite Rules pplus_rew :=
| 0 ++ ?n => ?n | S ?m ++ ?n => S (?m ++ ?n)
| ?m ++ 0 => ?m | ?m ++ S ?n => S (?m ++ ?n).

Module Type MTCtx.
End MTCtx.  

(* Module Type Expr (self: MTCtx).*)
Symbol expr : Type.
Symbol Var : nat -> expr.
Symbol Abs : nat -> expr -> expr.
Symbol App : expr -> expr -> expr.
(*End Expr.

Module Type sizeCtx.
  Include MTCtx.
  Include Expr.
End sizeCtx.  *)

(*Module Type size (self: sizeCtx).*)
Symbol size : expr -> nat.
(*End size.*)


(*
Module Type handlerCtx.
  Include sizeCtx.  
  Include size.
End handlerCtx.*)

(* Module handler (self: handlerCtx).*)

(*Definition size_Var_handler := fun (x:nat) => 0.
Definition size_Abs_handler := fun (x:nat) (x: self.expr) (size_x: nat) => 1 + size_x.
Definition size_App_handler := fun (x: self.expr) (size_x: nat) (y: self.expr) (size_y: nat) => size_x + size_y.*)

(*Import self.*)

Rewrite Rules size_rew :=
| size (Var ?x) => 1
| size (Abs ?x ?y) => 1 + size ?y
| size (App ?x ?y) => size (App ?x ?y). (*?x + size ?y.*)

Lemma blah : forall n:nat, size (Var n) = 1.
Proof.
  intros. simpl. reflexivity.
Qed.

Print size.
Check size.
Compute (size (App (Var 0) (Var 0))).
Require Extraction.

Extraction size.
  
