From NFPOP Require Import Loader.

Family Semantics.   
   FInductive step : Set :=
     | exec_skip : step.
     (* | exec_assign : self__Semantics.eval_expr -> step.*)

   FInductive eval_expr : Set := eval_binary : eval_expr | eval_const : eval_expr.
FEnd Semantics.

Family BSemantics extends Semantics.
   (* FInductive call_state : Set := ReturnState : self__BSemantics.eval_expr -> call_state. *)
   FInductive eval_expr : Set := eval_unop : self__BSemantics.step -> eval_expr.
FEnd BSemantics.

Family D extends BSemantics.
FEnd D.

Check BSemantics.eval_unop.

Check D.eval_unop.

(* Check D.exec_assign. *)

(* Check Semantics.step. *)

(* Check BSemantics.step. *)


