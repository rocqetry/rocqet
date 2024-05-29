From NFPOP Require Import Loader.

Family Semantics. 
   FInductive eval_expr : Set := eval_binary : eval_expr | eval_const : eval_expr.

   FInductive step : Set :=
     | exec_skip : step
     | exec_assign : self__Semantics.eval_expr -> step.
FEnd Semantics.

Family BSemantics extends Semantics.
   (* FInductive call_state : Set := ReturnState : self__BSemantics.eval_expr -> call_state. *)
   FInductive eval_expr : Set := eval_unop : eval_expr.

FEnd BSemantics.

Check Semantics.step.

Check BSemantics.step.




