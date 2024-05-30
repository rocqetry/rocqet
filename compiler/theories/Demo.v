From NFPOP Require Import Loader.

Family Semantics.   
   FInductive basic : Set := car : basic.

   FInductive step : Set :=
     | exec_skip : step.
     (* | exec_assign : self__Semantics.eval_expr -> step.*)

   FInductive eval_expr : Set := eval_binary : self__Semantics.step -> eval_expr | eval_const : eval_expr.

   FInductive work : Set := home : work | school : work.
FEnd Semantics.

Family BSemantics extends Semantics.
   (* FInductive call_state : Set := ReturnState : self__BSemantics.eval_expr -> call_state. *)
   FInductive step : Set := exec_assign : self__BSemantics.basic -> step.

   FInductive eval_expr : Set := eval_unop : self__BSemantics.step -> eval_expr.
FEnd BSemantics.

Family D extends BSemantics.

   FInductive eval_expr : Set := eval_ifthenelse : eval_expr.
FEnd D.

Family F extends D.
FEnd F.

Check F.eval_ifthenelse.

Check BSemantics.eval_unop.

Check D.eval_ifthenelse.

Check D.eval_unop.

Check D.exec_assign.

Check Semantics.step.

Check BSemantics.step.


Inductive t := a | b.

Check t.
