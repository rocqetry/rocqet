From NFPOP Require Import Loader.

Family Semantics. 
   FInductive eval_expr : Set := eval_binary : eval_expr | eval_const : eval_expr.

   FInductive step : Set := exec_skip : step | exec_assign : step.   
FEnd Semantics.

Check Semantics.step.

(* We need to make the tool accessible from the `./casestudy` directory *)
