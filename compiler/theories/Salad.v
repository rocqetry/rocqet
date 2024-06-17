From NFPOP Require Import Loader.

(* Strictness of "Typechecking" further binding *)

Notation ident := nat.

Family Salad.
   FInductive expr : Set := 
     | tm_var : ident -> expr 
     | tm_app : expr -> expr -> expr 
     | tm_abs : ident -> expr.                           
FEnd Salad.

Family SaladX extends Salad.
   FInductive expr : Set := 
     | tm_pair : expr -> expr -> expr.
FEnd SaladX.

Family Dataflow.
    Family Lang extends Salad.       
    FEnd Lang.
    
    Family Base. 
    FEnd Base.
    
    Family Liveness.
    FEnd Liveness.
FEnd Dataflow.

Family Random extends SaladX.
FEnd Random.

Family R1 extends Random.
FEnd R1.

Family DataflowX extends Dataflow.
    Family Lang extends R1.
        FInductive expr : Set := 
          | tm_proj_left : expr -> nat -> expr.
    FEnd Lang.
FEnd DataflowX.
