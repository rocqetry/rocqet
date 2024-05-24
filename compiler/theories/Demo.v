From NFPOP Require Import Loader.

(* FInductive step : Set := exec_label. *)

Family Cminorvariant.
    Family Semantics.
    FEnd Semantics.
FEnd Cminorvariant.

Family Cminor extends Cminorvariant.
    Family Semantics.
       FInductive name : Set := exec_step | exec_skip. 
    FEnd Semantics.
FEnd Cminor.

(* We need to make the tool accessible from the `./casestudy` directory *)
