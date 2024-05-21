From NFPOP Require Import Loader.

Family Cminorvariant.
    Family Semantics.
    FEnd Semantics.
FEnd Cminorvariant.

Family Cminor extends Cminorvariant.
    Family Semantics.
       FInductive name := exec_step. 
    FEnd Semantics.
FEnd Cminor.

(* We need to make the tool accessible from the `./casestudy` directory *)

