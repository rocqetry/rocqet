From NFPOP Require Import Loader.

Family X.
   FOpaque Definition y : nat -> nat := fun x => x.
FEnd X.

Family Y extends X.   
   FOverride Definition y := fun x => 0.
FEnd Y.


Print Y.y.
