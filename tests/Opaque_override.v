From NFPOP Require Import Loader.

Axiom cheat : forall {X}, X.

Family X.
   FOpaque Definition y : nat -> nat := fun x => x.
FEnd X.

Family Y extends X.   
   FOverride Definition y := fun x => 0.
FEnd Y.


Print Y.y.

Family Abs.
   FOpaque Definition T : Type := cheat.

   FOpaque Definition t : T := cheat.
FEnd Abs.

Family Conc extends Abs.
   FOverride Definition T := nat.

   FOverride Definition t := 0.
FEnd Conc.



