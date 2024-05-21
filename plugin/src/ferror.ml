

(* A nested command that is not a family *)
(* e.g 
   FRecursions ...
      FRecursion ....
*)
(* Without closing the first scope *)
exception NestedCommand
exception ClosingWrongScope

let report ~error = raise error
