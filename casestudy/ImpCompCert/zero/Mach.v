(* We need to override the `Lgetstack` / `Lsetstack` 
   instructions to use actual offsets instead of 
   an abstract stack slot. *)
(* I think maybe the stack slot should be a parameter 
   of the `Impbackend` family *)
family Impzero.Impmach extends Impbackend { }


(* Stacking translation: Linear -> Mach  *)
family Impzero.Impstacking extends ImpbackendTransform {
  family Source extends Implinear { }
  family Target extends Impmach { }

  family CorrectnessProof { }
}
