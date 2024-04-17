(* We need to override the `Lgetstack` / `Lsetstack` 
   instructions to use actual offsets instead of 
   an abstract stack slot. *)
(* I think maybe the stack slot should be a parameter 
   of the `Impbackend` family *)
family Impzero.Impmach extends Impbackend { 
    Inductive instruction: Type :=
        | Mgetstack: ptrofs -> typ -> mreg -> instruction
        | Msetstack: mreg -> ptrofs -> typ -> instruction
        | Mgetparam: ptrofs -> typ -> mreg -> instruction
        | Mop: operation -> list mreg -> mreg -> instruction
        | Mlabel: label -> instruction
        | Mgoto: label -> instruction
        | Mcond: condition -> list mreg -> label -> instruction
        | Mjumptable: mreg -> list label -> instruction        
      
    family Semantics { }
}


(* Stacking translation: Linear -> Mach  *)
family Impzero.Impstacking extends ImpbackendTransform {
  family Source extends Implinear { }
  family Target extends Impmach { }

  family CorrectnessProof { }
}
