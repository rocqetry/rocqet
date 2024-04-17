
family Impzero.Implinear extends Impbackend { 
    Inductive instruction: Type :=
       | Lgetstack: slot -> Z -> typ -> mreg -> instruction
       | Lsetstack: mreg -> slot -> Z -> typ -> instruction
       | Lop: operation -> list mreg -> mreg -> instruction
       | Llabel: label -> instruction
       | Lgoto: label -> instruction
       | Lcond: condition -> list mreg -> label -> instruction
       | Ljumptable: mreg -> list label -> instruction

    family Semantics { }                                             
}

(* LTL -> Linear translation *)
family Impzero.Implinearize extends ImpbackendTransform {  
  family Source extends Impltl { }
  family Target extends Implinear { }

  family CorrectnessProof { }
}
