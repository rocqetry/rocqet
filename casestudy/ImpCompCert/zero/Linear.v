
(* Nothing to do here *)
family Impzero.Implinear extends Impbackend { }

(* LTL -> Linear translation *)
family Impzero.Implinearize extends ImpbackendTransform {  
  family Source extends Impltl { }
  family Target extends Implinear { }

  family CorrectnessProof { }
}
