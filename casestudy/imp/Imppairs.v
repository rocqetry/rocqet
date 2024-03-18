(* Imp with pairs *)
family Imppairs extends Impzero { }

family Imppairs.Impcommon {                 
  Inductive expression : Type +=
     | Epair : expression -> expression -> expression.  
}

family Imppairs.Impcommon {
    family Semantics.Values {
        Inductive value: Type +=
          | Vpair: value -> value -> value
    }

    (* Print TODOs. A command to print a list of things to be handled based on
       the change to the inductive types *)
}    

family Imppairs.Impcommon {
  family Semantics {
      Inductive eval_expr : expression -> Values.value -> Prop :=
          | eval_Epair : forall e1 e2 v1 v2,
            eval_expr e1 v1 ->
            eval_expr e2 v2 ->
            eval_epxr (Epair e1 e2) (Vpair v1 v2)
  }
}

family Imppairs.Impgen {
  Fixpoint translate_expression :=
    Case Epair := ...
                  
  family Proofs {
       Lemma translate_expression_correct:
           forall a v,
           [self].Source.Semantics.eval_expr a v ->
           forall ta, translate_expression a = OK ta ->
           [self].Target.Semantics.eval_expr ta v.
       Proof.
         Case Epair := ...
       Qed.
  }
}  

(* Inherited from Impgen *)
family Imppairs.Impshmgen { }

(* Inherited from Impgen *)                          
family Imppairs.Impminorgen { }      
