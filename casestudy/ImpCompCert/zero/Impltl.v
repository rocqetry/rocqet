
family Impzero.LTL extends Impbackend {
    Definition node := positive

    Inductive instruction += 
      | Lbranch (s: node)
}

family Impzero.LTL.Semantics {
  Inductive step : state -> state -> Prop += 
     | exec_Lbranch: forall s f sp pc bb rs m,
         step (Block s f sp (Lbranch pc :: bb) rs m)
              (State s f sp pc rs m)
}

