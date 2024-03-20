(* Impsharpminor frontend IR *)
family Impzero.Impsharpminor extends Impfrontend {  
     Inductive expression : Type +=  ...        

     Inductive statement : Type += ...                

     family Semantics {
       Inductive cont: Type += ...            
                                                            
       Inductive step: state -> state -> Prop += ...
     }     
}

(* Translation from Imp -> Impsharpminor *)
family Impzero.Impshmgen extends ImpfrontendTransform {
   family Source extends Implight { }
   family Target extends Impsharpminor { }       
  
   (* This involves mostly simplification of control structures *)
    Fixpoint translate_expression := ... 
         
    Fixpoint translate_statment := ...

                                       
   (* Correctness proofs for Imp -> Impsharpminor *)      
   family Proofs {
         (*              
                           match_states
           Imp.state  ----------------------- Impsharpminor.state 
             |                                   |
             |                                   | *
             |                                   |
             v                                   v
          Imp.state' ----------------------- Impsharpminor.state'
                          match_states 
         *)
      Inductive match_cont : Imp.Semantics.cont -> [self].Semantics.cont -> Prop +=                  
         | match_Kwhile (* TODO: how does while relate to the semantics of Impsharpminor? *)
                 
      Inductive match_states : Imp.Semantics.state -> [self].Semantics.state -> Prop +=
         | match_state:
             forall f nbrk ncnt s k e le m tf ts tk te ts' tk' cu,                         
                 (TR: translate_statement cu.(prog_comp_env) nbrk ncnt s = OK ts)
                 (MTR: match_transl ts tk ts' tk')
                 (MK: match_cont k tk),
                        match_states (Imp.Semantics.State s k e)
                                     ([self].Semantics.State tf ts' tk' te le m)
}
