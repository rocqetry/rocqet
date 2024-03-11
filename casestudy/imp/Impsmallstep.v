(* Conventional small-step semantics for Imp *)
Family Impsmallstep extends Imp1.0 {
   Family Frontend {
       Family Imp {
           (* We inherit all the inductive types, and
              we don't need to change them. We only
              want to change the semantics *)
         
       Family Sematics {
         (*
            Operational semantics.
            This is a small-step semenatics with big steps evaluation for
            booleans.
         *)
         Inductive step : (statement * state) -> (statement * state) -> Prop :=
             | Step_Ass : forall st i a n,
                 aeval st a = n ->
                 Sassign (i, a) / st ==> Sskip / (state_update st i n)
             | Step_SeqStep : forall st c1 c1' st' c2,
                 c1 / st ==> c1' / st' ->
                 Sseq (c1, c2) / st ==> Sseq (c1', c2) / st'
             | Step_SeqFinish : forall st c2,
                 Sseq (Sskip, c2) / st ==> c2 / st
             | Step_IfTrue : forall st b c1 c2,
                 beval st b = true -> (* TODO: fix this *)
                 Sifthenelse (b, c1, c2) / st ==> c1 / st
             | Step_IfFalse : forall st b c1 c2,
                 beval st b = false -> (* TODO: fix this *)
                 Sifthenelse (b, c1, c2) / st ==> c2 / st
             | Step_While : forall st b c1,
                 Swhile (b, c1) / st ==> Sifthenelse (b, Sseq(c1, Swhile (b, c1)), Sskip) / st
         where " c '/' st '==>' c' '/' st' " := (step (c,st) (c',st'))
       }

       (* Imp -> Impsharpminor *)
       Family Impshmgen { (* Nothing to do here! *) }
   }

   Family FrontendProofs {   
       Family SP {             
           Family A extends Frontend { } 
           Family B extends Frontend { }
       }
   }

   Family Impsharpminor extends Frontend {     
        Family Semantics { 
            Inductive step: state -> trace -> state -> Prop :=
                 | step_skip_seq: forall f s k e le m,
                     step (State f Sskip (Kseq s k) e le m)
                       E0 (State f s k e le m)
                 | step_skip_block: forall f k e le m,
                     step (State f Sskip (Kblock k) e le m)
                       E0 (State f Sskip k e le m)                                
                 | step_set: forall f id a k e le m v,
                     eval_expr e le m a v ->
                     step (State f (Sset id a) k e le m)
                    E0 (State f Sskip k e (PTree.set id v le) m)
                 | step_store: forall f chunk addr a k e le m vaddr v m',
                     eval_expr e le m addr vaddr ->
                     eval_expr e le m a v ->
                     Mem.storev chunk m vaddr v = Some m' ->
                     step (State f (Sstore chunk addr a) k e le m)
                       E0 (State f Sskip k e le m')                              
                 | step_seq: forall f s1 s2 k e le m,
                     step (State f (Sseq s1 s2) k e le m)
                               E0 (State f s1 (Kseq s2 k) e le m)        
                 | step_ifthenelse: forall f a s1 s2 k e le m v b,
                     eval_expr e le m a v ->
                     Val.bool_of_val v b ->
                     step (State f (Sifthenelse a s1 s2) k e le m)
                       E0 (State f (if b then s1 else s2) k e le m)              
                 | step_loop: forall f s k e le m,
                     step (State f (Sloop s) k e le m)
                       E0 (State f s (Kseq (Sloop s) k) e le m)               
                 | step_block: forall f s k e le m,
                     step (State f (Sblock s) k e le m)
                       E0 (State f s (Kblock k) e le m)               
                | step_exit_seq: forall f n s k e le m,
                    step (State f (Sexit n) (Kseq s k) e le m)
                      E0 (State f (Sexit n) k e le m)
                | step_exit_block_0: forall f k e le m,
                    step (State f (Sexit O) (Kblock k) e le m)
                      E0 (State f Sskip k e le m)
                | step_exit_block_S: forall f n k e le m,
                    step (State f (Sexit (S n)) (Kblock k) e le m)
                      E0 (State f (Sexit n) k e le m)              
                | step_switch: forall f islong a cases k e le m v n,
                    eval_expr e le m a v ->
                    switch_argument islong v n ->
                    step (State f (Sswitch islong a cases) k e le m)
                      E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m)            
               | step_label: forall f lbl s k e le m,
                   step (State f (Slabel lbl s) k e le m)
                     E0 (State f s k e le m)
               | step_goto: forall f lbl k e le m s' k',
                   find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
                   step (State f (Sgoto lbl) k e le m)
                     E0 (State f s' k' e le m)
        }

    }

   Family Impminor extends Frontend { }

   Family ImppminorSel extends Frontend { }

   Family LTL { }

   Family RTL { }

   Family Backend {
       Family Semantics { }
   }

   Family Linear extends Backend { }

   Family Mach extends Backend { }

   Family Processor {
      Family Op { }      
   } 

   Family Aarch64 extends Processor {
      Family Op { }
   }
}
