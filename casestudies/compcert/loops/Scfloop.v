Family Scfloop extends Base. 
   Family C.     
      FInductive stmt : Type := 
        | Sdo : expr -> stmt(* evaluate expression for side effects *)        
        | Swhile : expr -> stmt -> stmt(* while loop *)
        | Sdowhile : expr -> stmt -> stmt(* do loop *)
        | Sfor: stmt -> expr -> stmt -> stmt -> stmt(* for loop *)
        | Sbreak : stmt(* break stmt *)
        | Scontinue : stmt(* continue stmt *)
   FEnd C.

   Family Clight. 
       FInductive stmt : Type := 
        | Sloop: stmt -> stmt -> stmt(* infinite loop *)
        | Sbreak : stmt(* break statement *)
        | Scontinue : stmt(* continue statement *)

        FInductive cont : Type := 
          | Kloop1: statement -> statement -> cont -> cont(* Kloop1 s1 s2 k = after s1 in Sloop s1 s2 *)
          | Kloop2: statement -> statement -> cont -> cont(* Kloop2 s1 s2 k = after s2 in Sloop s1 s2 *)

       FInductive step : genv -> state -> trace -> state -> Prop := 
         | step_loop: forall f s1 s2 k e le m,
            step (State f (Sloop s1 s2) k e le m)
                E0 (State f s1 (Kloop1 s1 s2 k) e le m)
        | step_skip_or_continue_loop1: forall f s1 s2 k e le m x,
            x = Sskip \/ x = Scontinue ->
            step (State f x (Kloop1 s1 s2 k) e le m)
                E0 (State f s2 (Kloop2 s1 s2 k) e le m)
        | step_break_loop1: forall f s1 s2 k e le m,
            step (State f Sbreak (Kloop1 s1 s2 k) e le m)
                E0 (State f Sskip k e le m)
        | step_skip_loop2: forall f s1 s2 k e le m,
            step (State f Sskip (Kloop2 s1 s2 k) e le m)
                E0 (State f (Sloop s1 s2) k e le m)
        | step_break_loop2: forall f s1 s2 k e le m,
            step (State f Sbreak (Kloop2 s1 s2 k) e le m)
                E0 (State f Sskip k e le m).
   FEnd Clight.  
   
   (* Cminor-like languages *)
   Family Cm.
     FInductive stmt : Type :=
       | Sloop: stmt -> stmt
       | Sblock: stmt -> stmt
       | Sexit: nat -> stmt.   

    FInductive cont: Type :=
        | Kblock: cont -> cont.         
    
   FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.                
      Case Kblock := (fun c call_cont_c => call_cont_c).
   FEnd call_cont.

    FRecursion is_call_cont. 
       Case Kblock := (fun c call_cont_c => False).
    FEnd is_call_cont.
    
     FInductive step : genv -> state -> trace -> state -> Prop :=
       | step_skip_block: forall ge f k e le m,
            step ge (self__Cfam.State f Sskip (Kblock k) e le m)
            E0 (self__Cfam.State f Sskip k e le m)
       | step_loop: forall ge f s k e le m,
            step ge (self__Cfam.State f (Sloop s) k e le m)
            E0 (self__Cfam.State f s (Kseq (Sloop s) k) e le m)        
       | step_block: forall ge f s k e le m,
            step ge (self__Cfam.State f (Sblock s) k e le m)
            E0 (self__Cfam.State f s (Kblock k) e le m).
   FEnd Cm.

   Family Cmtransl. 
     FRecursion transl_stmt.
       Case Sloop := (fun s1 transl_stmt_s1 =>
                            do ts <- transl_stmt_s1;
                            OK (Target.Sloop ts)).
          Case Sblock := (fun s transl_stmt_s =>
                             do ts <- transl_stmt_s;
                             OK (Target.Sblock ts)).
          Case Sexit := (fun n => OK (Target.Sexit n)).
     FEnd transl_stmt.

     FInduction transl_step_correct.      
     (* skip block *)
     + intros ge f k e le m prog tprog tge H G.
       intros T1 MSTATE. inv MSTATE.
       rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq in TR.
       unfold self__Cfamtransl.transl_stmtSskip in TR.
       monadInv TR.
       left. econstructor. split. apply plus_one. 
       (* Same as above, we need to show the cont is a Kblock *)
       apply (*self__Cfamtransl.Target.step_skip_block*) cheat.
       eapply self__Cfamtransl.match_state.
       apply TRF.
       rewrite -> self__Cfamtransl.transl_stmt_Sskip_eq.
       unfold self__Cfamtransl.transl_stmtSskip.
       reflexivity.
       apply MINJ.
       apply MCS.
       apply cheat. (* call_cont *)

     (* loop *)
     + 
       unfold self__Cfamtransl.__motiveTtransl_step_correct.
       intros ge f s k e le m prog tprog tge H G. 
       intros T1 MSTATE. inv MSTATE.            
       rewrite -> self__Cfamtransl.transl_stmt_Sloop_eq in TR.
       unfold self__Cfamtransl.transl_stmtSloop in TR.            
       monadInv TR. 
       left. econstructor. split. apply plus_one. 
       apply self__Cfamtransl.Target.step_loop.            
       eapply self__Cfamtransl.match_state; eauto.            
       - apply self__Cfamtransl.match_Kseq.  
      rewrite -> self__Cfamtransl.transl_stmt_Sloop_eq.
       unfold self__Cfamtransl.transl_stmtSloop. 
       (* (do ts <- self__Cfamtransl.transl_stmt s; OK (self__Cfamtransl.Target.Sloop ts)) =
           OK (self__Cfamtransl.Target.Sloop x) *)
       apply cheat. apply MK.     
            
     (* block *)
     + unfold self__Cfamtransl.__motiveTtransl_step_correct.
       intros ge f s k e le m prog tprog tge H G. 
       intros T1 MSTATE. inv MSTATE. 
       rewrite -> self__Cfamtransl.transl_stmt_Sblock_eq in TR.
       unfold self__Cfamtransl.transl_stmtSblock in TR.
       monadInv TR. 
       left. econstructor. split. apply plus_one. 
       apply self__Cfamtransl.Target.step_block.
       apply self__Cfamtransl.match_state with (f := f0) (lo := lo) (hi := hi) (cs := cs).
       apply TRF. apply EQ. apply MINJ. apply MCS. apply self__Cfamtransl.match_Kblock.  apply MK.
     Qed. FEnd transl_step_correct.

     
   FEnd Cmtransl.
   
   (* Lower C switch *)
   Family SimplExpr. 
   FEnd SimplExpr. 

   (* Automatically extend Cmtransl *)
   (*Family Cshmgen. 
   FEnd Cshmgen.

   Family Cminorgen. 
   FEnd Cminorgen.
   
   Family Selection. 
   FEnd Selection. *)
   
   (* needs low level control flow *)
   Family Lfam extends Cf.Lfam.
   FEnd Lfam.

FEnd Scfloop.
