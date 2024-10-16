Require Import Base.

(* control flow: label and goto *)

Family Cf extends Base. 
   Family C.     
      FInductive stmt : Type := 
        | Slabel : label -> stmt -> stmt
        | Sgoto : label -> stmt.
   FEnd C.
   
   Family Cfam.
     FInductive stmt : Type :=         
       | Slabel : label -> stmt -> stmt
       | Sgoto : label -> stmt.

     FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect. 
           Case Sskip := (fun lbl k => None).
           Case Sset := (fun id e lbl k => None).
           Case Sseq := (fun s1 find_label_s1 s2 find_label_s2 => fun lbl k => 
                          match find_label_s1 lbl (Kseq s2 k) with 
                          | Some sk => Some sk
                          | None => find_label_s2 lbl k end).
           Case Sifthenelse := (fun e s1 find_label_s1 s2 find_label_s2 => fun lbl k => 
                                    match find_label_s1 lbl k with 
                                    | Some sk => Some sk 
                                    | None => find_label_s2 lbl k end).
           Case Sloop := (fun s1 find_label_s1 => fun lbl k => 
                                    find_label_s1 lbl (Kseq (Sloop s1) k)).                                         
           Case Sblock := (fun s1 find_label_s1 => fun lbl k => find_label_s1 lbl (Kblock k)).
           Case Sexit := (fun n lbl k => None).
           Case Sreturn := (fun _ lbl k => None).
           Case Slabel := (fun lbl' s find_label_s => fun lbl k => 
                                  if ident_eq lbl lbl' then 
                                  Some(s, k) else find_label_s lbl k).
           Case Sgoto := (fun label lbl k => None).
      FEnd find_label.
    
     FInductive step : genv -> state -> trace -> state -> Prop :=
      | step_label: forall ge f lbl s k e le m,
        step ge (self__Cfam.State f (Slabel lbl s) k e le m)
          E0 (self__Cfam.State f s k e le m)
      | step_goto: forall ge f lbl k e le m s' k',
          find_label (function_body f) lbl (call_cont k) = Some(s', k') ->
          step ge (self__Cfam.State f (Sgoto lbl) k e le m)
            E0 (self__Cfam.State f s' k' e le m).
   FEnd Cfam.

   Family Cfamtransl.
      FRecursion transl_stmt. 
        Case Slabel := (fun lbl s transl_stmt_s =>                          
                            do ts <- transl_stmt_s;
                            OK (Target.Slabel lbl ts)).
          Case Sgoto := (fun lbl => OK (Target.Sgoto lbl)).
      FEnd transl_stmt.
      
      FInduction transl_find_label about Source.stmt motive
         (fun (s : Source.stmt) => forall k ts tk lbl,
              transl_stmt s = OK ts -> 
              match_cont k tk -> 
              match Source.find_label s lbl k with
              | None => Target.find_label ts lbl tk = None
              | Some(s', k') =>
                  exists ts', exists tk',
                    Target.find_label ts lbl tk = Some(ts', tk')
                 /\ transl_stmt s' = OK ts'
                 /\ match_cont k' tk'
              end).
      FProof.
      (* Skip *)
      + apply cheat.
      (* Set *)
      + apply cheat.
      (* Seq *)
      + apply cheat.
      (* Sifthenelse *)
      + apply cheat.
      (* Sloop *)
      + apply cheat.
      (* Sblock *)
      + apply cheat.
      (* Sexit *)
      + apply cheat.
       (* Sreturn *)
      + apply cheat.
       (* Slabel *)
      + apply cheat.
       (* Sgoto *)
      + apply cheat.
      Qed. FEnd transl_find_label.
       
      FLemma transl_find_label_body:
         forall f tf k tk lbl s' k',
         transl_function f = OK tf ->
         match_cont k tk ->
         Source.find_label (Source.function_body f) lbl (Source.call_cont k) = Some (s', k') ->
         exists ts', exists tk',
            Target.find_label (Target.function_body tf) lbl (Target.call_cont tk) = Some(ts', tk')
         /\ transl_stmt s' = OK ts'
         /\ match_cont k' tk'.
      FProofLemma.
      Admitted. CloseFLemma.

      FInduction transl_step_correct. 
      FProof. 
      (* label *)
      + unfold self__Cfamtransl.__motiveTtransl_step_correct.
        intros ge f lbl s k e le m prog tprog tge H G. 
        intros T1 MSTATE. inv MSTATE. 
        rewrite -> self__Cfamtransl.transl_stmt_Slabel_eq in TR.
        unfold self__Cfamtransl.transl_stmtSlabel in TR.
        monadInv TR.
        left. econstructor. split. apply plus_one. 
        apply self__Cfamtransl.Target.step_label.
        eapply self__Cfamtransl.match_state; eauto.         
            
      (* goto *)
      + unfold self__Cfamtransl.__motiveTtransl_step_correct.
        intros ge f lbl k e le m s' k' FL prog tprog tge H G. 
        intros T1 MSTATE. inv MSTATE.
        exploit self__Cfamtransl.transl_find_label; eauto. intros.
        rewrite -> self__Cfamtransl.transl_stmt_Sgoto_eq in TR.
        unfold self__Cfamtransl.transl_stmtSgoto in TR.
        monadInv TR.
        exploit self__Cfamtransl.transl_find_label_body; eauto. intros [ts' [tk' [A [B C]]]].       
        left. econstructor. split. apply plus_one.
        apply self__Cfamtransl.Target.step_goto.
        exact A.            
        eapply self__Cfamtransl.match_state; eauto.
      Qed. FEnd transl_step_correct. 

   FEnd Cfamtransl.
   
   Family Lfam.
      FInductive instruction: Type :=
        | Llabel: label -> instruction
        | Lgoto: label -> instruction.

      Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
        match c with
        | nil => None
        | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
      end.

      FInductive step: genv -> state -> trace -> state -> Prop :=
          | exec_Llabel:
              forall s f sp lbl b rs m,
              step (State s f sp (Llabel lbl :: b) rs m)
                E0 (State s f sp b rs m)
          | exec_Lgoto:
              forall s f sp lbl b rs m b',
              find_label lbl f.(fn_code) = Some b' ->
              step (State s f sp (Lgoto lbl :: b) rs m)
                E0 (State s f sp b' rs m)
   FEnd Lfam.

   Family Lineartransl. 
   FEndn Lineartransl.

FEnd Cf.
