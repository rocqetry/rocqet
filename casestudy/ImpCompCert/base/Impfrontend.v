(* A base family for Imp frontend IRs *)
family Impzero.Impfrontend {
    family Switch { ...  } 
                    
    Definition ident := string
    
    Inductive constant : Type :=
        | Ointconst: int -> constant

    Inductive unary_operation : Type := ...                              

    Inductive binary_operation : Type :=
        | Binplus
        | Binminus
        | Binmult.

     Inductive expression : Type :=
        | Evar : ident -> expression
        | Econst : constant -> expression
        | Eunop : unary_operation -> expression -> expression
        | Ebinop : binary_operation -> expr -> expr -> expr.

     Inductive statement : Type :=
        | Sassign : label -> expression -> statement
        | Sseq    : statement -> statement -> statement
        | Sifthenelse : expression -> statement -> statement -> statement        
        | Sskip : statement
        | Sblock: statement -> statement
        | Sexit: nat -> statement
        | Sswitch : Switch.switch
        (* | Sswitch: expr -> lbl_statement -> statement *)
        (* | Sloop: statement -> statement *)

     (* with lbl_statement : Type :=
           | LSnil: lbl_statement
           | LScons: option Z -> statement -> lbl_statement -> lbl_statement *)
                           

     family Program {
        Record function : Type := mkfunction {   
           (* fn_params: list ident;
           fn_vars: list ident;
           fn_temps: list ident; *)
           fn_body: statement
        }

        Inductive fundef : Type :=
          | Internal: function -> fundef          
        
        Inductive globdef : Type :=
          | Gfun (f: fundef)

        Record program : Type := mkprogram {
           prog_defs: list (ident * globdef);           
           prog_main: ident
        }
       (* Inductive program : Type := Program (ident * globaldef) *)
     }    
}
       
(* The semantics of the language *)                         
family Impzero.Impfrontend {
    family Semantics {                                        
        family Values {
            Inductive value: Type :=
              | Vint: int -> val
        }

        Inductive cont : Type :=
           | Kstop : cont
           | Kseq : statement -> cont -> cont
           | Kblock: cont -> cont                                               

         Inductive state: Type :=
           | State: forall (s: statement) (k: cont) (e: env), state        

         Definition eval_binop := ... 

         Inductive eval_expr: expression -> Values.value -> Prop :=
            | eval_Evar: forall id v,
                le!id = Some v ->
                eval_expr (Evar id) v           
            | eval_Econst: forall cst v,
                eval_constant cst = Some v ->
                eval_expr (Econst cst) v
            | eval_Eunop: forall op a1 v1 v,
                eval_expr a1 v1 ->
                eval_unop op v1 = Some v ->
                eval_expr (Eunop op a1) v
            | eval_Ebinop: forall op a1 a2 v1 v2 v,
                eval_expr a1 v1 ->
                eval_expr a2 v2 ->
                eval_binop op v1 v2 m = Some v ->
                eval_expr (Ebinop op a1 a2) v            
        
        Inductive eval_exprlist: list expression -> list Values.value -> Prop :=
          | eval_Enil:
              eval_exprlist nil nil
          | eval_Econs: forall a1 al v1 vl,
              eval_expr a1 v1 -> eval_exprlist al vl ->
              eval_exprlist (a1 :: al) (v1 :: vl).
        
        Inductive step : state -> state -> Prop :=
             | step_assign : forall st i a k n,            
                 aeval st a = n ->
                 step (State (Sassign i a) k st)
                   (State Sskip k (t_update st i n))             
             | step_seq : forall st c1 c2 k,  
                 step (State (Sseq c1 c2) k st)
                       (State c1 (Kseq c2 k) st)             
             | step_skip_seq: forall c k st,
                 step (State Sskip (Kseq c k) st)
                      (State c k st)                               
             | step_skip_block: forall f k e le m,
                 step (State f Sskip (Kblock k) e le m)
                      (State f Sskip k e le m)
             | step_ifthenelse: forall f a s1 s2 k e le m v b,
                  eval_expr e le m a v ->
                  Val.bool_of_val v b ->
                  step (State f (Sifthenelse a s1 s2) k e le m)
                       (State f (if b then s1 else s2) k e le m)
             | step_block: forall f s k e le m,
                  step (State f (Sblock s) k e le m)
                       (State f s (Kblock k) e le m)
             | step_exit_seq: forall f n s k e le m,
                 step (State f (Sexit n) (Kseq s k) e le m)
                       (State f (Sexit n) k e le m)
             | step_exit_block_0: forall f k e le m,
                 step (State f (Sexit O) (Kblock k) e le m)
                      (State f Sskip k e le m)
             | step_exit_block_S: forall f n k e le m,
                 step (State f (Sexit (S n)) (Kblock k) e le m)
                      (State f (Sexit n) k e le m)
             | step_switch: forall f islong a cases k e le m v n,
                  eval_expr e le m a v ->
                  switch_argument islong v n ->
                  step (State f (Sswitch islong a cases) k e le m)
                       (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m)
             | step_label: forall f lbl s k e le m,
                   step (State f (Slabel lbl s) k e le m)
                        (State f s k e le m)
                              
        (* (c, Kstop, st) *)
        Inductive initial_state (p: program): state -> Prop := ...           
        Inductive final_state := ...
        Field semantics := ...
    }
}

family Impzero.SourceLanguage extends Impfrontend { 
       (* Semantics for the source languages *)
       (* | KS_Ass : forall st i a k n,            (**r Computation for assignments *)
             aeval st a = n ->
             kstep (<{ i := a }>, k, st) (CSkip, k, t_update st i n)
        | KS_Seq : forall st c1 c2 k,  (**r Focusing on the left part of a sequence *)
             kstep (<{ c1 ; c2 }>, k, st) (c1, Kseq c2 k, st)
        | KS_IfTrue : forall st b c1 c2 k,  (**r Computation for conditionals *)
             beval st b = true ->
             kstep (<{ if b then c1 else c2 end }>, k, st) (c1, k, st)
        | KS_IfFalse : forall st b c1 c2 k,
             beval st b = false ->
             kstep (<{ if b then c1 else c2 end }>, k, st) (c2, k, st)
        | KS_SkipSeq: forall c k st,  (**r Resumption on [SKIP] *)
            kstep (CSkip, Kseq c k, st) (c, k, st) *)
        
}

family Impzero.MinorLanguage extends Impfrontend {
    
}


