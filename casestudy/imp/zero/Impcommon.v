(* A base family for Imp frontend IRs *)
family Impzero.Impcommon {
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
        | Sswitch: bool -> expr -> lbl_statement -> statement
        | Sloop: statement -> statement

     with lbl_statement : Type :=
           | LSnil: lbl_statement
           | LScons: option Z -> statement -> lbl_statement -> lbl_statement
                           

     (* Top level programs *)
     Inductive program : Type :=
        | Program : list statement (* -> [[list function]]*) -> program
}
       
(* The semantics of the language *)                         
family Impzero.Impcommon {
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
            | step_skip_block: forall k e,
                   step (State Sskip (Kblock k) e)
                        (State Sskip k e)                               
            | step_loop: forall s k e le m,
                   step (State (Sloop s) k e)
                        (State s (Kseq (Sloop s) k) e)
            | step_block: forall f s k e,
                   step (State (Sblock s) k e)
                        (State s (Kblock k) e)               
            | step_exit_seq: forall n s k e,
                  step (State (Sexit n) (Kseq s k) e)
                       (State (Sexit n) k e)
            | step_exit_block_0: forall k e,
                  step (State (Sexit O) (Kblock k) e)
                       (State Sskip k e)
            | step_exit_block_S: forall f n k e,
                  step (State (Sexit (S n)) (Kblock k) e)
                       (State (Sexit n) k e)              
            | step_switch: forall islong a cases k e m v n,
                    eval_expr e le m a v ->
                    switch_argument islong v n -> (* TODO: evalutaion *)
                    step (State (Sswitch islong a cases) k e)
                         (State (seq_of_lbl_statement (select_switch n cases)) k e)            
            | step_label: forall lbl s k e,
                   step (State (Slabel lbl s) k e)
                        (State s k e)
        
        Inductive eval_exprlist: list expression -> list Values.value -> Prop :=
          | eval_Enil:
              eval_exprlist nil nil
          | eval_Econs: forall a1 al v1 vl,
              eval_expr a1 v1 -> eval_exprlist al vl ->
              eval_exprlist (a1 :: al) (v1 :: vl).

        (* A common small step continuation-based semantics for frontned languages *)
        Inductive step : [self].state -> [self].state -> Prop :=
             | step_assign : forall st i a k n,            
                 aeval st a = n ->
                 step (State (Sassign i a) k st)
                   (State Sskip k (t_update st i n))
             (* | step_set: forall f id a k e le m v,
                     eval_expr e le m a v -> (* TODO : fix this *)
                     step (State (Sset id a) k e)
                          (State Sskip k (PTree.set id v e)) *)                                    
             | step_seq : forall st c1 c2 k,  
                 step (State (Sseq c1 c2) k st)
                       (State c1 (Kseq c2 k) st)                             
             | step_iftrue : forall st b c1 c2 k,
                 beval st b = true ->
                 step (State (Sifthenelse b c1 c2) k st)
                       (State c1 k st)                   
             | step_iffalse : forall st b c1 c2 k,
                 beval st b = false ->
                 step (State (Sifthenelse b c1 c2) k st)
                   (State c2 k st)
             (* | step_ifthenelse: forall a s1 s2 k e le m v b,
                     eval_expr e le m a v ->
                     Val.bool_of_val v b -> (* TODO: fix this *)
                     step (State (Sifthenelse a s1 s2) k e)
                          (State (if b then s1 else s2) k e) *)
             | step_skip_seq: forall c k st,
                 step (State Sskip (Kseq c k) st)
                      (State c k st)                               
        
        (* Definitions *)        
        Definition initial_state := ...
        Definition final_state := ...
        Definition semantics := ...
    }
}
