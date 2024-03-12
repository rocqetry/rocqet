Family Impzero {
   (* A base family for Imp frontend languages *)
   Family Impcommon { }

   Family ImpcommonProofs {   
     (* extensible semantic preservation proofs *)
     Family SP {                         
       Family A extends Impcommon { }
       Family B extends Impcommon { }
     }
   }      
           
   Family Imp extends Impcommom {
     Inductive binary_operation : Type :=
        | Binplus
        | Binminus
        | Binmult.

     Inductive expression : Type :=
        | Evar : ident -> expr 
        | Econst : value -> expr
        | Ebinop : binary_operation -> expr -> expr -> expr.

     Inductive statement : Type :=
        | Sassign : label -> expression -> statement
        | Sseq    : statement -> statement -> statement
        | Sifthenelse : expression -> statement -> statement -> statement
        | Swhile  : expression -> statement -> statement
        | Sskip : statement.

       (* How do we encode this in a family hierarchy?

       What about families that don't have functions? 

       Record function : Type := mkfunction {
             fn_sig: signature;
             fn_params: list ident;
             fn_vars: list (ident * Z);
             fn_temps: list ident;
             fn_body: stmt
         }.

       Definition fundef := AST.fundef function.

       Definition program : Type := AST.program fundef unit. *)
       (* A toplevel program *)
     Family Program { }

     Family Semantics {
         Definition env = total_map nat (* From Maps.v *)

         (* Continuations *)                                    
         Inductive cont : Type :=
           | Kstop : cont
           | Kseq : statement -> cont -> cont
           | Kwhile : expression -> statement -> cont -> cont

         (* States *)
         Inductive state: Type :=
             | State: forall (s: statement) (k: cont) (e: env), state

         Inductive step : state -> state -> Prop :=             
             | KS_Ass : forall st i a k n,            
                 aeval st a = n ->
                 step (State (Sassign i a) k st)
                       (State Sskip k (t_update st i n))           
             | KS_Seq : forall st c1 c2 k,  
                 step (State (Sseq c1 c2) k st)
                       (State c1 (Kseq c2 k) st)                             
             | KS_IfTrue : forall st b c1 c2 k,
                 beval st b = true ->
                 step (State (Sifthenelse b c1 c2) k st)
                       (State c1 k st)                   
             | KS_IfFalse : forall st b c1 c2 k,
                 beval st b = false ->
                 step (State (Sifthenelse b c1 c2) k st)
                       (State c2 k st)          
             | KS_WhileTrue : forall st b c k,
                 beval st b = true ->
                 step (State (Swhile b c) k st)
                       (State c (Kwhile b c k) st)
             | KS_WhileFalse : forall st b c k,
                 beval st b = false ->
                 step (State (Swhile b c) k st)
                       (State Sskip k st)                              
             | KS_SkipSeq: forall c k st,
                 step (State Sskip (Kseq c k) st)
                       (State c k st)                   
             | KS_SkipWhile: forall b c k st,
                 step (State Sskip (Kwhile b c k) st)
                       (State (Swhile b c) k st)
     }     
 }
       

 Family Impsharpminor extends Impcommon {
     Inductive constant : Type :=
        | Ointconst: int -> constant       
        | Ofloatconst: float -> constant   
        | Osingleconst: float32 -> constant
        | Olongconst: int64 -> constant.   

     Inductive expression : Type :=
        | Evar : ident -> expression                
        | Eaddrof : ident -> expression             
        | Econst : constant -> expression       
        | Eunop : unary_operation -> expression -> expression  
        | Ebinop : binary_operation -> expression -> expression -> expression
        | Eload : memory_chunk -> expression -> expression. 

     Inductive stmt : Type :=
        | Sskip: stmt
        | Sset : ident -> expr -> stmt        
        | Sseq: stmt -> stmt -> stmt
        | Sifthenelse: expr -> stmt -> stmt -> stmt        
        | Sblock: stmt -> stmt
        | Sexit: nat -> stmt
        | Sswitch: bool -> expr -> lbl_stmt -> stmt
        | Sloop: stmt -> stmt

        with lbl_stmt : Type :=
           | LSnil: lbl_stmt
           | LScons: option Z -> stmt -> lbl_stmt -> lbl_stmt.


     Family Semantics {
         Inductive cont: Type :=
            | Kstop: cont
            | Kseq: stmt -> cont -> cont
            | Kblock: cont -> cont      

         (* States *)
         Inductive state: Type :=
             | State: forall (s: statement) (k: cont) (e: env), state
                                                            
            Inductive step: state -> state -> Prop :=
                 | step_skip_seq: forall s k e,
                     step (State Sskip (Kseq s k) e)
                          (State s k e)
                 | step_skip_block: forall k e,
                     step (State Sskip (Kblock k) e)
                          (State Sskip k e)                                
                 | step_set: forall f id a k e le m v,
                     eval_expr e le m a v -> (* TODO : fix this *)
                     step (State (Sset id a) k e)
                          (State Sskip k (PTree.set id v e))                 
                 | step_seq: forall s1 s2 k e,
                     step (State (Sseq s1 s2) k e)
                          (State s1 (Kseq s2 k) e)        
                 | step_ifthenelse: forall a s1 s2 k e le m v b,
                     eval_expr e le m a v ->
                     Val.bool_of_val v b -> (* TODO: fix this *)
                     step (State (Sifthenelse a s1 s2) k e)
                          (State (if b then s1 else s2) k e)              
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
                         (State (seq_of_lbl_stmt (select_switch n cases)) k e)            
               | step_label: forall lbl s k e,
                   step (State (Slabel lbl s) k e)
                        (State s k e)               
       }

     (* Translation from Imp -> Impsharpminor *)
       Family Impshmgen extends {
          (* This involves mostly simplification of control structures *)
             Family Proofs extends Impcommonproofs {
            (*
               <<
                                     match_states
                    Imp.state  ----------------------- Impsharpminor.state 
                      |                                   |
                      |                                   | *
                      |                                   |
                      v                                   v
                   Imp.state' ----------------------- Impsharpminor.state'
                                     match_states 
             *)

              Inductive match_cont : Imp.Semantics.cont -> [self].Semantics.cont -> Prop :=
                 | match_Kstop: forall ce tyret nbrk ncnt,
                        match_cont tyret ce nbrk ncnt Imp.Semantics.Kstop Kstop
                 | match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
                       transl_statement ce tyret nbrk ncnt s = OK ts ->
                       match_cont ce tyret nbrk ncnt k tk ->
                       match_cont ce tyret nbrk ncnt
                                  (Imp.Semantics.Kseq s k)
                                  (Kseq ts tk)
                  | match_Kwhile 
                 
              Inductive match_states : Imp.Semantics.state -> [self].Semantics.state -> Prop :=
                 | match_state
           }
       }

    }

   Family Impminor extends Frontend {

   }

   Family ImppminorSel extends Frontend {

   }

   Family LTL {

   }

   Family RTL {

   }

   Family Backend {
       Family Semantics { }
   }

   Family Linear extends Backend {
          
   }

   Family Mach extends Backend {

   }

   Family Processor {
      Family Op { }      
   } 

   Family Aarch64 extends Processor {
      Family Op { }
   }
}


