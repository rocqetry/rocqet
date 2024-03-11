(*
  I think we can have very high level passes that desugars the semingly valid
  source languge into a the Compcert IRs

  extensible semantic preservation forward simulation proofs
  extensible bisimulation proofs
*)

Family Imp1.0 {
   Family Frontend {
       Family Imp {
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
       }

       Family Sematics {
         Definition state = total_map nat (* From Maps.v *)

         Reserved Notation " c '/' st '==>' c' '/' st' " (at level 40, st at level 39, c' at level 39)

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
   }

   Family FrontendProofs {       
       Family SP {
            Lemma compile_com_correct_terminating: forall C st c st',
                c / st \\ st' ->
                forall stk pc,
                codeseq_at C pc (compile_com c) -> star (transition C) {
                    intros.
                    
                }
             
           Family A extends Frontend { } 
           Family B extends Frontend { }
       }
   }

   Family Impsharpminor extends Frontend {
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
        | Sstore : memory_chunk -> expr -> expr -> stmt                
        | Sseq: stmt -> stmt -> stmt
        | Sifthenelse: expr -> stmt -> stmt -> stmt        
        | Sblock: stmt -> stmt
        | Sexit: nat -> stmt
        | Sswitch: bool -> expr -> lbl_stmt -> stmt
        | Sloop: stmt -> stmt        
        | Slabel: label -> stmt -> stmt
        | Sgoto: label -> stmt                                              

        with lbl_stmt : Type :=
           | LSnil: lbl_stmt
           | LScons: option Z -> stmt -> lbl_stmt -> lbl_stmt.


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

(* Imp with pairs *) 
Family Imppairs extends Imp1.0 { }

(* Imp w while loops *)
Family Impwwhile extends Imp1.0 { }

(* Add continue to Imp *)
Family Impwcontinue extends Imp1.0 { }

(* Add breaks to Imp *)
Family Impwbreak extends Imp1.0 { }

(* Imp with for loops *)
Family Impfor extends Imp1.0 { }

(* Imp with labels and goto *)
Family Impgoto extends Imp1.0 { }

(* Imploops is a mixins of all loop features *)
Family Imploops extends Imp1.0 { }

(* Imp w memory extensions *)
Family Impmemory extends Imp1.0 { }

Family Impfunctions extends Imp1.0 { }

(* Imp w different integer and float sizes *)
Family Impnumbers extends Imp1.0 { }

(* Mixin with various features *)
Family Imp2.0 { }





