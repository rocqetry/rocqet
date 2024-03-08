
(*
  I think we can have very high level passes that desugars the semingly valid
  source languge into a the Compcert IRs

  extensible semantic preservation forward simulation proofs
  extensible bisimulation proofs
*)

(*
Family Imp1.0 {
   Family Frontend
       Family Imp
          Inductive binary_operation : Type :=
             | Binplus
             | Binminus
             | Binmult.

          Inductive expression : Type :=
             | Evar : ident -> expr 
             | Econst : value -> expr
             | Ebinop : binary_operation -> expr -> expr -> expr.

         Inductive statement : Type :=
             | Sassign (x : var) (e : expr)    (* x = e *)
             | Sseq    (a b : stmt)            (* a ; b *)
             | Sifthenelse : expression -> statement -> statement -> statement
             | Swhile  : expression -> statement -> statement
             | Sskip : statement.

         Family Program { }
       }

       Family Sematics {
              
       }       
       

   End Frontend

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

   Family Impsharpminor {
      
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

(* Mixin with various features *)
Family Imp2.0 { }

*)





