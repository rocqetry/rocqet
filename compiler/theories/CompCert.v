From NFPOP Require Import Loader.

Notation ident := nat.

Family IR.
   FInductive constant : Type :=
      | Ointconst: nat -> constant.
    
    FInductive unary_operation : Type := Negation : unary_operation.

    FInductive binary_operation : Type :=
        | Binplus : binary_operation
        | Binminus : binary_operation
        | Binmult : binary_operation.

    FInductive expr : Type :=
        | Evar : ident -> expr
        | Econst : self__IR.constant -> expr
        | Eunop : self__IR.unary_operation -> expr -> expr
        | Ebinop : self__IR.binary_operation -> expr -> expr -> expr.
      
   Family Semantics. 
      FInductive state : Type := ReturnState : state.
      FInductive step : Type :=
        | step_assign : step
        | step_skip : self__Semantics.state -> step.
   FEnd Semantics.
FEnd IR.

Family RTL extends IR.
   Family Semantics.       
      FInductive step : Type :=
        | step_store : self__Semantics.state -> step.
   FEnd Semantics.
FEnd RTL.

Family Translation.
   Family Source extends IR.
   FEnd Source.

   Family Target extends IR.
   FEnd Target.
FEnd Translation.

Family ConstFold extends Translation.
    Family Source extends RTL.
        Family Semantics. 
         FInductive step : Type :=
               | step_load : step.
        FEnd Semantics.
        
        FInductive b : self__Source.Semantics.step -> Type := 
          | BB : b self__Source.Semantics.step_load.
    FEnd Source.
FEnd ConstFold.

(* Check ConstFold.Source.Semantics.step_load. *)
(* Print RTL.Semantics.*)
(* Print Translation.Source.Semantics.*)
(* Print ConstFold.Source.Semantics.*)

Family Cfrontend.
    FInductive constant : Type :=
      | Ointconst: nat -> constant.
    
    FInductive unary_operation : Type := Negation : unary_operation.

    FInductive binary_operation : Type :=
        | Binplus : binary_operation
        | Binminus : binary_operation
        | Binmult : binary_operation.

    FInductive expr : Type :=
        | Evar : ident -> expr
        | Econst : self__Cfrontend.constant -> expr
        | Eunop : self__Cfrontend.unary_operation -> expr -> expr
        | Ebinop : self__Cfrontend.binary_operation -> expr -> expr -> expr.

    FInductive statement : Type :=
       | Sassign : ident -> self__Cfrontend.expr -> statement
       | Sseq    : statement -> statement -> statement
       | Sifthenelse : self__Cfrontend.expr -> statement -> statement -> statement
       | Sskip : statement.

    Family Semantics.
        FInductive cont : Type :=
           | Kstop: cont
           | Kseq: self__Cfrontend.statement -> cont -> cont.    
    FEnd Semantics.
FEnd Cfrontend.

Family ClightVariant extends Cfrontend.
FEnd ClightVariant.


Family CminorVariant extends Cfrontend.
   FInductive constant : Type := Unit : constant.

   FInductive statement : Type :=
      | Sloop : statement -> statement.

   Family Semantics.
       FInductive cont : Type :=
          | Kblock : cont -> cont.
   FEnd Semantics.
FEnd CminorVariant.

Family Frontendtranslation.
   Family Source extends Cfrontend.
   FEnd Source.

   Family Target extends Cfrontend.
   FEnd Target.

   Family SimulationDiagram.
   FEnd SimulationDiagram.      
FEnd Frontendtranslation.

Family SimplExpr extends Frontendtranslation.
   Family Source extends CminorVariant.
   FEnd Source.
FEnd SimplExpr.


Check CminorVariant.Semantics.Kblock.
Check CminorVariant.Semantics.Kstop.
