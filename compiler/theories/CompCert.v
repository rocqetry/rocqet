From NFPOP Require Import Loader.

Notation ident := nat.

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
   FInductive statement : Type :=
      | Sloop : statement -> statement.

   Family Semantics.
       FInductive cont : Type :=
          | Kblock : cont -> cont.
   FEnd Semantics.
FEnd CminorVariant.

(*
Check CminorVariant.Semantics.Kblock.
Check CminorVariant.Semantics.Kstop.
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

*)
