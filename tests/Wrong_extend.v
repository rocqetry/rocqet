From NFPOP Require Import Loader.

Family Cfrontend.
    FDefinition ident := nat.

    FInductive constant : Type :=
      | Ointconst: nat -> constant.
    
    FInductive unary_operation : Type := Negation : unary_operation.

    FInductive binary_operation : Type :=
        | Binplus : binary_operation
        | Binminus : binary_operation
        | Binmult : binary_operation.

    FInductive expr : Type :=
        | Evar : ident -> expr
        | Econst : constant -> expr
        | Eunop : unary_operation -> expr -> expr
        | Ebinop : binary_operation -> expr -> expr -> expr.

    FInductive statement : Type :=
       | Sassign : ident -> self__Cfrontend.expr -> statement
       | Sseq    : statement -> statement -> statement
       | Sifthenelse : expr -> statement -> statement -> statement
       | Sskip : statement.

    Family Semantics.
        FInductive cont : Type :=
           | Kstop: cont
           | Kseq: statement -> cont -> cont.    
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

Family X extends SimplExpr.
FEnd X.

Family Y extends Frontendtranslation.
FEnd Y.

Check CminorVariant.Semantics.Kblock.
Check CminorVariant.Semantics.Kstop.


