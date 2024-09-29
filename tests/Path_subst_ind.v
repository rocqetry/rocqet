From NFPOP Require Import Loader.

Family Base.
   FDefinition ident := nat.

   FInductive expr : ident -> Type := 
     | A : forall i, expr i.
FEnd Base.

Family Derived extends Base.      
FEnd Derived.
