Require Import Rocqet.Loader.

Axiom cheat : forall {X}, X.
Notation signature := nat.
Notation ident := nat.
Notation Z := nat.

Family Imp. 
   Family Cfam.
      FOpaque Definition function : Type := cheat.
   FEnd Cfam.

   Family Cfamtransl.
      Family Source extends Cfam.
      FEnd Source.

      Family Target extends Cfam.
      FEnd Target.
   FEnd Cfamtransl.

   Family Csharpminor extends Cfam.
       MetaData fn.
       Record fn : Type := mkfunction {
         fn_sig: signature;
         fn_params: list ident;
         fn_vars: list (ident * Z);
         fn_temps: list ident;         
       }.
       FEnd fn.
       
       FOverride Definition function := fn.
   FEnd Csharpminor.

   Family Cminor extends Cfam.
     MetaData fn.
     Record fn : Type := mkfunction {
        fn_sig: signature;
        fn_params: list ident;
        fn_vars: list ident;
        fn_stackspace: Z;        
     }.
     FEnd fn.

     FOverride Definition function := fn.
   FEnd Cminor.

   Family Cminorgen extends Cfamtransl.
       Family Source extends Csharpminor.
       FEnd Source.
   FEnd Cminorgen.
FEnd Imp.
