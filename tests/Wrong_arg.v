Require Import Rocqet.Loader.

Notation ident := nat.

Family STLCBase.
  FInductive Ty: Set :=     
     | TNat : Ty. 

FEnd STLCBase.

Family STLCIf extends STLCBase.  
  FInductive Ty : Set := TBool : Ty.  
FEnd STLCIf.

Family BaseComp.
   Family STLC extends STLCBase.   
   FEnd STLC.

   Family IL.
      FInductive Ty : Set := TUnit : Ty | TCont : list Ty -> Ty.      

      FDefinition x := TUnit.
   FEnd IL.

   Family ILK extends IL.
   FEnd ILK.

   Family ILC extends IL.
   FEnd ILC.
FEnd BaseComp.

Family IfExt extends BaseComp.
   Family STLC extends STLCIf.
   FEnd STLC.

   Family IL.
       FInductive Ty : Set := TBool : Ty.
   FEnd IL.   
FEnd IfExt.
