From NFPOP Require Import Loader.

Notation ident := nat.
 
Family STLCBase. 
  Family X.
     Family X0.
     FInductive Ty: Set :=
        | TUnit : Ty
        | TArr : Ty -> Ty -> Ty.
     FEnd X0.
  FEnd X.

  Family Y.
     FRecursion subst : (t : X.X0.Ty) -> nat. 
        Case TUnit := 1.
        Case TArr domain codomain := (subst domain + subst codomain).
     FEnd subst.
  FEnd Y.
FEnd STLCBase.

Family IfExt.
   Family Base extends STLCBase.
       Family X.   
           Family X0.
           FInductive Ty : Set := TBool : Ty.
           FEnd X0.
       FEnd X.
       
       Family Y.
          FRecursion subst.
               Case TBool := 2.
          FEnd subst.
       FEnd Y.
   FEnd Base.
   
   Family Derived extends Base.
   FEnd Derived.
FEnd IfExt.

Family TempSTLC extends STLCBase.
    Family X.
       Family X0. 
          FInductive Ty : Set := TempExpr : Ty.
       FEnd X0.
    FEnd X.

    Family Y. 
    FRecursion subst.
        Case TempExpr := 10.
    FEnd subst.
    FEnd Y.
FEnd TempSTLC.

Family Temp extends IfExt.
    Family Base extends TempSTLC.       
       Family X. 
           Family X0.
              FInductive Ty : Set := AnotherExpr : nat -> Ty.
           FEnd X0.
       FEnd X.

       Family Y.
          FRecursion subst.
              Case AnotherExpr x := x.
          FEnd subst.
       FEnd Y.
    FEnd Base.
FEnd Temp.
    
Family ArithExt. 
   Family Base extends STLCBase.
        Family X.
           Family X0.
               FInductive Ty : Set := TNat : Ty.
           FEnd X0.
        FEnd X.
        
        Family Y.
        FRecursion subst.
            Case TNat := 1.
        FEnd subst.
        FEnd Y.

       FInductive Exp : Set :=
         | EAdd : Exp -> Exp -> Exp
       with Val : Set :=
         | VNat : nat -> Val.
   FEnd Base.
   
   Family Derived extends Base. 
   FEnd Derived.
FEnd ArithExt.

Family IfExtBuild extends IfExt.
    Family Base extends STLCBase.                              
          Family Y. 
             FRecursion subst.             
             FEnd subst.
          FEnd Y.          
    FEnd Base.
FEnd IfExtBuild.

Family ArithExtBuild extends ArithExt.
   Family Base extends IfExtBuild.Derived.
   FEnd Base.
FEnd ArithExtBuild.

Family STLCArithIf extends ArithExtBuild.Derived.
FEnd STLCArithIf.
