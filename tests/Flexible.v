Require Import Rocqet.Loader.

Notation ident := nat.
 
Family STLCBase. 
  Family X.
     FInductive Ty: Set :=
        | TUnit : Ty
        | TArr : Ty -> Ty -> Ty.
  FEnd X.

  FRecursion subst about X.Ty motive (fun (_ : X.Ty) => nat) by _rec. 
     Case TUnit := 1.
     Case TArr := (fun _ subst_domain _ subst_codomain => subst_domain + subst_codomain).
  FEnd subst.
FEnd STLCBase.

Family IfExt.
   Family Base extends STLCBase.
       Family X.
           FInductive Ty : Set := TBool : Ty.
       FEnd X.        
       
       FRecursion subst.
            Case TBool := 2.
       FEnd subst.
   FEnd Base.
   
   Family Derived extends Base.
   FEnd Derived.
FEnd IfExt.

Family TempSTLC extends STLCBase.
    Family X.    
    FInductive Ty : Set := TempExpr : Ty.
    FEnd X.

    FRecursion subst.
        Case TempExpr := 10.
    FEnd subst.
FEnd TempSTLC.

Family Temp extends IfExt.
    Family Base extends TempSTLC.       
       FRecursion subst.
       FEnd subst.
    FEnd Base.
FEnd Temp.
    
Family ArithExt. 
   Family Base extends STLCBase.
        Family X.
        FInductive Ty : Set := TNat : Ty.
        FEnd X.
        
        FRecursion subst.
            Case TNat := 1.
        FEnd subst.

       FInductive Exp : Set :=
         | EAdd : Exp -> Exp -> Exp
       with Val : Set :=
         | VNat : Exp -> nat -> Val.
   FEnd Base.
   
   Family Derived extends Base. 
   FEnd Derived.
FEnd ArithExt.

Family IfExtBuild extends IfExt.
    Family Base extends STLCBase.                              
          FRecursion subst.             
          FEnd subst.          
    FEnd Base.
FEnd IfExtBuild.

Family ArithExtBuild extends ArithExt.
   Family Base extends IfExtBuild.Derived.
   FEnd Base.
FEnd ArithExtBuild.

Family STLCArithIf extends ArithExtBuild.Derived.
FEnd STLCArithIf.
