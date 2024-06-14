From NFPOP Require Import Loader.

Notation ident := nat.

Family STLCBase.
  FInductive Ty: Set :=
     | TUnit : Ty
     | TArr : Ty -> Ty -> Ty.

  FInductive Exp : Set :=     
     | EApp : Exp -> Exp -> Exp
     | EVal : Val -> Exp
     with Val : Set :=
     | VVar : ident -> Val 
     | VLam : ident -> Exp -> Val
     | VUnit : Val.
FEnd STLCBase.

Family IfExt. 
   Family Base extends STLCBase.
       FInductive Ty : Set := TBool : Ty.

       FInductive Exp : Set :=
         | EIf : Exp -> Exp -> Exp -> Exp
       with Val : Set :=
         | VTrue : Val
         | VFalse : Val.  
   FEnd Base.
   
   Family Derived extends Base.
   FEnd Derived.
FEnd IfExt.

Family ArithExt. 
   Family Base extends STLCBase.
        FInductive Ty : Set := TNat : Ty.

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
    FEnd Base.
FEnd IfExtBuild.

Family ArithExtBuild extends ArithExt.
   Family Base extends IfExtBuild.Derived. 
   FEnd Base.
FEnd ArithExtBuild.

Family STLCArithIF extends ArithExtBuild.Derived.
FEnd STLCArithIF.
