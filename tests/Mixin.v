Require Import Rocqet.Loader.

Notation ident := nat.

Family STLCBase.
  FInductive Ty: Set :=
     | TUnit : Ty
     | TArr : Ty -> Ty -> Ty.

  FRecursion subst about Ty motive (fun (_ : Ty) => nat) by _rec.
     Case TUnit := 1.
     Case TArr := (fun _ n _ m => 1).
  FEnd subst.  
  
  FInduction easy_theorem
       about Ty
       motive (fun (t : Ty) => subst t = 1).
     FProof.          
     + fsimpl. reflexivity.
     + intros. fsimpl. reflexivity.
     Qed.
  FEnd easy_theorem.

  FInduction subst_theorem
       about Ty
       motive (fun (t : Ty) => self__STLCBase.subst t = 1).
    FProof.
      + fsimpl. reflexivity.
      + intros. fsimpl. reflexivity.          
    Qed.
  FEnd subst_theorem.  
  
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

       FRecursion subst.
            Case TBool := 1.
       FEnd subst.    

       FInduction easy_theorem.
       FProof.
        + fsimpl. reflexivity. 
       Qed.
       FEnd easy_theorem.

       FInduction subst_theorem.
       FProof.
        + fsimpl. reflexivity.
       Qed.
       FEnd subst_theorem.

       FInductive Exp : Set :=
         | EIf : Exp -> Exp -> Exp -> Exp
       with Val : Set :=
         | VTrue : Val
         | VFalse : Val.  
   FEnd Base.
   
   Family Derived extends Base.
   FEnd Derived.
FEnd IfExt.

Family TempSTLC extends STLCBase.
    FInductive Ty : Set := TempExpr : Ty.

    FRecursion subst.
        Case TempExpr := 1.
    FEnd subst.

    FInduction easy_theorem.
       FProof.
        + fsimpl. reflexivity. 
       Qed.
    FEnd easy_theorem.

    FInduction subst_theorem.
      FProof.
        + fsimpl. reflexivity.
      Qed.
     FEnd subst_theorem.
FEnd TempSTLC.

Family Temp extends IfExt.
    Family Base extends TempSTLC.       
       FRecursion subst.
       FEnd subst.
    FEnd Base.
FEnd Temp.
    
Family ArithExt. 
   Family Base extends STLCBase.
        FInductive Ty : Set := TNat : Ty.
        
        FRecursion subst.
            Case TNat := 1.
        FEnd subst.

        FInduction easy_theorem.
       FProof.
        + fsimpl. reflexivity. 
       Qed.
    FEnd easy_theorem.

    FInduction subst_theorem.
      FProof.
        + fsimpl. reflexivity.
      Qed.
     FEnd subst_theorem.
        
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

