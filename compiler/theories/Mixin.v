From NFPOP Require Import Loader.

Notation ident := nat.

Family STLCBase.
  FInductive Ty: Set :=
     | TUnit : Ty
     | TArr : Ty -> Ty -> Ty.

  FRecursion subst about Ty motive (fun (_ : Ty) => nat) by _rec.
       Case TUnit := 1.
       Case TArr := (fun _ n _ m => m + n).
   FEnd subst.

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
            Case TBool := 2.
       FEnd subst.
       
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
        
        FRecursion subst.
            Case TNat := 1.
        FEnd subst.

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
          (*FInductive B : Set := BB : Ty -> B.
          FDefinition c := self__Base.B_rect.*)          
          (* FInductive Ty : Set := Blah : Ty. *)
          FRecursion subst.             
          FEnd subst.
          (* FDefinition A := Ty. *)
    FEnd Base.
FEnd IfExtBuild.

Family ArithExtBuild extends ArithExt.
   Family Base extends IfExtBuild.Derived.       
   FEnd Base.
FEnd ArithExtBuild.

Family STLCArithIf extends ArithExtBuild.Derived.
FEnd STLCArithIf.
