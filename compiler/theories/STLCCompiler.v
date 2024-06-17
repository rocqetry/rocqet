From NFPOP Require Import Loader.

Notation ident := nat.

Family STLCBase.
  FInductive Ty: Set :=
     | TUnit : Ty
     | TNat : Ty
     | TArr : Ty -> Ty -> Ty.

  FInductive Exp : Set :=     
     | EApp : Exp -> Exp -> Exp
     | EVal : Val -> Exp
     with Val : Set :=
     | VVar : ident -> Val 
     | VLam : ident -> Exp -> Val
     | VUnit : Val.
FEnd STLCBase.

Family STLCIf extends STLCBase.  
  FInductive Ty : Set := TBool : Ty.

  FInductive Exp : Set :=
    | EIf : Exp -> Exp -> Exp -> Exp
  with Val : Set :=
    | VTrue : Val
    | VFalse : Val.  
FEnd STLCIf.

Family BaseComp.
   Family STLC extends STLCBase.   
   FEnd STLC.

   Family IL.
      FInductive Ty : Set := TUnit : Ty | TCont : list Ty -> Ty.

      FInductive Exp : Set :=
        | ELet : ident -> Val -> Exp
        | EApp : Val -> list Val -> Exp
      with Val : Set := VUnit : Val | VVar : ident -> Val.
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
       FInductive Exp : Set := EIf : Val -> Exp -> Exp -> Exp 
       with Val : Set := Bool : bool -> Val.
   FEnd IL.   
FEnd IfExt.

Check IfExt.STLC.EIf.
Check IfExt.ILC.TBool.
Check IfExt.ILK.TBool.
Check IfExt.ILC.EIf.
