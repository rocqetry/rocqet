(* Compiling with paramenterized self hierachies *)

Definition ident := nat.

Module Type STLCBase_Ty_Ctx.
End STLCBase_Ty_Ctx.

Module Type STLCBase_Ty (self : STLCBase_Ty_Ctx).
  Axiom Ty : Set.
  Axiom TyUnit : Ty.
  Axiom TNat : Ty. 
  Axiom TArr : Ty -> Ty -> Ty.
End STLCBase_Ty.

Module Type STLCBase_ExpVal_Ctx.
  Include STLCBase_Ty_Ctx.
  Include STLCBase_Ty.
End STLCBase_ExpVal_Ctx.

Module Type STLCBase_ExpVal (self : STLCBase_ExpVal_Ctx).
  Axiom Exp : Set.
  Axiom Val : Set.
  Axiom EVal : Val -> Exp.
  Axiom EApp : Exp -> Exp -> Exp.
  Axiom Unit : Val.
  Axiom Var : ident -> Val.
  Axiom Lam : ident -> Exp -> Val.
End STLCBase_ExpVal.

(* Generate a concerete module for STLCBase *)
Module STLCBase.
   Inductive Ty' : Set := 
     | TyUnit' : Ty'
     | TNat' : Ty' 
     | TArr' : Ty' -> Ty' -> Ty'.
   Definition Ty := Ty'.
   Definition TyUnit := TyUnit'.
   Definition TNat := TNat'.
   Definition TArr := TArr'.
   
   Inductive Val' : Set := 
     | Unit' : Val'
     | Var' : ident -> Val'
     | Lam' : ident -> Exp' -> Val' 
    with Exp' : Set := 
      | EVal' : Val' -> Exp' 
      | EApp' : Exp' -> Exp' -> Exp'.
   
   Definition Val := Val'.
   Definition Unit := Unit'.
   Definition Var := Var'.
   Definition Lam := Lam'.
   Definition Exp := Exp'.
   Definition EVal := EVal'.
   Definition EApp := EApp'.

End STLCBase.


Module Type STLCIf_Ty_Ctx.
End STLCIf_Ty_Ctx.

Module Type STLCIf_Ty (self : STLCIf_Ty_Ctx). 
  Include STLCBase_Ty(self).
  Axiom TBool : Ty.    
End STLCIf_Ty.
Module Type STLCIf_ExpVal_Ctx. 
  Include STLCIf_Ty_Ctx.
  Include STLCIf_Ty.
End STLCIf_ExpVal_Ctx.

Module Type STLCIf_ExpVal (self : STLCIf_ExpVal_Ctx).
  Include STLCBase_ExpVal(self).
  Axiom VTrue : Val.
  Axiom VFalse : Val.
  Axiom EIf : Exp -> Exp -> Exp -> Exp.
End STLCIf_ExpVal.

(* Instantiate STLCIf *)
Module STLCIf.
  Inductive Ty' : Set := 
     | TyUnit' : Ty'
     | TNat' : Ty' 
     | TArr' : Ty' -> Ty' -> Ty'
     | TBool' : Ty'.
   Definition Ty := Ty'.
   Definition TyUnit := TyUnit'.
   Definition TNat := TNat'.
   Definition TArr := TArr'.
   Definition TBool := TBool'.
   
   Inductive Val' : Set := 
     | Unit' : Val'
     | Var' : ident -> Val'
     | Lam' : ident -> Exp' -> Val'
     | VTrue' : Val'
     | VFalse' : Val'
    with Exp' : Set := 
      | EVal' : Val' -> Exp' 
      | EApp' : Exp' -> Exp' -> Exp'
      | EIf' : Exp' -> Exp' -> Exp' -> Exp'.
   
   Definition Val := Val'.
   Definition Unit := Unit'.
   Definition Var := Var'.
   Definition Lam := Lam'.
   Definition Exp := Exp'.
   Definition EVal := EVal'.
   Definition EApp := EApp'.
   Definition VTrue := VTrue'.
   Definition VFalse := VFalse'.
End STLCIf.


Module Type BaseComp_STLC_Ctx.
End BaseComp_STLC_Ctx.

Module Type BaseComp_STLC_Ty_Ctx.
End BaseComp_STLC_Ty_Ctx.

Module Type BaseComp_STLC_Ty   
   (self__BaseComp: BaseComp_STLC_Ctx)
   (self__STLC : BaseComp_STLC_Ty_Ctx).
  Include STLCBase_Ty(self__STLC).
End BaseComp_STLC_Ty.

(* ^ Do we parameterize or just include it 
    directly?  *)
Module Type A.
 Axiom T : Set.
End A.

Module A_Impl <: A.
  Axiom T : Set.
End A_Impl.

Module BaseComp_STLC_Ctx_Impl.
End BaseComp_STLC_Ctx_Impl.

Module BaseComp_STLC_Ty_Ctx_Impl.
End BaseComp_STLC_Ty_Ctx_Impl.

Module Type B := BaseComp_STLC_Ctx <+ BaseComp_STLC_Ty_Ctx_Impl.

Module Type BaseComp_STLC_ExpVal_Ctx.  
  Include BaseComp_STLC_Ty (BaseComp_STLC_Ctx_Impl) (BaseComp_STLC_Ty_Ctx_Impl).
End BaseComp_STLC_ExpVal_Ctx.

Module Type BaseComp_STLC_ExpVal 
    (self__BaseComp : BaseComp_STLC_Ctx)
    (self__STLC : BaseComp_STLC_ExpVal_Ctx(self__BaseComp)).
  Include STLCBase_ExpVal(self__STLC).
End BaseComp_STLC_ExpVal.

Module Type BaseComp_STLC_Sig_Helper (self__BaseComp : BaseComp_STLC_Ctx).
  Include BaseComp_STLC_ExpVal_Ctx(self__BaseComp).
  Include BaseComp_STLC_ExpVal(self__BaseComp).  
End BaseComp_STLC_Sig_Helper.

Module Type BaseComp_STLC_Sig (self__BaseComp : BaseComp_STLC_Ctx).
  Declare Module STLC : BaseComp_STLC_Sig_Helper(self__BaseComp).
End BaseComp_STLC_Sig.

(* Instantiate BaseComp.STLC *)
Module BaseComp_STLC_Impl (self__BaseComp : BaseComp_STLC_Ctx) 
        <: BaseComp_STLC_Sig(self__BaseComp).
  Module STLC.
       Inductive Ty' : Set := 
     | TyUnit' : Ty'
     | TNat' : Ty' 
     | TArr' : Ty' -> Ty' -> Ty'.
   Definition Ty := Ty'.
   Definition TyUnit := TyUnit'.
   Definition TNat := TNat'.
   Definition TArr := TArr'.
   
   Inductive Val' : Set := 
     | Unit' : Val'
     | Var' : ident -> Val'
     | Lam' : ident -> Exp' -> Val' 
    with Exp' : Set := 
      | EVal' : Val' -> Exp' 
      | EApp' : Exp' -> Exp' -> Exp'.
   
   Definition Val := Val'.
   Definition Unit := Unit'.
   Definition Var := Var'.
   Definition Lam := Lam'.
   Definition Exp := Exp'.
   Definition EVal := EVal'.
   Definition EApp := EApp'.
  End STLC.
End BaseComp_STLC_Impl.

Module Type BaseComp_IL_Ctx.
  Include BaseComp_STLC_Sig.
End BaseComp_IL_Ctx.

Module Type BaseComp_IL_Ty_Ctx (self__BaseComp : BaseComp_IL_Ctx).
End BaseComp_IL_Ty_Ctx.

Module Type BaseComp_IL_Ty 
  (self__BaseComp : BaseComp_IL_Ctx)
  (self__IL : BaseComp_IL_Ty_Ctx(self__BaseComp)).  
  Axiom Ty : Set.
  Axiom TUnit : Ty.
  Axiom TCont : list Ty -> Ty.
End BaseComp_IL_Ty.

Module Type BaseComp_IL_Val_Ctx (self__BaseComp : BaseComp_IL_Ctx).
  Include BaseComp_IL_Ty_Ctx.
End BaseComp_IL_Val_Ctx.




