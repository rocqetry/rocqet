(* Compiling with paramenterized self hierarchies *)
(* https://stackoverflow.com/questions/48837996/import-module-vs-include-module-in-coq-module-system/49717951 *)

Module Type X.
    Axiom data : nat.
End X.

Module Type Y.
   Axiom datacell : nat.
End Y.

Module In (y : Y).
  (* Definition data := y.datacell.*)
End In.

Module YFake.
  Include Y.
End YFake.

Module Inc := In YFake.

(*Print Assumptions Inc.data*)


Module Type Z.
   Axiom atomicdata : nat.
End Z.

Module Type G.
    Declare Module T : Z.
End G.

Module Ix (g : G).
End Ix.  

Module I.
  Module T.
    Definition atomicdata := 10.
    Definition data := 10.
  End T.

  Include Ix.
End I.

Module E (x : X) (y : Y) (z : Z).
   Definition x := 10.
End E.

Module B.  
  Definition data := 10.      
  
  Module Inner.    
    Module Ctx.
      Definition data := B.data.
    End Ctx.
    
    Definition datacell := 10.        

    Module InnerInner.      
      Module Ctx.
        Definition datacell := Inner.datacell.
      End Ctx.

      Include Z.
      Include E Inner.Ctx InnerInner.Ctx.

    End InnerInner.    
  End Inner. 
End B.

Print B.

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

Module Type BaseComp_STLC_Ty_Ctx
   (self__BaseComp: BaseComp_STLC_Ctx).
End BaseComp_STLC_Ty_Ctx.

Module Type BaseComp_STLC_Ty   
   (self__BaseComp: BaseComp_STLC_Ctx)
   (self__STLC : BaseComp_STLC_Ty_Ctx self__BaseComp).
  Include STLCBase_Ty(self__STLC).
End BaseComp_STLC_Ty.

Module Type BaseComp_STLC_ExpVal_Ctx
  (self__BaseComp: BaseComp_STLC_Ctx).  
  Include BaseComp_STLC_Ctx.
  Include BaseComp_STLC_Ty (self__BaseComp).
End BaseComp_STLC_ExpVal_Ctx.

Module Type BaseComp_STLC_ExpVal 
    (self__BaseComp : BaseComp_STLC_Ctx)
    (self__STLC : BaseComp_STLC_ExpVal_Ctx self__BaseComp).
  Include STLCBase_ExpVal(self__STLC).
End BaseComp_STLC_ExpVal.

Module Type BaseComp_STLC_Sig_Helper (self__BaseComp : BaseComp_STLC_Ctx).  
  Include BaseComp_STLC_ExpVal_Ctx.
  Include BaseComp_STLC_ExpVal
    (self__BaseComp).  
End BaseComp_STLC_Sig_Helper.

Module Type BaseComp_STLC_Sig (self__BaseComp : BaseComp_STLC_Ctx).
  Declare Module STLC : BaseComp_STLC_Sig_Helper(self__BaseComp).
End BaseComp_STLC_Sig.

(* Instantiate BaseComp.STLC *)
Module BaseComp_STLC_Impl (self__BaseComp : BaseComp_STLC_Ctx) 
        <: BaseComp_STLC_Sig(self__BaseComp).
  Module STLC := STLCBase.
End BaseComp_STLC_Impl.

Module Type BaseComp_Ident_Ctx.
  Include BaseComp_STLC_Ctx.
  Include BaseComp_STLC_Sig.
End BaseComp_Ident_Ctx.

Module Type BaseComp_Ident_Sig
  (self__BaseComp : BaseComp_Ident_Ctx).
  Axiom Ident : Set.
End BaseComp_Ident_Sig.

Module BaseComp_Ident 
  (self__BaseComp : BaseComp_Ident_Ctx) 
  <: BaseComp_Ident_Sig (self__BaseComp).
  Definition Ident := nat.
End BaseComp_Ident.

Module Type BaseComp_IL_Ctx.
  Include BaseComp_Ident_Ctx.
  Include BaseComp_Ident_Sig.
End BaseComp_IL_Ctx.

Module Type BaseComp_IL_Ty_Ctx
  (self__BaseComp : BaseComp_IL_Ctx).
End BaseComp_IL_Ty_Ctx.

Module Type BaseComp_IL_Ty 
  (self__BaseComp : BaseComp_IL_Ctx)
  (self__IL : BaseComp_IL_Ty_Ctx self__BaseComp).  
  Axiom Ty : Set.
  Axiom TUnit : Ty.
  Axiom TCont : list Ty -> Ty.
End BaseComp_IL_Ty.
  
Module Type BaseComp_IL_Val_Ctx
  (self__BaseComp : BaseComp_IL_Ctx).
  Include BaseComp_IL_Ty_Ctx (self__BaseComp).
  Include BaseComp_IL_Ty (self__BaseComp).
End BaseComp_IL_Val_Ctx.

Module Type BaseComp_IL_Val
  (self__BaseComp : BaseComp_IL_Ctx)
  (self__IL : BaseComp_IL_Val_Ctx self__BaseComp).
  Axiom Val : Set.
  Axiom Unit : Val.
  Axiom Var : self__BaseComp.Ident -> Val.
End BaseComp_IL_Val.

Module Type BaseComp_IL_Exp_Ctx 
   (self__BaseComp : BaseComp_IL_Ctx).
  Include BaseComp_IL_Val_Ctx (self__BaseComp).
  Include BaseComp_IL_Val (self__BaseComp).
End BaseComp_IL_Exp_Ctx.

Module Type BaseComp_IL_Exp 
  (self__BaseComp : BaseComp_IL_Ctx)  
  (self__IL : BaseComp_IL_Exp_Ctx self__BaseComp).
  Axiom Exp : Set.
  Axiom ELet : self__BaseComp.Ident -> self__IL.Val -> Exp -> Exp.
  Axiom EApp : self__IL.Val -> list self__IL.Val -> Exp.
  Axiom EHalt : self__IL.Val -> Exp.  
End BaseComp_IL_Exp.

Module Type BaseComp_IL_Sig_Helper (self__BaseComp : BaseComp_IL_Ctx).
  Include BaseComp_IL_Exp_Ctx (self__BaseComp).
  Include BaseComp_IL_Exp (self__BaseComp).
  Module Type Ty := BaseComp_IL_Ty.
  Module Type Val := BaseComp_IL_Val.
End BaseComp_IL_Sig_Helper.

Module Type BaseComp_IL_Sig (self__BaseComp : BaseComp_IL_Ctx).
  Declare Module IL : BaseComp_IL_Sig_Helper self__BaseComp.
End BaseComp_IL_Sig.



(* Instantiate BaseComp.IL *)
Module BaseComp_IL_Impl (self__BaseComp : BaseComp_IL_Ctx)
     <: BaseComp_IL_Sig (self__BaseComp).
    Module IL.
    Inductive Ty' := TUnit' | TCont' (ts : list Ty').
    Definition Ty := Ty'.
    Definition TUnit := TUnit'.
    Definition TCont := TCont'.

    Inductive Val' := Unit' | Var' (x : self__BaseComp.Ident).
    Definition Val := Val'.
    Definition Unit := Unit'.
    Definition Var := Var'.

    Inductive Exp' := 
      | ELet' (x : self__BaseComp.Ident) (v : Val) (e : Exp')
      | EApp' (v : Val) (vs : list Val) 
      | EHalt' (v : Val).
    Definition Exp := Exp'.
    Definition ELet := ELet'.
    Definition EApp := EApp'.
    Definition EHalt := EHalt'.    
    Module Type Ty := BaseComp_IL_Ty.
    Module Type Val := BaseComp_IL_Val.
  End IL.
End BaseComp_IL_Impl.

(* ILK *)
Module Type BaseComp_ILK_Ctx.
  Include BaseComp_IL_Ctx.
  Include BaseComp_IL_Sig.
End BaseComp_ILK_Ctx.

Print BaseComp_ILK_Ctx.

Module STL.

Definition y := 10.

Inductive ask := yes | no.

End STL.

(* for final families *)
Module Type BaseComp_ILK_Sig_ (self__BaseComp : BaseComp_ILK_Ctx).
  (* late binding inheritance *)
  Module ILK := self__BaseComp.IL.
  (* non late binding inheritance *)
  Module J := STL.
  
  (*Declare Module ILK : BaseComp_IL_Sig_Helper self__BaseComp := self__BaseComp.IL.*)
  
  (* with Module := self__BaseComp.IL.                                               

  Include BaseComp_IL_Sig (self__BaseComp) with Module IL := ILK.*)
End BaseComp_ILK_Sig_.

Module Type Ctx.
Include BaseComp_ILK_Ctx.
Include BaseComp_ILK_Sig_.
End Ctx.

Module R (self: Ctx).

(* Check self.J.y.*) 

Definition y := self.IL.TUnit.
Definition x := self.ILK.TCont (y :: nil).

End R.

Module Type BaseComp_ILK_Ty_Ctx
  (self__BaseComp : BaseComp_ILK_Ctx).
End BaseComp_ILK_Ty_Ctx.

Module A.
  Include BaseComp_ILK_Ctx.
End A.  

Module A0.
  Include BaseComp_ILK_Ty_Ctx A.
End A0.  

Module Type BaseComp_ILK_Ty 
  (self__BaseComp : BaseComp_ILK_Ctx)
  (self__ILK : BaseComp_ILK_Ty_Ctx self__BaseComp).
  Include self__BaseComp.IL.Ty (self__BaseComp) (self__ILK).
  (* Include BaseComp_IL_Ty (self__BaseComp) (self__ILK).*)
End BaseComp_ILK_Ty.
  
Module Type BaseComp_ILK_Val_Ctx
  (self__BaseComp : BaseComp_ILK_Ctx).
  Include BaseComp_ILK_Ty_Ctx self__BaseComp.
  Include BaseComp_ILK_Ty (self__BaseComp).
End BaseComp_ILK_Val_Ctx.

Module Type BaseComp_ILK_Val
  (self__BaseComp : BaseComp_ILK_Ctx)
  (self__ILK : BaseComp_ILK_Val_Ctx self__BaseComp).
  Include self__BaseComp.IL.Val (self__BaseComp) (self__ILK).
  
  (* Include BaseComp_IL_Val (self__BaseComp) (self__ILK).*)
  
  (* Axiom Lam : list ident -> self.Exp -> Val. *)
End BaseComp_ILK_Val.

Module Type BaseComp_ILK_Exp_Ctx
  (self__BaseComp : BaseComp_ILK_Ctx).
  Include BaseComp_ILK_Val_Ctx self__BaseComp.
  Include BaseComp_ILK_Val (self__BaseComp). 
End BaseComp_ILK_Exp_Ctx.

Module Type BaseComp_ILK_Exp 
  (self__BaseComp : BaseComp_ILK_Ctx)  
  (self__ILK : BaseComp_ILK_Exp_Ctx self__BaseComp).
  Include BaseComp_IL_Exp (self__BaseComp) (self__ILK).
End BaseComp_ILK_Exp.

Module Type BaseComp_ILK_Sig_Helper (self__BaseComp : BaseComp_ILK_Ctx).
  Include BaseComp_ILK_Exp_Ctx self__BaseComp.
  Include BaseComp_ILK_Exp (self__BaseComp) (* BaseComp_ILK_Exp_Ctx_Impl *).
End BaseComp_ILK_Sig_Helper.

Module Type T (self__BaseComp : BaseComp_ILK_Ctx) := BaseComp_ILK_Exp_Ctx self__BaseComp <+ BaseComp_ILK_Exp self__BaseComp.

Module Type BaseComp_ILK_Sig (self__BaseComp : BaseComp_ILK_Ctx).
   Module ILK := BaseComp_ILK_Exp_Ctx self__BaseComp <+ BaseComp_ILK_Exp self__BaseComp.
End BaseComp_ILK_Sig.

(*Module Type BaseComp_ILK_Sig (self__BaseComp : BaseComp_ILK_Ctx).
  Declare Module ILK : BaseComp_ILK_Sig_Helper (self__BaseComp).
End BaseComp_ILK_Sig. *)

(* Instantiate BaseComp.ILK *)
Module BaseComp_ILK_Impl (self__BaseComp : BaseComp_ILK_Ctx)
        <: BaseComp_ILK_Sig (self__BaseComp).
  Module ILK.    
   Inductive Ty' := TUnit' | TCont' (ts : list Ty').
    Definition Ty := Ty'.
    Definition TUnit := TUnit'.
    Definition TCont := TCont'.

    Inductive Val' := Unit' | Var' (x : self__BaseComp.Ident).
    (* Lam (x : list string) (e : Exp) *)
    Definition Val := Val'.
    Definition Unit := Unit'.
    Definition Var := Var'.

    Inductive Exp' := 
      | ELet' (x : self__BaseComp.Ident) (v : Val) (e : Exp')
      | EApp' (v : Val) (vs : list Val) 
      | EHalt' (v : Val).
    Definition Exp := Exp'.
    Definition ELet := ELet'.
    Definition EApp := EApp'.
    Definition EHalt := EHalt'.    
  End ILK.
  (* Definition f := self.IL.Unit. 
  Check f.*)
End BaseComp_ILK_Impl.

(* ILC *)

Module Type BaseComp_ILC_Ctx.
  Include BaseComp_ILK_Ctx.
  Include BaseComp_ILK_Sig.
End BaseComp_ILC_Ctx.

Module Type BaseComp_ILC_Ty_Ctx 
   (self__BaseComp : BaseComp_ILC_Ctx).
End BaseComp_ILC_Ty_Ctx.

Module Type BaseComp_ILC_Ty 
  (self__BaseComp : BaseComp_ILC_Ctx)
  (self__ILC : BaseComp_ILC_Ty_Ctx self__BaseComp).  
  
  Include BaseComp_IL_Ty (self__BaseComp) (self__ILC).
  Axiom TVar : self__BaseComp.Ident -> Ty.
  Axiom TExist : self__BaseComp.Ident -> Ty -> Ty.
End BaseComp_ILC_Ty.
  
Module Type BaseComp_ILC_Val_Ctx
   (self__BaseComp : BaseComp_ILC_Ctx).
  Include BaseComp_ILC_Ty_Ctx self__BaseComp.
  Include BaseComp_ILC_Ty (self__BaseComp).
End BaseComp_ILC_Val_Ctx.

Module Type BaseComp_ILC_Val 
  (self__BaseComp : BaseComp_ILC_Ctx)
  (self__ILC : BaseComp_ILC_Val_Ctx self__BaseComp).
  Include BaseComp_IL_Val (self__BaseComp) (self__ILC).
  (* Axiom Lam : list ident -> self.Exp -> Val. *)
  Axiom Pack : self__ILC.Ty -> Val -> Val.
  Axiom Name : self__BaseComp.Ident -> Val.
End BaseComp_ILC_Val.

Module Type BaseComp_ILC_Exp_Ctx
   (self__BaseComp : BaseComp_ILC_Ctx).
  Include BaseComp_ILC_Val_Ctx self__BaseComp.
  Include BaseComp_ILC_Val (self__BaseComp).
End BaseComp_ILC_Exp_Ctx.

Module Type BaseComp_ILC_Exp 
  (self__BaseComp : BaseComp_ILC_Ctx)  
  (self__ILC : BaseComp_ILC_Exp_Ctx self__BaseComp).
  Include BaseComp_IL_Exp (self__BaseComp) (self__ILC).
  Axiom EUnpack : self__BaseComp.Ident -> self__BaseComp.Ident -> self__ILC.Val -> Exp -> Exp.
End BaseComp_ILC_Exp.

Module Type BaseComp_ILC_Sig_Helper (self__BaseComp : BaseComp_ILC_Ctx).
  Include BaseComp_ILC_Exp_Ctx self__BaseComp.
  Include BaseComp_ILC_Exp (self__BaseComp).
End BaseComp_ILC_Sig_Helper.

Module Type BaseComp_ILC_Sig (self__BaseComp : BaseComp_ILC_Ctx).
  Declare Module ILC : BaseComp_ILC_Sig_Helper (self__BaseComp).
End BaseComp_ILC_Sig.

(* Instantiate BaseComp.ILC *)
Module BaseComp_ILC_Impl (self__BaseComp : BaseComp_ILC_Ctx)
        <: BaseComp_ILC_Sig (self__BaseComp).
   Module ILC.
    Inductive Ty' := 
      | TUnit' | TCont' (ts : list Ty')
      | TVar' (s : self__BaseComp.Ident) | TExist' (x : self__BaseComp.Ident) (t : Ty').
    Definition Ty := Ty'.
    Definition TUnit := TUnit'.
    Definition TCont := TCont'.
    Definition TVar := TVar'.
    Definition TExist := TExist'.
    
    Inductive Val' := 
      | Unit' | Var' (x : self__BaseComp.Ident)
      | Pack' (t : Ty) (v : Val') | Name' (n : self__BaseComp.Ident).
    (* Lam (x : list string) (e : Exp) *)
    Definition Val := Val'.
    Definition Unit := Unit'.
    Definition Var := Var'.
    Definition Pack := Pack'.
    Definition Name := Name'.

    Inductive Exp' := 
      | ELet' (x : self__BaseComp.Ident) (v : Val) (e : Exp')
      | EApp' (v : Val) (vs : list Val) 
      | EHalt' (v : Val)
      | EUnpack' (a : self__BaseComp.Ident) (x : self__BaseComp.Ident) (v : Val) (e : Exp').
    Definition Exp := Exp'.
    Definition ELet := ELet'.
    Definition EApp := EApp'.
    Definition EHalt := EHalt'.    
    Definition EUnpack := EUnpack'.
  End ILC.
End BaseComp_ILC_Impl.

(* Instantiate BaseComp *)
Module BaseComp.
  Include BaseComp_STLC_Impl.

  Include BaseComp_Ident.
  
  Include BaseComp_IL_Impl.
  
  Include BaseComp_ILK_Impl.

  Include BaseComp_ILC_Impl.
End BaseComp.

Check BaseComp.IL.Ty.

Check BaseComp.STLC.Exp.


Check BaseComp.Ident.

Module Type IfExt_STLC_Ctx.  
End IfExt_STLC_Ctx.

Module Type IfExt_STLC_Ty_Ctx
   (self__IfExt: IfExt_STLC_Ctx).
End IfExt_STLC_Ty_Ctx.

Module Type IfExt_STLC_Ty   
   (self__IfExt: IfExt_STLC_Ctx)
   (self__STLC : IfExt_STLC_Ty_Ctx self__IfExt).  
  (* Include BaseComp_STLC_Ty (self__IfExt) (self__STLC).
     This is subsumed by STLCIf
   *)
  Include STLCIf_Ty(self__STLC).  
End IfExt_STLC_Ty.

Module Type IfExt_STLC_ExpVal_Ctx
  (self__BaseComp: IfExt_STLC_Ctx).  
  Include IfExt_STLC_Ctx.
  Include IfExt_STLC_Ty (self__BaseComp).
End IfExt_STLC_ExpVal_Ctx.

Module Type IfExt_STLC_ExpVal 
    (self__IfExt : IfExt_STLC_Ctx)
    (self__STLC : IfExt_STLC_ExpVal_Ctx self__IfExt).
  Include STLCIf_ExpVal(self__STLC).
End IfExt_STLC_ExpVal.

Module Type IfExt_STLC_Sig_Helper (self__IfExt : IfExt_STLC_Ctx).  
  Include IfExt_STLC_ExpVal_Ctx.
  Include IfExt_STLC_ExpVal
    (self__IfExt).  
End IfExt_STLC_Sig_Helper.

Module Type IfExt_STLC_Sig (self__IfExt : IfExt_STLC_Ctx).
  Declare Module STLC : IfExt_STLC_Sig_Helper(self__IfExt).
End IfExt_STLC_Sig.

(* Instantiate BaseComp.STLC *)
Module IfExt_STLC_Impl (self__IfExt : IfExt_STLC_Ctx) 
        <: IfExt_STLC_Sig(self__IfExt).
  Module STLC.
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
   
   Definition VTrue := VTrue'.
   Definition VFalse := VFalse'.
   Definition EIf := EIf'.
   Definition Val := Val'.
   Definition Unit := Unit'.
   Definition Var := Var'.
   Definition Lam := Lam'.
   Definition Exp := Exp'.
   Definition EVal := EVal'.
   Definition EApp := EApp'.
  End STLC.
End IfExt_STLC_Impl.

Module Type IfExt_Ident_Ctx.
  Include IfExt_STLC_Ctx.
  Include IfExt_STLC_Sig.
End IfExt_Ident_Ctx.

Module Type IfExt_Ident_Sig
  (self__IfExt : IfExt_Ident_Ctx).
  Include BaseComp_Ident_Sig (self__IfExt).
End IfExt_Ident_Sig.

Module IfExt_Ident 
  (self__IfExt : IfExt_Ident_Ctx) 
  <: IfExt_Ident_Sig (self__IfExt).
  Include BaseComp_Ident (self__IfExt).
End IfExt_Ident.

Module Type IfExt_IL_Ctx.
  Include IfExt_Ident_Ctx.
  Include IfExt_Ident_Sig.
End IfExt_IL_Ctx.

Module Type IfExt_IL_Ty_Ctx
  (self__IfExt : IfExt_IL_Ctx).
End IfExt_IL_Ty_Ctx.

Module Type IfExt_IL_Ty 
  (self__IfExt : IfExt_IL_Ctx)
  (self__IL : IfExt_IL_Ty_Ctx self__IfExt).  
  Include BaseComp_IL_Ty (self__IfExt) (self__IL).
  Axiom TBool : Ty.
End IfExt_IL_Ty.

Module Type IfExt_IL_Val_Ctx
  (self__IfExt : IfExt_IL_Ctx).
  Include IfExt_IL_Ty_Ctx (self__IfExt).
  Include IfExt_IL_Ty (self__IfExt).
End IfExt_IL_Val_Ctx.

Module Type IfExt_IL_Val
  (self__IfExt : IfExt_IL_Ctx)
  (self__IL : IfExt_IL_Val_Ctx self__IfExt).
  Include BaseComp_IL_Val (self__IfExt) (self__IL).
  Axiom Bool : bool -> Val.
End IfExt_IL_Val.

Module Type IfExt_IL_Exp_Ctx 
   (self__IfExt : IfExt_IL_Ctx).
  Include IfExt_IL_Val_Ctx (self__IfExt).
  Include IfExt_IL_Val (self__IfExt).
End IfExt_IL_Exp_Ctx.

Module Type IfExt_IL_Exp 
  (self__IfExt : IfExt_IL_Ctx)
  (self__IL : IfExt_IL_Exp_Ctx self__IfExt).
  Include BaseComp_IL_Exp (self__IfExt) (self__IL).
  Axiom EIf : self__IL.Val -> Exp -> Exp -> Exp.
End IfExt_IL_Exp.

Module Type IfExt_IL_Sig_Helper (self__IfExt : IfExt_IL_Ctx).
  Include IfExt_IL_Exp_Ctx (self__IfExt).
  Include IfExt_IL_Exp (self__IfExt).
End IfExt_IL_Sig_Helper.

Module Type IfExt_IL_Sig (self__IfExt : IfExt_IL_Ctx).
  Declare Module IL : IfExt_IL_Sig_Helper (self__IfExt).
End IfExt_IL_Sig.

(* Instantiate IfExt.IL *)
Module IfExt_IL_Impl (self__IfExt : IfExt_IL_Ctx)
     <: IfExt_IL_Sig (self__IfExt).
    Module IL.
    Inductive Ty' := TUnit' | TCont' (ts : list Ty') | TBool'.
    Definition Ty := Ty'.
    Definition TUnit := TUnit'.
    Definition TCont := TCont'.
    Definition TBool := TBool'.

    Inductive Val' := Unit' | Var' (x : self__IfExt.Ident) | Bool' (b : bool).
    Definition Bool := Bool'.
    Definition Val := Val'.
    Definition Unit := Unit'.
    Definition Var := Var'.

    Inductive Exp' := 
      | ELet' (x : self__IfExt.Ident) (v : Val) (e : Exp')
      | EApp' (v : Val) (vs : list Val) 
      | EHalt' (v : Val)
      | EIf' (v : Val) (e1 e2 : Exp').
    Definition EIf := EIf'.
    Definition Exp := Exp'.
    Definition ELet := ELet'.
    Definition EApp := EApp'.
    Definition EHalt := EHalt'.    
  End IL.
End IfExt_IL_Impl.

Module Type IfExt_ILK_Ctx.
  Include IfExt_IL_Ctx.
  Include IfExt_IL_Sig.
End IfExt_ILK_Ctx.

Module Type IfExt_ILK_Ty_Ctx
  (self__IfExt : IfExt_ILK_Ctx).
End IfExt_ILK_Ty_Ctx.

Module Type IfExt_ILK_Ty 
  (self__IfExt : IfExt_ILK_Ctx)
  (self__ILK : IfExt_ILK_Ty_Ctx self__IfExt).
  Include BaseComp_ILK_Ty (self__IfExt) (self__ILK).
  Include IfExt_IL_Ty (self__IfExt) (self__ILK).
  (* how to compile mixins? *)
  (* can we compile mixins without code duplication? *)
  Axiom TBool : Ty.
End IfExt_ILK_Ty.

Module Type IfExt_ILK_Val_Ctx
  (self__IfExt : IfExt_ILK_Ctx).
  Include IfExt_ILK_Ty_Ctx (self__IfExt).
  Include IfExt_ILK_Ty (self__IfExt).
End IfExt_ILK_Val_Ctx.

Module Type IfExt_ILK_Val 
  (self__IfExt : IfExt_ILK_Ctx)
  (self__ILK : IfExt_ILK_Val_Ctx self__IfExt).
  Include IfExt_IL_Val (self__IfExt) (self__ILK).
  (* Include BaseComp_ILK_Val (self__IfExt) (self__ILK). *)
  (* Axiom Lam : list ident -> self.Exp -> Val. *)
End IfExt_ILK_Val.

Module Type IfExt_ILK_Exp_Ctx
  (self__IfExt : IfExt_ILK_Ctx).
  Include IfExt_ILK_Val_Ctx self__IfExt.
  Include IfExt_ILK_Val (self__IfExt). 
End IfExt_ILK_Exp_Ctx.

Module Type IfExt_ILK_Exp 
  (self__IfExt : IfExt_ILK_Ctx)  
  (self__ILK : IfExt_ILK_Exp_Ctx self__IfExt).
  Include IfExt_IL_Exp (self__IfExt) (self__ILK).
  (* Include BaseComp_ILK_Exp (self__IfExt) (self__ILK). *)
End IfExt_ILK_Exp.

Module Type IfExt_ILK_Sig_Helper (self__IfExt : IfExt_ILK_Ctx).
  Include IfExt_ILK_Exp_Ctx self__IfExt.
  Include IfExt_ILK_Exp (self__IfExt).
End IfExt_ILK_Sig_Helper.

Module Type IfExt_ILK_Sig (self__IfExt : IfExt_ILK_Ctx).
  Declare Module ILK : IfExt_ILK_Sig_Helper (self__IfExt).
End IfExt_ILK_Sig.

(* Instantiate IfExt.ILK *)
Module IfExt_ILK_Impl (self__IfExt : IfExt_ILK_Ctx)
        <: IfExt_ILK_Sig (self__IfExt).
  Module ILK.    
   Inductive Ty' := TUnit' | TCont' (ts : list Ty') | TBool'.
    Definition Ty := Ty'.
    Definition TUnit := TUnit'.
    Definition TCont := TCont'.
    Definition TBool := TBool'.

    Inductive Val' := Unit' | Var' (x : self__IfExt.Ident) | Bool' (b : bool).
    (* Lam (x : list string) (e : Exp) *)
    Definition Bool := Bool'.
    Definition Val := Val'.
    Definition Unit := Unit'.
    Definition Var := Var'.

    Inductive Exp' := 
      | ELet' (x : self__IfExt.Ident) (v : Val) (e : Exp')
      | EApp' (v : Val) (vs : list Val) 
      | EHalt' (v : Val)
      | EIf' (v : Val) (e1 e2 : Exp').
    Definition Exp := Exp'.
    Definition ELet := ELet'.
    Definition EApp := EApp'.
    Definition EHalt := EHalt'.
    Definition EIf := EIf'.
  End ILK.
  (* Definition f := self.IL.Unit. 
  Check f.*)
End IfExt_ILK_Impl.

Module Type IfExt_ILC_Ctx.
  Include IfExt_ILK_Ctx.
  Include IfExt_ILK_Sig.
End IfExt_ILC_Ctx.

Module Type IfExt_ILC_Ty_Ctx 
   (self__IfExt : IfExt_ILC_Ctx).
End IfExt_ILC_Ty_Ctx.

Module Type IfExt_ILC_Ty 
  (self__IfExt : IfExt_ILC_Ctx)
  (self__ILC : IfExt_ILC_Ty_Ctx self__IfExt).
  Include IfExt_IL_Ty (self__IfExt) (self__ILC).
  (* Include BaseComp_ILC_Ty (self__IfExt) (self__ILC). *)
  Axiom TVar : self__IfExt.Ident -> Ty.
  Axiom TExist : self__IfExt.Ident -> Ty -> Ty.
End IfExt_ILC_Ty.

Module Type IfExt_ILC_Val_Ctx
   (self__IfExt : IfExt_ILC_Ctx).
  Include IfExt_ILC_Ty_Ctx (self__IfExt).
  Include IfExt_ILC_Ty (self__IfExt).
End IfExt_ILC_Val_Ctx.

Module Type IfExt_ILC_Val 
  (self__IfExt : IfExt_ILC_Ctx)
  (self__ILC : IfExt_ILC_Val_Ctx self__IfExt).
  Include IfExt_IL_Val (self__IfExt) (self__ILC).
  (* Include BaseComp_ILC_Val (self__IfExt) (self__ILC). *)
  Axiom Pack : self__ILC.Ty -> Val -> Val.
  Axiom Name : self__IfExt.Ident -> Val.
End IfExt_ILC_Val.

Module Type IfExt_ILC_Exp_Ctx
   (self__IfExt : IfExt_ILC_Ctx).
  Include IfExt_ILC_Val_Ctx self__IfExt.
  Include IfExt_ILC_Val (self__IfExt).
End IfExt_ILC_Exp_Ctx.

Module Type IfExt_ILC_Exp 
  (self__IfExt : IfExt_ILC_Ctx)  
  (self__ILC : IfExt_ILC_Exp_Ctx self__IfExt).
  Include IfExt_IL_Exp (self__IfExt) (self__ILC).
  (* Include BaseComp_ILC_Exp (self__IfExt) (self__ILC). *)
  Axiom EUnpack : self__IfExt.Ident -> self__IfExt.Ident -> self__ILC.Val -> Exp -> Exp.
End IfExt_ILC_Exp.

Module Type IfExt_ILC_Sig_Helper (self__IfExt : IfExt_ILC_Ctx).
  Include IfExt_ILC_Exp_Ctx self__IfExt.
  Include IfExt_ILC_Exp (self__IfExt).
End IfExt_ILC_Sig_Helper.

Module Type IfExt_ILC_Sig (self__IfExt : IfExt_ILC_Ctx).
  Declare Module ILC : IfExt_ILC_Sig_Helper (self__IfExt).
End IfExt_ILC_Sig.

Module IfExt_ILC_Impl (self__IfExt : IfExt_ILC_Ctx)
        <: IfExt_ILC_Sig (self__IfExt).
  Module ILC.    
    Inductive Ty' := TUnit' | TCont' (ts : list Ty') | TBool'
     | TVar' (s : self__IfExt.Ident) | TExist' (x : self__IfExt.Ident) (t : Ty').
    Definition Ty := Ty'.
    Definition TUnit := TUnit'.
    Definition TCont := TCont'.
    Definition TBool := TBool'.
    Definition TVar := TVar'.
    Definition TExist := TExist'.

    Inductive Val' := Unit' | Var' (x : self__IfExt.Ident)
                 | Bool' (b : bool)
                 | Pack' (t : Ty) (v : Val') | Name' (n : self__IfExt.Ident).
    (* Lam (x : list string) (e : Exp) *)
    Definition Bool := Bool'.
    Definition Val := Val'.
    Definition Unit := Unit'.
    Definition Var := Var'.
    Definition Pack := Pack'.
    Definition Name := Name'.

    Inductive Exp' := 
      | ELet' (x : self__IfExt.Ident) (v : Val) (e : Exp')
      | EApp' (v : Val) (vs : list Val) 
      | EHalt' (v : Val)
      | EIf' (v : Val) (e1 e2 : Exp')
      | EUnpack' (a : self__IfExt.Ident) (x : self__IfExt.Ident) (v : Val) (e : Exp').
    Definition Exp := Exp'.
    Definition EUnpack := EUnpack'.
    Definition ELet := ELet'.
    Definition EApp := EApp'.
    Definition EHalt := EHalt'.
    Definition EIf := EIf'.
  End ILC.
  (* Definition f := self.IL.Unit. 
  Check f.*)
End IfExt_ILC_Impl.

Module IfExt.
  Include IfExt_STLC_Impl.

  Include IfExt_Ident.
  
  Include IfExt_IL_Impl.
  
  Include IfExt_ILK_Impl.

  Include IfExt_ILC_Impl.
End IfExt.

Check IfExt.Ident.


