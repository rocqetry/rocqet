(* Based on the case study from https://dl.acm.org/doi/10.1145/3649836 *)

Module Type S.
   Axiom Ty : Set.
End S.

Module S_Impl <: S.
  Inductive Ty' := TyNat.
  Definition Ty := Ty'.
End S_Impl.
  

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
   Inductive Ty : Set := 
     | TyUnit : Ty 
     | TNat : Ty 
     | TArr : Ty -> Ty -> Ty.
   
   Inductive Val : Set := 
     | Unit : Val
     | Var : ident -> Val
     | Lam : ident -> Exp -> Val 
    with Exp : Set := 
      | EVal : Val -> Exp 
      | EApp : Exp -> Exp -> Exp.
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
   Inductive Ty : Set := 
     | TyUnit : Ty 
     | TNat : Ty 
     | TArr : Ty -> Ty -> Ty.
   
   Inductive Val : Set := 
     | Unit : Val
     | Var : ident -> Val
     | Lam : ident -> Exp -> Val 
     | VTrue : Val 
     | VFalse : Val 
    with Exp : Set := 
      | EVal : Val -> Exp 
      | EApp : Exp -> Exp -> Exp
      | EIf : Exp -> Exp -> Exp -> Exp.
End STLCIf.


Module Type BaseComp_STLC_Ctx.
End BaseComp_STLC_Ctx.

Module Type BaseComp_STLC_Ty_Ctx. 
  Include BaseComp_STLC_Ctx.
End BaseComp_STLC_Ty_Ctx.

Module Type BaseComp_STLC_Ty (self : BaseComp_STLC_Ty_Ctx).
  Include STLCBase_Ty(self).
End BaseComp_STLC_Ty.

Module Type BaseComp_STLC_ExpVal_Ctx. 
  Include BaseComp_STLC_Ty_Ctx.
  Include BaseComp_STLC_Ty.
End BaseComp_STLC_ExpVal_Ctx.

Module Type BaseComp_STLC_ExpVal (self : BaseComp_STLC_ExpVal_Ctx). 
  Include STLCBase_ExpVal(self).
End BaseComp_STLC_ExpVal.

Module Type BaseComp_STLC_sig (self : BaseComp_STLC_Ctx).
  Include BaseComp_STLC_ExpVal_Ctx.
  Include BaseComp_STLC_ExpVal.
End BaseComp_STLC_sig.

Module Type BaseComp_STLC (self : BaseComp_STLC_Ctx). 
  Declare Module STLC : BaseComp_STLC_sig(self).
End BaseComp_STLC.

(* Instantiate BaseComp.STLC *)
Module BaseComp_STLC_Impl (self : BaseComp_STLC_Ctx) <: BaseComp_STLC(self).
  Module STLC.
    Inductive Ty : Set := 
     | TyUnit : Ty 
     | TNat : Ty 
     | TArr : Ty -> Ty -> Ty.
   
   Inductive Val : Set := 
     | Unit : Val
     | Var : ident -> Val
     | Lam : ident -> Exp -> Val 
    with Exp : Set := 
      | EVal : Val -> Exp 
      | EApp : Exp -> Exp -> Exp.
  End STLC.
End BaseComp_STLC_Impl.

(* IL *)
Module Type BaseComp_IL_Ctx.
  Include BaseComp_STLC_Ctx.
  Include BaseComp_STLC.
End BaseComp_IL_Ctx.

Module Type BaseComp_IL_Ty_Ctx.
  Include BaseComp_IL_Ctx.
End BaseComp_IL_Ty_Ctx.

Module Type BaseComp_IL_Ty (self : BaseComp_IL_Ty_Ctx).
  Axiom Ty : Set.
  Axiom TUnit : Ty.
  Axiom TCont : list Ty -> Ty.
End BaseComp_IL_Ty.

Module Type BaseComp_IL_Val_Ctx.
  Include BaseComp_IL_Ty_Ctx.
  Include BaseComp_IL_Ty.
End BaseComp_IL_Val_Ctx.

Module Type BaseComp_IL_Val (self : BaseComp_IL_Val_Ctx).
  Axiom Val : Set.
  Axiom Unit : Val.
  Axiom Var : ident -> Val.
End BaseComp_IL_Val.

Module Type BaseComp_IL_Exp_Ctx.
  Include BaseComp_IL_Val_Ctx.
  Include BaseComp_IL_Val.
End BaseComp_IL_Exp_Ctx.

Module Type BaseComp_IL_Exp (self : BaseComp_IL_Exp_Ctx).
  Axiom Exp : Set.
  Axiom ELet : ident -> self.Val -> Exp -> Exp.
  Axiom EApp : self.Val -> list self.Val -> Exp.
  Axiom EHalt : self.Val -> Exp.
End BaseComp_IL_Exp.

Module Type BaseComp_IL_sig (self : BaseComp_IL_Ctx).
  Include BaseComp_IL_Exp_Ctx.
  Include BaseComp_IL_Exp.
End BaseComp_IL_sig.

Module Type BaseComp_IL (self : BaseComp_IL_Ctx).
  Declare  Module IL : BaseComp_IL_sig(self).  
End BaseComp_IL.

(* Instantiate BaseComp.IL *)
Module BaseComp_IL_Impl (self : BaseComp_IL_Ctx).
  Module IL.
    Inductive Ty := TUnit | TCont (ts : list Ty).
    Inductive Val := Unit | Var (x : ident).
    Inductive Exp := 
      | ELet (x : ident) (v : Val) (e : Exp)
      | EApp (v : Val) (vs : list Val) 
      | EHalt (v : Val).
  End IL.
  (* Module s := self.STLC. *)
End BaseComp_IL_Impl.


(* ILK *)

Module Type BaseComp_ILK_Ctx. 
  Include BaseComp_IL_Ctx.
  Include BaseComp_IL.
End BaseComp_ILK_Ctx.

Module Type BaseComp_ILK_Ty_Ctx. 
  Include BaseComp_ILK_Ctx.
End BaseComp_ILK_Ty_Ctx.

Module Type BaseComp_ILK_Ty (self : BaseComp_ILK_Ty_Ctx).
  Include BaseComp_IL_Ty(self).
End BaseComp_ILK_Ty.

Module Type BaseComp_ILK_Val_Ctx.
  Include BaseComp_ILK_Ty_Ctx.
  Include BaseComp_ILK_Ty.
End BaseComp_ILK_Val_Ctx.

Module Type BaseComp_ILK_Val (self : BaseComp_IL_Val_Ctx).
  Include BaseComp_IL_Val(self).
  (* Axiom Lam : list ident -> self.Exp -> Val. *)
End BaseComp_ILK_Val.

Module Type BaseComp_ILK_Exp_Ctx.
  Include BaseComp_ILK_Val_Ctx.
  Include BaseComp_ILK_Val.
End BaseComp_ILK_Exp_Ctx.

Module Type BaseComp_ILK_Exp (self : BaseComp_IL_Exp_Ctx).
  Include BaseComp_IL_Exp(self).
End BaseComp_ILK_Exp.

Module Type BaseComp_ILK_sig (self : BaseComp_ILK_Ctx).
  Include BaseComp_IL_Exp_Ctx.
  Include BaseComp_IL_Exp.
End BaseComp_ILK_sig.

Module Type BaseComp_ILK (self : BaseComp_ILK_Ctx).
  Declare Module ILK : BaseComp_ILK_sig(self).  
End BaseComp_ILK.

(* Instantiate BaseComp.ILK *)
Module BaseComp_ILK_Impl (self : BaseComp_ILK_Ctx).
  Module ILK.
    Inductive Ty := TUnit | TCont (ts : list Ty).
    Inductive Val := 
      | Unit 
      | Var (x : ident).
      (* Lam (x : list string) (e : Exp) *)
    Inductive Exp := 
      | ELet (x : ident) (v : Val) (e : Exp)
      | EApp (v : Val) (vs : list Val) 
      | EHalt (v : Val).
  End ILK.
  Definition f := self.IL.Unit.
  Check f.
End BaseComp_ILK_Impl.

(* ILC *)

Module Type BaseComp_ILC_Ctx.
  Include BaseComp_ILK_Ctx.
  Include BaseComp_ILK.
End BaseComp_ILC_Ctx.

Module Type BaseComp_ILC_Ty_Ctx.
  Include BaseComp_ILC_Ctx.
End BaseComp_ILC_Ty_Ctx.

Module Type BaseComp_ILC_Ty (self : BaseComp_ILC_Ty_Ctx).
  Include BaseComp_IL_Ty(self).
  Axiom TVar : ident -> Ty.
  Axiom TExist : ident -> Ty -> Ty.
End BaseComp_ILC_Ty.

Module Type BaseComp_ILC_Val_Ctx.
  Include BaseComp_ILC_Ty_Ctx.
  Include BaseComp_ILC_Ty.
End BaseComp_ILC_Val_Ctx.

Module Type BaseComp_ILC_Val (self : BaseComp_ILC_Val_Ctx).
  Include BaseComp_IL_Val(self).
  Axiom Pack : self.Ty -> Val -> Val.
  Axiom Name : ident -> Val.
End BaseComp_ILC_Val.

Module Type BaseComp_ILC_Exp_Ctx.
  Include BaseComp_ILC_Val_Ctx.
  Include BaseComp_ILC_Val.
End BaseComp_ILC_Exp_Ctx.

Module Type BaseComp_ILC_Exp (self : BaseComp_ILC_Exp_Ctx).
  Include BaseComp_IL_Exp(self).
  Axiom EUnpack : ident -> ident -> self.Val -> Exp -> Exp.
End BaseComp_ILC_Exp.

Module Type BaseComp_ILC_sig (self : BaseComp_ILC_Ctx).
  Include BaseComp_ILC_Exp_Ctx.
  Include BaseComp_ILC_Exp.
End BaseComp_ILC_sig.

Module Type BaseComp_ILC (self : BaseComp_ILC_Ctx).
  Declare Module ILC : BaseComp_ILC_sig(self).
End BaseComp_ILC.

(* Instantiate BaseComp.ILC *)
Module BaseComp_ILC_Impl (self : BaseComp_ILC_Ctx).
  Module ILC.
    Inductive Ty := 
      | TUnit 
      | TCont (ts : list Ty)
      | TVar (s : ident) | TExist (x : ident) (t : Ty).
    Inductive Val := 
      | Unit 
      | Var (x : ident)
      (* Lam (x : list string) (e : Exp) *)
      | Pack (t : Ty) (v : Val) | Name (n : ident).
    Inductive Exp := 
      | ELet (x : ident) (v : Val) (e : Exp)
      | EApp (v : Val) (vs : list Val) 
      | EHalt (v : Val)
      | EUnpack(a : ident) (x : ident) (v : Val) (e : Exp).
  End ILC.
  
End BaseComp_ILC_Impl.

Module BaseComp.
  Include BaseComp_STLC_Impl.
  
  Include BaseComp_IL_Impl.

(* On completion of the family *)
module BaseComp {
    module STLC {
        Inductive Ty := TyUnit | TNat | TArr (t1 t2 : Ty)        
        Inductive Exp := EVal (v : Val) | EApp(e1 e2 : Exp)
        with Val := Unit | Var (x : string) | Lam (x : string) (e : Exp)
    }

    module IL { 
        Inductive Ty := TUnit | TCont (ts : list Ty)
        Inductive Val := Unit | Var (x : string)
        Inductive Exp := 
          | ELet (x : string) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
    }
    
    module ILK { 
        Inductive Ty := TUnit | TCont (ts : list Ty)
        Inductive Val := Unit | Var (x : string) | Lam (x : list string) (e : Exp)
        Inductive Exp := 
          | ELet (x : string) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
    }

    module ILC { 
        Inductive Ty := TUnit | TCont (ts : list Ty) | TVar (s : string) | TExist (x : string) (t : Ty)
        Inductive Val := Unit | Var (x : string) | Pack (t : Ty) (v : Val) | Name (n : string)
        Inductive Exp := 
          | ELet (x : string) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
          | EUnpack(a : string) (x : string) (v : Val) (e : Exp)
    }
}

module type IfExt_STLC_Ctx { }

module type IfExt_STLC_Ty_Ctx { }
module type IfExt_STLC_Ty (self: IfExt_STLC_Ty_Ctx) {
  include BaseComp_STLC_Ty(self) 
  include STLCIf_Ty(self)
}

module type IfExt_STLC_Exp/Val_Ctx { 
  include IfExt_STLC_Ty_Ctx
  include IfExt_STLC_Ty
}
module type IfExt_STLC_Exp/Val (self : If_STLC_Exp/Val_Ctx) { 
  include BaseComp_STLC_Exp/Val(self)
  include STLCIf_Exp/Val(self)
}

module type IfExt_STLC (self : IfExt_STLC_Ctx) {
  module STLC : sig
    include IfExt_STLC_Exp/Val_Ctx                  
    include IfExt_STLC_Exp/Val
  end
}

module type IfExt_IL_Ctx { 
  include IFExt_STLC_Ctx 
  include IfExt_STLC
}

module type IfExt_IL_Ty_Ctx { 
  include IfExt_IL_Ctx
}

module type IfExt_IL_Ty (self: IfExt_IL_Ty_Ctx) { 
  include BaseComp_IL_Ty(self) 
  Axiom TBool : Ty
}

module type IfExt_IL_Val_Ctx { 
  include IfExt_IL_Ty_Ctx
  include IfExt_IL_Ty
}

module type IfExt_IL_Val (self : IfExt_IL_Val_Ctx) {
  include BaseComp_IL_Val(self)
  Axiom Bool : bool -> Val
}

module type IfExt_IL_Exp_Ctx { 
  include IfExt_IL_Val_Ctx
  include IfExt_IL_Val
}

module type IfExt_IL_Exp (self : IfExt_IL_Exp_Ctx) {
  include BaseComp_IL_Exp(self)
  Axiom EIf : Val -> Exp -> Exp -> Exp
}

module type IfExt_IL (self : IfExt_IL_Ctx) { 
  module IL : sig 
    include IfExt_IL_Exp_Ctx
    include IfExt_IL_Exp                
  end                 
}

module type IfExt_ILK_Ctx {
  include IfExt_IL_Ctx 
  include IfExt_IL 
}

module type IfExt_ILK_Ty_Ctx {
  include IfExt_ILK_Ctx
}

module type IfExt_ILK_Ty (self : IfExt_ILK_Ty_Ctx) {  
  include BaseComp_ILK_Ty(self)
  include IfExt_IL_Ty(self)          
}

module type IfExt_ILK_Val_Ctx {
  include IfExt_ILK_Ty_Ctx 
  include IfExt_ILK_Ty
}

module type BaseComp_ILK_Val (self : IfExt_ILK_Val_Ctx) {
  include BaseComp_ILK_Val(self)
  include IfExt_IL_Val(self)
}

module type IfExt_ILK_Exp_Ctx {
  include IfExt_ILK_Val_Ctx 
  include IfExt_ILK_Val
}

module type IfExt_ILK_Exp (self : IfExt_ILK_Exp_Ctx) {
  include BaseComp_ILK_Exp(self)
  include IfExt_IL_Exp(self)
}

module type IfExt_ILK (self : IfExt_ILK_Ctx) { 
  module ILC : sig 
    include IfExt_ILK_Exp_Ctx
    include IfExt_ILK_Exp                
  end                 
}


(* ILC *)
module type IfExt_ILC_Ctx {
  include IfExt_ILK_Ctx 
  include IfExt_ILK 
}

module type IfExt_ILC_Ty_Ctx {
  include IfExt_ILC_Ctx
}

module type IfExt_ILC_Ty (self : IfExt_ILC_Ty_Ctx) {  
  include BaseComp_ILC_Ty(self)
  include IfExt_IL_Ty(self)          
}

module type IfExt_ILC_Val_Ctx {
  include IfExt_ILC_Ty_Ctx 
  include IfExt_ILC_Ty
}

module type BaseComp_ILC_Val (self : IfExt_ILC_Val_Ctx) {
  include BaseComp_ILC_Val(self)
  include IfExt_IL_Val(self)
}

module type IfExt_ILC_Exp_Ctx {
  include IfExt_ILC_Val_Ctx 
  include IfExt_ILC_Val
}

module type IfExt_ILC_Exp (self : IfExt_ILC_Exp_Ctx) {
  include BaseComp_ILC_Exp(self)
  include IfExt_IL_Exp(self)
}

module type IfExt_ILC (self : IfExt_ILC_Ctx) { 
  module ILC : sig 
    include IfExt_ILC_Exp_Ctx
    include IfExt_ILC_Exp                
  end                 
}

(* On completion of the IfExt family *)
module IfExt { 
   module STLC { 
      Inductive Ty := TyUnit | TNat | TArr (t1 t2 : Ty) | TBool 
      Inductive Exp := EVal (v : Val) | EApp(e1 e2 : Exp) | EIf (e e1 e2 : Exp)
      with Val := 
        | Unit
        | Var (x : string)
        | Lam (x : string) (e : Exp)
        | VTrue
        | VFalse
   }

   module IL { 
     Inductive Ty := TUnit | TCont (ts : list Ty) | TBool
     Inductive Val := Unit | Var (x : string) | Bool (b : bool)
     Inductive Exp := 
       | ELet (x : string) (v : Val) (e : Exp)
       | EApp (v : Val) (vs : list Val) 
       | EHalt (v : Val)
       | EIf (v : Val) (e1 e2 : Exp)
    }

    module ILK { 
        Inductive Ty := TUnit | TCont (ts : list Ty)
        Inductive Val := Unit | Var (x : string) | Lam (x : list string) (e : Exp)
        Inductive Exp := 
          | ELet (x : string) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
    }

    module ILC { 
        Inductive Ty := TUnit | TCont (ts : list Ty) | TVar (s : string) | TExist (x : string) (t : Ty)
        Inductive Val := Unit | Var (x : string) | Pack (t : Ty) (v : Val) | Name (n : string)
        Inductive Exp := 
          | ELet (x : string) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
          | EUnpack(a : string) (x : string) (v : Val) (e : Exp)
   }  
}
