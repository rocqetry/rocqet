module type STLCBase_Ty_Ctx { }

module type STLCBase_Ty (self: STLC_Ty_Ctx) {
  Axiom Ty : Set 
  Axiom TyUnit : Ty 
  Axiom TNat : Ty 
  Axiom TArr : Ty -> Ty -> Ty                    
}

module type STLCBase_Exp/Val_Ctx { 
  include STLCBase_Ty_Ctx
  include STLCBase_Ty          
}

module type STLCBase_Exp/Val (self: STLCBase_Exp/Val_Ctx) {
  Axiom Exp : Set 
  Axiom Val : Set 
  Axiom EVal : Val -> Exp 
  Axiom EApp : Exp -> Exp -> Exp 
  Axiom Unit : Val
  <Axiom Var : string -> Val 
  Axiom Lam : string -> Exp -> Val                 
}

module type STLCIf_Ty_Ctx { }

module type STLCIf_Ty (self : STLCIf_Ty_Ctx) {
  include include STLCBase_Ty(self)
  Axiom TBool : Ty
}

module type STLCIf_Exp/Val_Ctx {
  include STLCIf_Ty_Ctx 
  include STLCIf_Ty
} 

module type STLCIf_Exp/Val (self : STLCIf_Exp/Val_Ctx) {
  include STLCBase_Exp/Val(self) 
  Axiom EIf : Exp -> Exp -> Exp -> Val
}

module type BaseComp_STLC_Ctx { }

module type BaseComp_STLC_Ty_Ctx {
  include BaseComp_STLC_Ctx
 }
module type BaseComp_STLC_Ty (self : BaseComp_STLC_Ty_Ctx) {
  include STLCBase_Ty(self)
}

module type BaseComp_STLC_Exp/Val_Ctx { 
  include BaseComp_STLC_Ty_Ctx
  include BaseComp_STLC_Ty
}

module type BaseComp_STLC_Exp/Val (self : BaseComp_STLC_Exp/Val_Ctx) { 
  include STLCBase_Exp/Val(self)
}

module type BaseComp_STLC (self : BaseComp_STLC_Ctx) {
  module STLC : sig      
     include BaseComp_STLC_Exp/Val_Ctx
     include BaseComp_STLC_Exp/Val
  end
}


(* IL *)
module type BaseComp_IL_Ctx {
  include BaseComp_STLC_Ctx 
  include BaseComp_STLC
}

module type BaseComp_IL_Ty_Ctx {
  include BaseComp_IL_Ctx
}

module type BaseComp_IL_Ty (self : BaseComp_IL_Ty_Ctx) {
  Axiom Ty : Set
  Axiom TUnit : Ty 
  Axiom TCont : list Ty -> Ty
}

module type BaseComp_IL_Val_Ctx {
  include BaseComp_IL_Ty_Ctx 
  include BaseComp_IL_Ty
}

module type BaseComp_IL_Val (self : BaseComp_IL_Val_Ctx) {
  Axiom Val : Set 
  Axiom Unit : Val 
  Axiom Var : string -> Val
}

module type BaseComp_IL_Exp_Ctx { 
  include BaseComp_IL_Val_Ctx
  include BaseComp_IL_Val
}

module type BaseComp_IL_Exp (self : BaseComp_IL_Exp_Ctx) {
  Axiom Exp : Set 
  Axiom ELet : string -> Val -> Exp -> Exp 
  Axiom EApp : Val -> list Val -> Exp 
  Axiom EHalt : Val -> Exp 
}

module type BaseComp_IL (self : BaseComp_IL_Ctx) {
  module IL : sig
    include BaseComp_IL_Exp_Ctx
    include BaseComp_IL_Exp
  end 
}

(* ILK *)

module type BaseComp_ILK_Ctx {
  include BaseComp_IL_Ctx 
  include BaseComp_IL 
}

module type BaseComp_ILK_Ty_Ctx {
  include BaseComp_ILK_Ctx
}

module type BaseComp_ILK_Ty (self : BaseComp_ILK_Ty_Ctx) {
  include BaseComp_IL_Ty(self)
}

module type BaseComp_ILK_Val_Ctx {
  include BaseComp_ILK_Ty_Ctx 
  include BaseComp_ILK_Ty
}

module type BaseComp_ILK_Val (self : BaseComp_IL_Val_Ctx) {
  include BaseComp_IL_Val(self)
  Axiom Lam : list string -> Exp -> Val
}

module type BaseComp_ILK_Exp_Ctx { 
  include BaseComp_ILK_Val_Ctx
  include BaseComp_ILK_Val
}

module type BaseComp_ILK_Exp (self : BaseComp_IL_Exp_Ctx) {
  include BaseComp_IL_Exp(self)
}

module type BaseComp_ILK (self : BaseComp_ILK_Ctx) {
  module ILK : sig
    include BaseComp_IL_Exp_Ctx
    include BaseComp_IL_Exp
  end
}


(* ILC *)

module type BaseComp_ILC_Ctx {
  include BaseComp_ILK_Ctx 
  include BaseComp_ILK 
}

module type BaseComp_ILC_Ty_Ctx {
  include BaseComp_ILC_Ctx
}

module type BaseComp_ILC_Ty (self : BaseComp_ILC_Ty_Ctx) {
  include BaseComp_IL_Ty(self)
  Axiom TVar : string -> Ty 
  Axiom TExist : string -> Ty -> Ty             
}

module type BaseComp_ILC_Val_Ctx {
  include BaseComp_ILC_Ty_Ctx 
  include BaseComp_ILC_Ty
}

module type BaseComp_ILC_Val (self : BaseComp_ILC_Val_Ctx) {
  include BaseComp_IL_Val(self)
  Axiom Pack : Ty -> Val -> Val 
  Axiom Name : string -> Val
}

module type BaseComp_ILC_Exp_Ctx { 
  include BaseComp_ILC_Val_Ctx
  include BaseComp_ILC_Val
}

module type BaseComp_ILC_Exp (self : BaseComp_ILC_Exp_Ctx) {
  include BaseComp_IL_Exp(self)
  Axiom EUnpack : string -> string -> Val -> Exp -> Exp 
}

module type BaseComp_ILC (self : BaseComp_ILC_Ctx) {
  module ILC : sig
    include BaseComp_ILC_Exp_Ctx
    include BaseComp_ILC_Exp
  end
}

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

(* On completion of the family *)
module IfExt { 
  module STLC { } 

  module IL { }

  module ILK { }

  module ILC { }
}
