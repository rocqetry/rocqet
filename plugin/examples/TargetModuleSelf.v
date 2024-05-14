(* Compiling with paramenterized self hierachy *)
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
  Axiom Var : string -> Val 
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

module type BaseComp_STLC_Ty_Ctx (self[BaseComp]: BaseComp_STLC_Ctx) { }

module type BaseComp_STLC_Ty   
   (self[BaseComp]: BaseComp_STLC_Ctx)
   (self[STLC] : BaseComp_STLC_Ty_Ctx(self[BaseComp]))
{
  include STLCBase_Ty(self[STLC])
}

module type BaseComp_STLC_Exp/Val_Ctx 
    (self[BaseComp]: BaseComp_STLC_Ctx) 
{ 
  include BaseComp_STLC_Ty_Ctx
  include BaseComp_STLC_Ty(self[BaseComp])
}

module type BaseComp_STLC_Exp/Val 
           (self[BaseComp] : BaseComp_STLC_Ctx)
           (self[STLC] : BaseComp_STLC_Exp/Val_Ctx(self[BaseComp]))           
{ 
  include STLCBase_Exp/Val(self[STLC])
}


module type BaseComp_STLC (self[BaseComp] : BaseComp_STLC_Ctx) { 
  module STLC : sig
    include BaseComp_STLC_Exp/Val_Ctx(self[BaseComp])
    include BaseComp_STLC_Exp/Val(self[BaseComp])
  end 
}



family A { 
   Inductive t := FF 
   family B { 
      Inductive t := ...
      Definition convert : self[B].t -> self[A].t := ...
      family C {
          Inductive t := ...
          Definition convert : self[C].t -> self[B].t := ...
          family D { 
              Inductive t := ...
              Definition convert : self[D].t -> self[C].t := ...
          }
      }
   } 
}

family A' extends A { 
    family B { 
        family C { 
            family D { }
        } 
    }
}

(* ==> *)

module type B_Ctx { }



