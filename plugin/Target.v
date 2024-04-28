
module type STLC_Ctx { }

module type STLC_Ty_Ctx { 
  include STLC_Ctx
}

module type STLC_Ty (self: STLC_Ty_Ctx) {
  Axiom Ty : Set 
  Axiom TyUnit : Ty 
}

module type STLC_Exp_Ctx {
  include STLC_Ty_Ctx
  include STLC_Ty
}

module type STLC_Exp (self: STLC_Exp_Ctx) {
  Axiom Exp : Set 
  Axiom EVal :               
}

module type STLC_Family (self: STLC_Ctx) { 
  module type STLC_Sig { 
      
  }
  module STLC : STLC_Sig 
}
