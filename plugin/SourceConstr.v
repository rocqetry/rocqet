Definition a : nat.  Proof. Admitted.

family STLC {
  Inductive Ty : Set := TNat : Ty | TTuple : Ty -> Ty 
}

family PairExt { 
  Inductive Ty : Set += TTuple : Ty -> Ty -> Ty
}

(* ==> *)

module type STLC_Ty_Ctx { }
module type STLC_Ty_Artifact (self : STLC_Ty_Ctx) { 
  Axiom Ty : Set 
  Axiom STLC_TNat : Ty 
  Axiom STCL_TTuple : Ty -> Ty 
}

module type STLC_Ty (self : STLC_Ty_Ctx) {
  include STLC_Ty_Artifact(self)
  Axiom TNat : Ty 
  Axiom TTuple : Ty -> Ty 
}

module type PairExt_Ctx { }
module type PairExt_Artifact (self : PairExt_Ctx) {
  include STLC_Ty_Artifact(self)
  Axiom PairExt_TTuple : Ty -> Ty -> Ty
}
module type PairExt (self : PairExt_Ctx) {
  include PairExt_Ty_Artifact(self)
  Axiom TNat : Ty 
  Axiom TTuple : Ty -> Ty Ty 
}
