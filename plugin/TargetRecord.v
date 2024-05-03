Require Export Coq.Strings.String.
(* Can we maintain modularity if we compile to records instead of modules?  *)

(* module type STLCBase_Ty_Ctx { } *)
Record STLCBase_Ty_Ctx := { }.

Record STLCBase_Ty (self : STLCBase_Ty_Ctx) := { 
    Ty : Set; 
    TyUnit : Ty; 
    TNat : Ty; 
    TArr : Ty -> Ty -> Ty
}.

Record STLCBase_ExpVal_Ctx := { 
    ctx : STLCBase_Ty_Ctx; 
    elem : STLCBase_Ty(ctx); 
}.

Record STLCBase_EXPVal (self: STLCBase_ExpVal_Ctx) := {
   Exp : Set;
   Val : Set;
   EVal : Val -> Exp;
   EApp : Exp -> Exp -> Exp;
   Unit : Val;
   Var : string -> Val;
   Lam : string -> Exp -> Val;
}.

Record STLCIf_Ty_Ctx := { }.

(* https://coq.inria.fr/doc/V8.19.0/refman/addendum/implicit-coercions.html *)
Axiom to_base : STLCIf_Ty_Ctx -> STLCBase_Ty_Ctx.

Record STLCIf_Ty (self : STLCIf_Ty_Ctx) := {
    super : STLCBase_Ty(to_base self);
}.

