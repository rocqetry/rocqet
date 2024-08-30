Module Type STLC_Ty_Ctx.
End STLC_Ty_Ctx.

(* Module Type STLC_Ty_Artifact (self : STLC_Ty_Ctx).
  Axiom Ty : Set.
  Axiom STLC_TNat : Ty.
  Axiom STCL_TTuple : Ty -> Ty.
End STLC_Ty_Artifact. *)

Module Type STLC_Ty (self : STLC_Ty_Ctx). 
  Axiom Ty : Set.
  Axiom TNat : Ty. 
  Axiom TTuple : Ty -> Ty.
 End STLC_Ty.

Module Type PairExt_Ctx.
End PairExt_Ctx.

(* Module Type PairExt_Ty_Artifact (self : PairExt_Ctx).
  Include STLC_Ty_Artifact(self).
  Axiom PairExt_TTuple : Ty -> Ty -> Ty.
End PairExt_Ty_Artifact.*)

Module Type PairExt (self : PairExt_Ctx). 
  Axiom Ty : Set.
  Axiom TNat : Ty.
  Axiom TTuple : Ty -> Ty -> Ty.
End PairExt.

Module Type LamExt_Ctx.
End LamExt_Ctx.

Module Type LamExt (self : LamExt_Ctx).
  Include STLC_Ty (self).
End LamExt.
