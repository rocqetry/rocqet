(* Can we maintain modularity if we compile to records instead of modules?  *)

Record STLC_tm_ctx := { }.

Record STLC_tm_ty := {
    tm : Set
}.

Definition STLC_tm := forall (self : STLC_tm_ctx),  STLC_tm_ty.

