Require Import STLC_horizon.
Require Import STLC_base.
Require Import Rocqet.Loader.

Family STLC.
  
FDefinition g := X.ty.
FDefinition y := subst_size.

FDefinition c := b.
FDefinition dy := a.
  
FEnd STLC.
