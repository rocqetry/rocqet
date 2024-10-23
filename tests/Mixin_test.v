From NFPOP Require Import Loader.

Family STLC.
  Family X.
    FInductive ty : Set :=     
     | ty_arrow : ty -> ty -> ty.
    FDefinition stlc := 10.
  FEnd X.           
FEnd STLC.

Family STLC_unit.
  Family X.
    FInductive ty : Set :=     
     | ty_unit : ty.
    FDefinition stlc_unit := 10.
  FEnd X.           
FEnd STLC_unit.

Family STLC_bool.
  Family X.
    FInductive ty : Set :=
      | ty_bool : ty.          
    FDefinition stlc_bool := 10.
  FEnd X.   
FEnd STLC_bool.

Family STLC_prod.
  Family X.
  FInductive ty : Set :=
    | ty_prod : ty -> ty -> ty.
  FDefinition stlc_prod := 10.
  FEnd X.  
FEnd STLC_prod.

Family Al extends STLC, STLC_unit, STLC_bool, STLC_prod.
FEnd Al.

Check Al.X.ty_arrow.
Check Al.X.ty_unit.
Check Al.X.ty_bool.
Check Al.X.ty_prod.



