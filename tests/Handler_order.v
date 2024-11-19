Require Import Rocqet.Loader.

Family Compiler_Arr.
Family STLC_Arr.
FInductive ty : Set :=     
  | ty_arrow : ty -> ty -> ty.

FEnd STLC_Arr.

Family STLC_Eval.
Family S extends STLC_Arr. FEnd S.

FRecursion subst about S.ty motive (fun (_: S.ty) => nat) by _rect.  
Case ty_arrow a b := (subst a + subst b).
FEnd subst.

FEnd STLC_Eval.

FEnd Compiler_Arr.

Family Compiler_Rest extends Compiler_Arr.

Trait STLC_Unit extends STLC_Arr.
FInductive ty : Set :=
     | ty_unit : ty.
FEnd STLC_Unit.

Trait STLC_Prod extends STLC_Arr.
FInductive ty : Set :=
  | ty_prod : ty -> ty -> ty.
FEnd STLC_Prod.

Trait STLC_nat extends STLC_Arr.
FInductive ty : Set :=
| ty_nat : ty.
FEnd STLC_nat.

Family STLC_Arr
  extends
    STLC_Unit,
    STLC_Prod,
    STLC_nat.                
FEnd STLC_Arr.

Trait STLC_Unit_Eval extends STLC_Eval.
Family S extends STLC_Unit. FEnd S.

FRecursion subst.
Case ty_unit := 0.
FEnd subst.
FEnd STLC_Unit_Eval.

Trait STLC_nat_Eval extends STLC_Eval.
Family S extends STLC_nat. FEnd S.

FRecursion subst.
Case ty_nat := 1.
FEnd subst.
FEnd STLC_nat_Eval.

Trait STLC_Prod_Eval extends STLC_Eval.
Family S extends STLC_Prod. FEnd S.

FRecursion subst.
Case ty_prod l r := (subst l + 1).
FEnd subst.
FEnd STLC_Prod_Eval.

Family STLC_Eval
  extends
  STLC_Prod_Eval,
  STLC_Unit_Eval,
  STLC_nat_Eval.
FEnd STLC_Eval.

FEnd Compiler_Rest.

  
