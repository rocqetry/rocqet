Require Import STLC_base.
Require Import STLC_bool.
Require Import STLC_prod.
Require Import Rocqet.Loader.

Family A extends STLC_prod.
FEnd A.

Family C extends STLC_bool.
FEnd C.

Family all extends STLC, STLC_bool, STLC_prod.
FEnd all.






