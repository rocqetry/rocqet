Require Import Rocqet.Loader.

Family RV.

Family Common.
FDefinition a := 10.
FEnd Common.

Family RV32I extends Common.
FDefinition b := 10.
FDefinition c := 10.
FEnd RV32I.

Family RV64I extends RV32I.
FDefinition d := 10.
FDefinition e := 10.
FEnd RV64I.

FEnd RV.

Family Comp.

Family Inner.

Family Asm extends RV.RV64I.
FDefinition y := 10.
FEnd Asm.

FEnd Inner.

FEnd Comp.
