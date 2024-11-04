Require Import NFPOP.Loader.

Family A.

Family C.
FInductive expr : Type := 
| Eaddr : expr.
FEnd C.

Family I := C.

FDefinition Y := I.Eaddr.

FEnd A.

Family B extends A.

Family C.
FInductive expr : Type := 
| Esizeof : expr.
FEnd C.

FEnd B.

Print B.I.

