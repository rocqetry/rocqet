Require Import Rocqet.Loader.

Family X.

MetaData pick binds Yes, No.
Inductive pick := Yes | No.
FEnd pick.

FDefinition x := Yes.

FEnd X.

Family A extends X.
FEnd A.

Family Y.
Family B. 
Family C.
Family D extends X. FEnd D.
FEnd C.
FEnd B.
FEnd Y.

