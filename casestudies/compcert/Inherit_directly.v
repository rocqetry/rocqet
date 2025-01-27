Require Import Rocqet.Loader.

Family F.
FInductive A : Set := a : A.
FInductive P : A -> Prop := Pa : P a.
FInduction PP about A motive (fun (x : A) => P x).
FProof.
fconstructor.
Qed. FEnd PP.
FEnd F.

Family G extends F.
Inherit A.
FDefinition a_check := a.
Inherit PP.
FInduction PP' about A motive (fun (x : A) => P x).
FProof.
apply PP.
Qed. FEnd PP'.
FEnd G.
