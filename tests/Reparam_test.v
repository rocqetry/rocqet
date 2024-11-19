Require Import Rocqet.Loader.

Family Imp. 
   MetaData intsize.
     Inductive intsize : Type :=
     | I8: intsize
     | I16: intsize
     | I32: intsize
     | IBool: intsize.
   FEnd intsize.

  Family CminorVariant.
    FDefinition Ofoo := 10.
    (*FInductive constantk : Type :=
       | Ointconstk: (*int ->*) constantk. *)

    FInductive constant : Type :=
       | Ointconst: (*int ->*) constant 
       | Ofloatconst: (*float ->*) constant 
       | Osingleconst: (*float32 ->*) constant
       | Olongconst: (*int64 -> *) constant.
  FEnd CminorVariant.

  Family CminorTransl.
     Family Source extends CminorVariant.
     FEnd Source.
  FEnd CminorTransl.
FEnd Imp.

Family Y extends Imp.
FEnd Y.
