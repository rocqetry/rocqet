(* 
Require Import Demo.

Family Ra extends A10.
FEnd Ra.

 *)

(*Family X.
   Family Inner.
      FDefinition x := 42.
   FEnd Inner.
   
   FDefinition y := 10.

   FInductive ty : Set :=
      | ty_unit : ty
      | ty_arrow : ty -> ty -> ty.

FEnd X.   

Family Y extends X.
    FInductive ty : Set :=
      | ty_bool : ty. *)

(*Family A.
   Family B.
      Family C.
          Family D.
              FInductive ty : Set :=
                | ty_dummy : ty.
          FEnd D.
      FEnd C.
   FEnd B.
FEnd A.*)

