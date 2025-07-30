Require Import Rocqet.Loader.

Definition ident := nat.

(*Record lambda_arg : Set := Build_lambda_arg { id : ident }.
Definition x := {| id := 0 |}.*)

(*Record lambda_arg : Set := {
    id : ident;
  }.


Definition y := Build_lambda_arg 0.*)

Family STLC.

FInductive ty: Set :=
| ty_unit : ty
| ty_arrow : ty -> ty -> ty.

FRecord lambda_arg : Set := { id : ident }.

(* FDefinition i := {| x := 10 |}.*)
FDefinition x : lambda_arg := {| id := 10 |}. 
(* FDefinition y : ident := id {| id := 10 |}.*)

(*
FLemma easy_lemma : id (Build_lambda_arg_STLC 10) = 10.
FProofLemma.
fsimpl.
Qed. CloseFLemma.
*)


(*
MetaData lambda_arg_eq_STLC.
Axiom axiom_id : forall x, id (Build_lambda_arg_STLC x) = x.
FEnd lambda_arg_eq_STLC.
*)

FInductive tm : Type :=
| tm_var : ident -> tm    
| tm_abs : lambda_arg -> tm -> tm
| tm_app : tm -> tm -> tm
| tm_unit: tm.

FEnd STLC.


Family SystemF extends STLC.

FDefinition tvar := nat.

FInductive ty: Set :=
| ty_forall : tvar -> ty -> ty. (* ∀α.T *)

(* tm_abs is extended with a type *)
FRecord A : Set := { }.

FRecord lambda_arg : Set := { arg_ty : ty } default arg_ty := ty_unit.

FDefinition kl : lambda_arg := {| id := 10; arg_ty := ty_unit; |}.

FDefinition j := Build_lambda_arg_SystemF 10 ty_unit.

FEnd SystemF.

(*
MetaData lambda_arg_constr_SystemF.
Axiom Build_lambda_arg_SystemF : ident -> ty -> lambda_arg.
FEnd lambda_arg_constr_SystemF.

(* Is it possible to modularly compose two records? We need a way to supply the
   default value. A couple of options:
   - Allow field to have default values regardless of whether we're extending
     a field or not
   - Allow to supply the default value like a proof obligation -- similar to
     FRecursion/FInduction *)
MetaData lambda_arg_eq_STLC.
Axiom axiom_id0 : forall i t, arg_ty (Build_lambda_arg_SystemF i t) = t.
Axiom axiom_id1 : forall i, (Build_lambda_arg_STLC i) = (Build_lambda_arg_SystemF i ty_unit).
FEnd lambda_arg_eq_STLC.


FInductive tm : Type :=  
| tm_tabs : tvar -> tm -> tm  (* Λα.t *)
| tm_tapp : tm -> ty -> tm.   (* t [T] *)

FEnd SystemF.

Family SystemFOmega extends SystemF.

FRecord B : Set := { } default arg_ty := ty_unit, argn := 10.

FEnd SystemFOmega.
*)
