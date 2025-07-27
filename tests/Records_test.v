Require Import Rocqet.Loader.

Definition ident := nat.

(* Record lambda_arg : Set := Build_lambda_arg { id : ident }.*)

(*Record lambda_arg : Set := {
    id : ident;
  }.

Definition x := {| id := 0 |}.
Definition y := Build_lambda_arg 0.*)

Family STLC.
FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.

FRecord lambda_arg : Set := {
    id : ident;
  }.

FDefinition x : lambda_arg := Build_lambda_arg_STLC 10.

FDefinition y : ident := id (Build_lambda_arg_STLC 10).

FEnd STLC.

(*MetaData _id_comp.
Axiom id : lambda_arg ->  ident.
FEnd _id_comp.

MetaData lambda_arg_eq_STLC.
Axiom axiom_id : forall x, id (Build_lambda_arg_STLC x) = x.
FEnd lambda_arg_eq_STLC.*)

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
FRecord lambda_arg : Set := {
    arg_ty : ty;
  }.
FDefault lambda_arg arg_ty := ty_unit.

MetaData lambda_arg_constr_SystemF.
Axiom Build_lambda_arg_SystemF : ident -> ty -> lambda_arg.
FEnd lambda_arg_constr_SystemF.

MetaData lambda_arg_eq_STLC.
Axiom axiom_id0 : forall i t, arg_ty (Build_lambda_arg_SystemF i t) = t.
Axiom axiom_id1 : forall i, (Build_lambda_arg_STLC i) = (Build_lambda_arg_SystemF i ty_unit).
FEnd lambda_arg_eq_STLC.*)


FInductive tm : Type :=  
| tm_tabs : tvar -> tm -> tm  (* Λα.t *)
| tm_tapp : tm -> ty -> tm.   (* t [T] *)

FEnd SystemF.
