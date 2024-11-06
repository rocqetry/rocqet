From NFPOP Require Import Loader.

Definition ident := nat.


Family Base.

Family Asm.
FDefinition operation := nat.

FDefinition condition := nat.
FEnd Asm.

Family C.
FInductive expr : Type :=
| Evar : ident -> expr (* reading a temporary variable *)  
| Econdition : condexpr -> expr -> expr -> expr
| Eop : Asm.operation -> exprlist -> expr
| Elet : expr -> expr -> expr
| Eletvar : nat -> expr
with exprlist : Type :=
| Enil: exprlist
| Econs: expr -> exprlist -> exprlist
with condexpr : Type :=
| CEcond : Asm.condition -> exprlist -> condexpr
| CEcondition : condexpr -> condexpr -> condexpr -> condexpr
| CElet: expr -> condexpr -> condexpr.
FEnd C.


Family S.
FRecursion transl_expr about C.expr motive (fun (_ : C.expr) => nat -> nat)
  with transl_exprlist about C.exprlist motive (fun (_ : C.exprlist) => nat -> nat)
  with transl_condexpr about C.condexpr motive (fun (_ : C.condexpr) => nat -> nat) by _rect.
Case Evar i := (fun _ => 0).
Case Econdition c a b := (fun _ => 0).
Case Eop a b := (fun _ => 0).
Case Elet a b := (fun _ => 0).
Case Eletvar n := (fun _ => 0).

Case Enil := (fun _ => 0).
Case Econs a b := (fun _ => 0).

Case CEcond c e := (fun _ => 0).
Case CEcondition a b c := (fun _ => 0).
Case CElet a b := (fun _ => 0).
FEnd transl_expr with transl_exprlist with transl_condexpr.
FEnd S.

Family STLC_top.
Family X.
FInductive tm : Set :=
  | tm_var : ident -> tm.
FEnd X.
FEnd STLC_top.

Family STLC extends STLC_top.

Family X.
FInductive tm : Set :=
| tm_app : tm -> tm -> tm
| tm_val : val -> tm
with val : Set :=
| val_abs : ident -> tm -> val
| val_unit: val.
FEnd X.

Family Y.
FRecursion blah about X.tm motive (fun (_ : X.tm) => nat) by _rect.
Case tm_val v := 0.
Case tm_var i := 0.
Case tm_app f a := 0.
FEnd blah.
FEnd Y.

Family Z.
FRecursion comb_size_tm about X.tm motive (fun (_ : X.tm) => nat)
      with comb_size_val about X.val motive (fun (_ : X.val) => nat) by _rect.
Case tm_var i := 0.
Case tm_app f a := 0.
Case tm_val v := 0.

Case val_abs x body := 0.
Case val_unit := 0.
FEnd comb_size_tm with comb_size_val.

FEnd Z.

FEnd STLC.

FEnd Base.
