From Rocqet Require Import Loader.

From Rocqet Require Import Coqlib.
From Rocqet Require Import Errors.
From Rocqet Require Import Values.
From Rocqet Require Import AST.
From Rocqet Require Import Integers. 
From Rocqet Require Import Floats.
From Rocqet Require Import Memory.
From Rocqet Require Import Globalenvs.
From Rocqet Require Import Smallstep.
From Rocqet Require Import Events.
From Rocqet Require Import Maps.
From Rocqet Require Import Linking.
Require Import Rocqet.CompCert.lib.Ctypes.
From Rocqet Require Import Cop.
From Rocqet Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From Rocqet Require Import Prelude.
From Rocqet Require Import Op.

Require Import CfamBase.

Trait Base.

Trait Cfamtransl.
Family S extends Cfam. FEnd S.
Family T extends Cfam. FEnd T.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

FOpaque Definition earg : Type := cheat.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => earg -> res T.expr) by _rect.
Case Evar id := (fun _ => OK (T.Evar id)).
FEnd transl_expr.

FOpaque Definition sarg : Type := cheat.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => earg -> sarg -> res T.stmt) by _rect.
Case Sskip := (fun _ _ => OK (T.Sskip)).
Case Sassign id e :=
  (fun earg _ =>
     do te <- transl_expr e earg;
     OK (T.Sassign id te)).
Case Sseq s1 s2 :=
 (fun earg sarg =>
    do ts1 <- transl_stmt s1 earg sarg; 
    do ts2 <- transl_stmt s2 earg sarg; 
    OK (T.Sseq ts1 ts2)).
Case Sreturn expr :=
  (fun earg _ =>
     match expr with
     | None => OK (T.Sreturn None)
     | Some expr =>
          do te <- transl_expr expr earg;
          OK (T.Sreturn (Some te))
     end).
Case Slabel lbl s :=
  (fun earg sarg =>                          
     do ts <- transl_stmt s earg sarg;
     OK (T.Slabel lbl ts)).
Case Sgoto lbl := (fun earg sarg => OK (T.Sgoto lbl)).
FEnd transl_stmt.

(* Overridable in derived families *)
FOpaque Definition transl_function : S.function -> res T.function :=
  cheat.

FDefinition transl_fundef : S.fundef -> res T.fundef := fun f =>
   transf_partial_fundef transl_function f.

FDefinition transl_program : S.program -> res T.program := fun p =>
  transform_partial_program transl_fundef p.

FEnd Cfamtransl.

FEnd Base.

Trait Comp_Heap extends Base.

Trait Cfamtransl.
FEnd Cfamtransl.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Trait Cfamtransl.
FEnd Cfamtransl.

FEnd Comp_Field.


Trait Comp_Loops extends Base.

Trait Cfamtransl. FEnd Cfamtransl.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

Trait Cfamtransl. FEnd Cfamtransl.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base, Comp_Call.

Trait Cfamtransl. FEnd Cfamtransl.

FEnd Comp_Builtin.

Trait Comp_External extends Base.

Trait Cfamtransl. FEnd Cfamtransl.

FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Trait Cfamtransl. FEnd Cfamtransl.

FEnd Comp_Call.


(*Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  Comp_External,
  Comp_Builtin.

FEnd Comp.*)
