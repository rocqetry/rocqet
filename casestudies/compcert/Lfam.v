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

Local Open Scope string_scope.
Local Open Scope list_scope.
Open Scope asm.

(* RISC-V *)

Local Open Scope error_monad_scope.

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

Trait Base.

Family Lfam.
FDefinition label := positive.

FInductive instruction: Type :=
| Lop : Op.operation -> list mreg -> mreg -> instruction
| Lcond : Op.condition -> list mreg -> label -> instruction
| Llabel: label -> instruction
| Lgoto: label -> instruction
| Lreturn : instruction.

FDefinition code: Type := list instruction.

FOpaque Definition function : Type := cheat.
FOpaque Definition function_sig: function -> signature := cheat.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

FDefinition genv := Genv.t fundef unit.

FRecursion is_label about instruction motive (fun (_ : instruction) => label -> bool) by _rect.
Case Lop op arg dst := (fun lbl => false).
Case Lcond c args l := (fun lbl => false). 
Case Llabel lbl' := (fun lbl => if peq lbl lbl' then true else false).
Case Lgoto lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false).
FEnd is_label.

MetaData find_label.
Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label i1 lbl then Some il else find_label lbl il
  end.
FEnd find_label.

FEnd Lfam.

FEnd Base.

Trait Comp_Loops extends Base.

Family Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Lfam.
FEnd Lfam.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Lfam.
FEnd Lfam.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family Lfam.
FEnd Lfam.

FEnd Comp_Switch.

(* Family Comp extends
  Comp_Heap,             
  Base,
  Comp_Switch,
  Comp_Loops,  
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin.

FEnd Comp.*)
