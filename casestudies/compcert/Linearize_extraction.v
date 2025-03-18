From Rocqet Require Import Loader.
From Rocqet Require Import LibTactics.

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

Require Import LTL.
Require Import LfamBase.
Require Import Linear.

From Rocqet Require Import Registers.     

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

Trait Base.

(* LTL -> Linear *)
Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

From Rocqet Require Import Lattice.
From Rocqet Require Import Kildall.

(* Determination of the order of basic blocks *)

Module DS := Dataflow_Solver(LBoolean)(NodeSetForward).

FDefinition reachable_aux : S.function -> option (PMap.t bool) :=
  fun (f: S.function) =>
  DS.fixpoint
    (S.fn_code f) S.successors_block
    (fun pc r => r)
    (S.fn_entrypoint f) true.

FDefinition reachable : S.function -> PMap.t bool := fun f =>
  match reachable_aux f with
  | None => PMap.init true
  | Some rs => rs
  end.

MetaData enumerate_aux.
Parameter enumerate_aux: self__Linearize.S.function -> PMap.t bool -> list self__Linearize.S.node.
FEnd enumerate_aux.

Module Nodeset := FSetAVL.Make(OrderedPositive).

From Rocqet Require Import Errors.
Open Scope error_monad_scope.

MetaData nodeset_of_list.
Fixpoint nodeset_of_list (l: list self__Linearize.S.node) (s: Nodeset.t)
                         {struct l}: res Nodeset.t :=
  match l with
  | nil => OK s
  | hd :: tl =>
      if Nodeset.mem hd s
      then Error (msg "Linearize: duplicates in enumeration")
      else nodeset_of_list tl (Nodeset.add hd s)
  end.
FEnd nodeset_of_list.

FDefinition check_reachable_aux := 
     fun (reach: PMap.t bool) (s: Nodeset.t)
     (ok: bool) (pc: S.node) (bb: S.bblock) =>
  if reach!!pc then ok && Nodeset.mem pc s else ok.

FDefinition check_reachable := 
     fun (f: S.function) (reach: PMap.t bool) (s: Nodeset.t) =>
  PTree.fold (check_reachable_aux reach s) (S.fn_code f) true.

FDefinition enumerate : S.function -> res (list S.node) := fun f => 
  let reach := reachable f in
  let enum := enumerate_aux f reach in
  do s <- nodeset_of_list enum Nodeset.empty;
  if check_reachable f reach s
  then OK enum
  else Error (msg "Linearize: wrong enumeration").

FRecursion starts_with_label about T.instruction motive (fun (_ : T.instruction) => T.label -> bool) by _rect.
Case Llabel lbl' := (fun lbl => peq lbl lbl').
Case Lop op args res := (fun lbl => false).
Case Lgetstack sl ofs ty r := (fun lbl => false).
Case Lsetstack r sl ofs ty := (fun lbl => false).
Case Lcond cond args lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false).
Case Lgoto lbl' := (fun lbl => false).
FEnd starts_with_label.

MetaData starts_with.
Fixpoint starts_with (lbl: self__Linearize.T.label) (k: self__Linearize.T.code) {struct k} : bool :=
     match k with
     | i :: k' => if self__Linearize.starts_with_label i lbl then true else starts_with lbl k'
     | _ => false
     end.
FEnd starts_with.
              
FDefinition add_branch : T.label -> T.code -> T.code := fun (s: T.label) (k: T.code) =>
   if starts_with s k then k else T.Lgoto s :: k.

FRecursion translate_instr about S.instruction motive (fun (_ : S.instruction) => (T.code -> T.code) -> T.code -> T.code) by _rect.
Case Lop op args res := (fun f k => T.Lop op args res :: f k).
Case Lgetstack sl ofs ty r := (fun f k => T.Lgetstack sl ofs ty r :: f k).
Case Lsetstack r sl ofs ty := (fun f k => T.Lsetstack r sl ofs ty :: f k).
Case Lbranch s := (fun f k => add_branch s k).
Case Lcond cond args s1 s2 :=
(fun f k => if starts_with s1 k then T.Lcond (Op.negate_condition cond) args s2 :: add_branch s1 k else T.Lcond cond args s1 :: add_branch s2 k).
Case Lreturn := (fun f k => T.Lreturn :: f k).
FEnd translate_instr.
       
MetaData linearize_block.
Fixpoint linearize_block (b: self__Linearize.S.bblock) (k: self__Linearize.T.code) : self__Linearize.T.code :=
   match b with
   | nil => k
   | i :: b' => self__Linearize.translate_instr i (linearize_block b') k
   end.
FEnd linearize_block.

FDefinition linearize_node : S.function -> S.node -> T.code -> T.code :=
  fun (f: S.function) (pc: S.node) (k: T.code) =>
  match (S.fn_code f)!pc with
  | None => k
  | Some b => T.Llabel pc :: linearize_block b k
  end.

FDefinition linearize_body : S.function -> list S.node -> T.code :=
  fun (f: S.function) (enum: list S.node) =>
  list_fold_right (linearize_node f) enum nil.

FDefinition transf_function : S.function -> res T.function := fun f =>
  do enum <- enumerate f;
  OK (T.mkfunction
       (S.fn_sig f)
       (S.fn_stacksize f)
       (add_branch (S.fn_entrypoint f) (linearize_body f enum))).

FDefinition transf_fundef : S.fundef -> res T.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res T.program := fun p =>
  transform_partial_program transf_fundef p.

FEnd Linearize.

FEnd Base.

Trait Comp_Loops extends Base.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Family Linearize.

FRecursion starts_with_label.
Case Ljumptable a b  := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Ljumptable args tbl := (fun f k => T.Ljumptable args tbl :: k).
FEnd translate_instr.

FEnd Linearize.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Linearize.

FRecursion starts_with_label.
Case _ := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lbuiltin ef args res := (fun f k => T.Lbuiltin ef args res ::f k).
FEnd translate_instr.

FEnd Linearize.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

FRecursion starts_with_label.
Case Lstore a b c d := (fun lbl => false).
Case Lload a b c d := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lstore chunk addr args src := (fun f k => T.Lstore chunk addr args src :: f k).
Case Lload chunk addr args dst := (fun f k => T.Lload chunk addr args dst :: f k).
FEnd translate_instr.

FEnd Linearize.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Linearize.
FEnd Linearize.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

FRecursion starts_with_label.
Case Lcall a b := (fun lbl => false).
Case Ltailcall a b := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lcall sig ros := 
  (fun f k => T.Lcall sig ros :: f k).
Case Ltailcall sig ros := 
 (fun f k => T.Ltailcall sig ros :: k).
FEnd translate_instr.
  
FEnd Linearize.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Family Linearize.
FEnd Linearize.

FEnd Comp_Switch.

Family Comp extends  
  Base,
  Comp_Loops,  
  Comp_Field, 
  Comp_Call,
  Comp_Heap,        
  Comp_Builtin,
  Comp_Switch.

Family Linearize.
Final Family S := LTL.
Final Family T := Linear.
FEnd Linearize.

FEnd Comp.

Require Extraction.

Cd "extraction".

(* Go! *)

Separate Extraction Comp.Linearize.
