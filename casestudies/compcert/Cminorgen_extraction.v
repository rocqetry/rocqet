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
Require Import Csharpminor.
Require Import Cminor.
Require Import Cfamtransl.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Trait Base.

Family Cminorgen extends Cfamtransl.

Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FDefinition compilenv := PTree.t Z.
FDefinition exit_env : Type := list bool.

FRecursion transl_constant about S.constant motive (fun (_ : S.constant) => T.constant) by _rect.
Case Ointconst n := (T.Ointconst n).
Case Ofloatconst n := (T.Ofloatconst n).
Case Osingleconst n := (T.Osingleconst n).
Case Olongconst n := (T.Olongconst n).
FEnd transl_constant.

FOverride Definition earg := compilenv.

FRecursion transl_expr.
Case Econst c := (fun earg => OK (T.Econst (transl_constant c))).
Case Eunop op e1 := 
  (fun arg => do te1 <- transl_expr e1 arg; OK (T.Eunop op te1)).
Case Ebinop op e1 e2 :=
  (fun arg => 
     do te1 <- transl_expr e1 arg;
     do te2 <- transl_expr e2 arg;
     OK (T.Ebinop op te1 te2)).
FEnd transl_expr.

FOverride Definition sarg := exit_env.

FRecursion transl_stmt.
Case Sifthenelse e s1 s2 :=
 (fun earg sarg => 
    do te <- transl_expr e earg;
    do ts1 <- transl_stmt s1 earg sarg;
    do ts2 <- transl_stmt s2 earg sarg;
    OK (T.Sifthenelse te ts1 ts2)).
FEnd transl_stmt.

(* Stack layout *)
FDefinition block_alignment : Z -> Z := fun sz =>
    if zlt sz 2 then 1
    else if zlt sz 4 then 2
    else if zlt sz 8 then 4 else 8.

FDefinition assign_variable : compilenv * Z -> ident * Z -> compilenv * Z := 
    fun cenv_stacksize id_sz => 
    let (id, sz) := id_sz in
    let (cenv, stacksize) := cenv_stacksize in
    let ofs := align stacksize (block_alignment sz) in
    (PTree.set id ofs cenv, ofs + Z.max 0 sz).

FDefinition assign_variables : compilenv * Z -> list (ident * Z) -> compilenv * Z :=
    fun cenv_stacksize vars => List.fold_left assign_variable vars cenv_stacksize.

FDefinition build_compilenv : S.function -> compilenv * Z :=
    fun f => assign_variables (PTree.empty Z, 0) (VarSort.sort (S.fn_vars f)).

(* Translate Function, Fundef, Program *)
FDefinition transl_funbody := 
fun (cenv: compilenv) (stacksize: Z) (f: S.function) =>
  do tbody <- transl_stmt (S.fn_body f) cenv nil ;
  OK (T.mkfunction
        (S.fn_sig f)
        (S.fn_params f)
        (S.fn_temps f)
        stacksize
        tbody).

FOverride Definition transl_function := fun f =>
  let (cenv, stacksize) := build_compilenv f in
  if zle stacksize Ptrofs.max_unsigned
  then transl_funbody cenv stacksize f
  else Error(msg "Cminorgen: too many local variables, stack size exceeded").

Inherit transl_program.

FEnd Cminorgen.

FEnd Base.

Trait Comp_Loops extends Base.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit exit_env.

MetaData shift_exit.
Fixpoint shift_exit (e: exit_env) (n: nat) {struct e} : nat :=
  match e, n with
  | nil, _ => n
  | false :: e', _ => Datatypes.S (shift_exit e' n)
  | true :: e', O => O
  | true :: e', Datatypes.S m => Datatypes.S (shift_exit e' m)
  end.
FEnd shift_exit.

FRecursion transl_stmt.
Case Sloop s :=
  (fun cenv xenv => 
    do ts <- transl_stmt s cenv xenv;
    OK (T.Sloop ts)).
Case Sblock s :=
  (fun cenv xenv =>
      do ts <- transl_stmt s cenv (true :: xenv);
      OK (T.Sblock ts)).
Case Sexit n :=
  (fun cenv xenv =>    
      OK (T.Sexit (shift_exit xenv n))).
FEnd transl_stmt.

FEnd Cminorgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit transl_expr.

MetaData transl_exprlist.
Fixpoint transl_exprlist 
  (cenv: compilenv) (el: list S.expr)
                     {struct el}: res (list T.expr) :=
  match el with
  | nil =>
      OK nil
  | e1 :: e2 =>
      do te1 <- transl_expr e1 cenv;
      do te2 <- transl_exprlist cenv e2;
      OK (te1 :: te2)
  end.
FEnd transl_exprlist.

FRecursion transl_stmt.
Case Sbuiltin optid ef el :=
   (fun cenv xenv => 
      do tel <- transl_exprlist cenv el;
      OK (T.Sbuiltin optid ef tel)).
FEnd transl_stmt.

FEnd Cminorgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit compilenv.

FDefinition var_addr : compilenv -> ident -> T.expr := fun cenv id =>
  match PTree.get id cenv with
  | Some ofs => T.Econst (T.Oaddrstack (Ptrofs.repr ofs))
  | None => T.Econst (T.Oaddrsymbol id Ptrofs.zero)
  end.

FRecursion transl_expr.
Case Eaddrof id := (fun cenv => OK (var_addr cenv id)).
Case Eload chunk e :=
  (fun cenv => 
     do te <- transl_expr e cenv;
     OK (T.Eload chunk te)).
FEnd transl_expr.

FRecursion transl_stmt.
Case Sstore chunk e1 e2 :=
(fun cenv xenv => 
   do te1 <- transl_expr e1 cenv;
   do te2 <- transl_expr e2 cenv;
   OK (T.Sstore chunk te1 te2)).
FEnd transl_stmt.

FEnd Cminorgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion transl_stmt.
Case Scall optid sig e el :=
  (fun cenv xenv => 
     do te <- transl_expr e cenv;
     do tel <- transl_exprlist cenv el;
   OK (T.Scall optid sig te tel)).
FEnd transl_stmt.

FEnd Cminorgen.

FEnd Comp_Call.

From Rocqet Require Import Switch.
Trait Comp_Switch extends Comp_Loops.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion switch_table about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => nat -> list (Z * nat) * nat) by _rect.
Case LSnil := (fun k => (nil, k)).
Case LScons lbl stmt rem :=
(fun k =>
   match lbl with
   | None => let (tbl, dfl) := switch_table rem ((1 + k)%nat) in (tbl, k)
   | Some ni => let (tbl, dfl) := switch_table rem ((1 + k)%nat) in ((ni, k) :: tbl, dfl)
   end).
FEnd switch_table.

Inherit exit_env.

FRecursion switch_env about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => exit_env -> exit_env) by _rect.
Case LSnil := (fun e => e).
Case LScons a b ls' := (fun e => false :: switch_env ls' e).
FEnd switch_env.

(* Extending non mutual induction to be mutual *)
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => earg -> sarg -> res T.stmt)
  with transl_lbl_stmt about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => earg -> sarg -> T.stmt -> res T.stmt) by _rect.

Case Sswitch long e ls :=
  (fun cenv xenv => 
     let (tbl, dfl) := switch_table ls O in
     do te <- transl_expr e cenv;
     transl_lbl_stmt ls cenv (switch_env ls xenv) (T.Sswitch long te tbl dfl)).

Case LSnil 
  := (fun cenv xenv body => OK (T.Sseq (T.Sblock body) T.Sskip)).
Case LScons a s ls' :=
  (fun cenv xenv body =>
     do ts <- transl_stmt s cenv xenv;
     transl_lbl_stmt ls' cenv (List.tail xenv) (T.Sseq (T.Sblock body) ts)).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cminorgen.

FEnd Comp_Switch.

Family Comp extends 
  Base,  
  Comp_Loops,
  Comp_Builtin,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,    
  Comp_Switch.

Family Cminorgen.
Final Family S := Csharpminor.
Final Family T := Cminor.
FEnd Cminorgen.

FEnd Comp.

Print Comp.Cminorgen.Ctx.
Cd "extraction".

(* Go! *)

Separate Extraction Comp.Cminorgen.
