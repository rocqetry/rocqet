From NFPOP Require Import Loader.

From NFPOP Require Import Coqlib.
From NFPOP Require Import Errors.
From NFPOP Require Import Values.
From NFPOP Require Import AST.
From NFPOP Require Import Integers. 
From NFPOP Require Import Floats.
From NFPOP Require Import Memory.
From NFPOP Require Import Globalenvs.
From NFPOP Require Import Smallstep.
From NFPOP Require Import Events.
From NFPOP Require Import Maps.
From NFPOP Require Import Linking.
Require Import NFPOP.CompCert.lib.Ctypes.
From NFPOP Require Import Cop.
From NFPOP Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From NFPOP Require Import Prelude.
From NFPOP Require Import Op.

Local Open Scope string_scope.
Local Open Scope list_scope.
Open Scope asm.

Trait Base.

(* C family languages: Csharpminor, Cminor, CminorSel *)
Family Cfam.

FInductive expr : Type :=
| Evar : ident -> expr. (* reading a temporary variable *)

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt.
       
FOpaque Definition function : Type := cheat.
FOpaque Definition function_body : function -> stmt := cheat.
FOpaque Definition function_locals : function -> list ident := cheat.
FOpaque Definition function_params : function -> list ident := cheat.       
FOpaque Definition function_sig : function -> signature := cheat.
       
FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

FEnd Cfam.

(* constants *)
Inductive unary_operation : Type :=
  | Ocast8unsigned: unary_operation(* 8-bit zero extension *)
  | Ocast8signed: unary_operation(* 8-bit sign extension *)
  | Ocast16unsigned: unary_operation(* 16-bit zero extension *)
  | Ocast16signed: unary_operation(* 16-bit sign extension *)
  | Onegint: unary_operation(* integer opposite *)
  | Onotint: unary_operation(* bitwise complement *)
  | Onegf: unary_operation(* float64 opposite *)
  | Oabsf: unary_operation(* float64 absolute value *)
  | Onegfs: unary_operation(* float32 opposite *)
  | Oabsfs: unary_operation(* float32 absolute value *)
  | Osingleoffloat: unary_operation(* float truncation to float32 *)
  | Ofloatofsingle: unary_operation(* float extension to float64 *)
  | Ointoffloat: unary_operation(* signed integer to float64 *)
  | Ointuoffloat: unary_operation(* unsigned integer to float64 *)
  | Ofloatofint: unary_operation(* float64 to signed integer *)
  | Ofloatofintu: unary_operation(* float64 to unsigned integer *)
  | Ointofsingle: unary_operation(* signed integer to float32 *)
  | Ointuofsingle: unary_operation(* unsigned integer to float32 *)
  | Osingleofint: unary_operation(* float32 to signed integer *)
  | Osingleofintu: unary_operation(* float32 to unsigned integer *)
  | Onegl: unary_operation(* long integer opposite *)
  | Onotl: unary_operation(* long bitwise complement *)
  | Ointoflong: unary_operation(* long to int *)
  | Olongofint: unary_operation(* signed int to long *)
  | Olongofintu: unary_operation(* unsigned int to long *)
  | Olongoffloat: unary_operation(* float64 to signed long *)
  | Olonguoffloat: unary_operation(* float64 to unsigned long *)
  | Ofloatoflong: unary_operation(* signed long to float64 *)
  | Ofloatoflongu: unary_operation(* unsigned long to float64 *)
  | Olongofsingle: unary_operation(* float32 to signed long *)
  | Olonguofsingle: unary_operation(* float32 to unsigned long *)
  | Osingleoflong: unary_operation(* signed long to float32 *)
  | Osingleoflongu: unary_operation. (* unsigned long to float32 *)

Inductive binary_operation : Type :=
  | Oadd: binary_operation(* integer addition *)
  | Osub: binary_operation(* integer subtraction *)
  | Omul: binary_operation(* integer multiplication *)
  | Odiv: binary_operation(* integer signed division *)
  | Odivu: binary_operation(* integer unsigned division *)
  | Omod: binary_operation(* integer signed modulus *)
  | Omodu: binary_operation(* integer unsigned modulus *)
  | Oand: binary_operation(* integer bitwise ``and'' *)
  | Oor: binary_operation(* integer bitwise ``or'' *)
  | Oxor: binary_operation(* integer bitwise ``xor'' *)
  | Oshl: binary_operation(* integer left shift *)
  | Oshr: binary_operation(* integer right signed shift *)
  | Oshru: binary_operation(* integer right unsigned shift *)
  | Oaddf: binary_operation(* float64 addition *)
  | Osubf: binary_operation(* float64 subtraction *)
  | Omulf: binary_operation(* float64 multiplication *)
  | Odivf: binary_operation(* float64 division *)
  | Oaddfs: binary_operation(* float32 addition *)
  | Osubfs: binary_operation(* float32 subtraction *)
  | Omulfs: binary_operation(* float32 multiplication *)
  | Odivfs: binary_operation(* float32 division *)
  | Oaddl: binary_operation(* long addition *)
  | Osubl: binary_operation(* long subtraction *)
  | Omull: binary_operation(* long multiplication *)
  | Odivl: binary_operation(* long signed division *)
  | Odivlu: binary_operation(* long unsigned division *)
  | Omodl: binary_operation(* long signed modulus *)
  | Omodlu: binary_operation(* long unsigned modulus *)
  | Oandl: binary_operation(* long bitwise ``and'' *)
  | Oorl: binary_operation(* long bitwise ``or'' *)
  | Oxorl: binary_operation(* long bitwise ``xor'' *)
  | Oshll: binary_operation(* long left shift *)
  | Oshrl: binary_operation(* long right signed shift *)
  | Oshrlu: binary_operation(* long right unsigned shift *)
  | Ocmp: comparison -> binary_operation(* integer signed comparison *)
  | Ocmpu: comparison -> binary_operation(* integer unsigned comparison *)
  | Ocmpf: comparison -> binary_operation(* float64 comparison *)
  | Ocmpfs: comparison -> binary_operation(* float32 comparison *)
  | Ocmpl: comparison -> binary_operation(* long signed comparison *)
  | Ocmplu: comparison -> binary_operation. (* long unsigned comparison *)

Family Csharpminor extends Cfam.
FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant.

FInductive expr : Type :=
| Econst : constant -> expr (* constants *)
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)                                    
                                                                              
FInductive stmt : Type :=
| Sifthenelse: expr -> stmt -> stmt -> stmt
with lbl_stmts : Type :=
  | LSnil: lbl_stmts
  | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

(* function *)
MetaData fn.
Record fn : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list (ident * Z);
  fn_temps: list ident;
  fn_body: self__Csharpminor.stmt
}.
FEnd fn.       
FOverride Definition function := fn.
FOverride Definition function_body := self__Csharpminor.fn_body.
FOverride Definition function_locals := self__Csharpminor.fn_temps.
FOverride Definition function_params := self__Csharpminor.fn_params.
FOverride Definition function_sig := self__Csharpminor.fn_sig.

FEnd Csharpminor.

Family Cminor extends Cfam.
FInductive constant : Type :=
| Ointconst: int -> constant(* integer constant *)
| Ofloatconst: float -> constant(* double-precision floating-point constant *)
| Osingleconst: float32 -> constant(* single-precision floating-point constant *)
| Olongconst: int64 -> constant(* long integer constant *)
| Oaddrsymbol: ident -> ptrofs -> constant(* address of the symbol plus the offset *)
| Oaddrstack: ptrofs -> constant. (* stack pointer plus the given offset *)

FInductive expr : Type :=
| Econst : constant -> expr
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)

FInductive stmt : Type :=
| Sifthenelse: expr -> stmt -> stmt -> stmt
| Sblock: stmt -> stmt.                                           
        
MetaData fn.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: self__Cminor.stmt
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_body := self__Cminor.fn_body.
FOverride Definition function_locals := self__Cminor.fn_vars.
FOverride Definition function_params := self__Cminor.fn_params.
FOverride Definition function_sig := self__Cminor.fn_sig.

FEnd Cminor.

From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.

(* Csharpminor -> Cminor *)
Family Cminorgen.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FDefinition compilenv : Type := PTree.t Z.
FDefinition exit_env : Type := list bool.
FDefinition transl_arg := (compilenv * exit_env)%type.

FRecursion transl_constant about S.constant motive (fun (_ : S.constant) => T.constant) by _rect.
Case Ointconst n := (T.Ointconst n).
Case Ofloatconst n := (T.Ofloatconst n).
Case Osingleconst n := (T.Osingleconst n).
Case Olongconst n := (T.Olongconst n).
FEnd transl_constant.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => transl_arg -> res T.expr) by _rect.
Case Evar id := (fun _ => OK (T.Evar id)).
Case Econst c := (fun _ => OK (T.Econst (transl_constant c))).
Case Eunop op e1 := 
  (fun arg => do te1 <- transl_expr e1 arg; OK (T.Eunop op te1)).
Case Ebinop op e1 e2 :=
  (fun arg => 
     do te1 <- transl_expr e1 arg;
     do te2 <- transl_expr e2 arg;
     OK (T.Ebinop op te1 te2)).
FEnd transl_expr.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => transl_arg -> res T.stmt)
      with transl_lbl_stmt about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => transl_arg -> T.stmt -> res T.stmt) by _rect.
Case Sskip := (fun _ => OK (T.Sskip)).
Case Sassign id e := (fun arg => do te <- transl_expr e arg; OK (T.Sassign id te)).
Case Sseq s1 s2 :=
(fun arg => do ts1 <- transl_stmt s1 arg; 
            do ts2 <- transl_stmt s2 arg; 
            OK (T.Sseq ts1 ts2)).
Case Sreturn e := 
(fun arg => match e with
            | None => OK (T.Sreturn None)
            | Some e =>
                do te <- transl_expr e arg;
                OK (T.Sreturn (Some te))
            end).
Case Slabel lbl s := (fun arg => do ts <- transl_stmt s arg; OK (T.Slabel lbl ts)).
Case Sgoto lbl := (fun arg => OK (T.Sgoto lbl)).
Case Sifthenelse e s1 s2 :=
 (fun arg => 
    do te <- transl_expr e arg;
    do ts1 <- transl_stmt s1 arg;
    do ts2 <- transl_stmt s2 arg;
    OK (T.Sifthenelse te ts1 ts2)).

Case LSnil 
  := (fun arg body => OK (T.Sseq (T.Sblock body) T.Sskip)).
Case LScons a s ls' :=
  (fun arg body =>
     do ts <- transl_stmt s arg;
     transl_lbl_stmt ls' (fst arg, List.tail (snd arg)) (T.Sseq (T.Sblock body) ts)).
FEnd transl_stmt with transl_lbl_stmt.

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
  do tbody <- transl_stmt (S.fn_body f) (cenv, nil) ;
  OK (T.mkfunction
        (S.fn_sig f)
        (S.fn_params f)
        (S.fn_temps f)
        stacksize
        tbody).

FDefinition transl_function := fun (f: S.function) =>
  let (cenv, stacksize) := build_compilenv f in
  if zle stacksize Ptrofs.max_unsigned
  then transl_funbody cenv stacksize f
  else Error(msg "Cminorgen: too many local variables, stack size exceeded").

FDefinition transl_fundef : S.fundef -> res T.fundef := fun f =>
   transf_partial_fundef transl_function f.

FDefinition transl_program : S.program -> res T.program := fun p =>
  transform_partial_program transl_fundef p.

FEnd Cminorgen.

FEnd Base.

Trait Comp_Loops extends Base.

Trait Csharpminor_Sblock extends Csharpminor.
FInductive stmt : Type :=
| Sblock: stmt -> stmt. 
FEnd Csharpminor_Sblock.

Trait Csharpminor_Sexit extends Csharpminor.
FInductive stmt : Type :=
| Sexit: nat -> stmt.
FEnd Csharpminor_Sexit.

Trait Csharpminor_Sloop extends Csharpminor.
FInductive stmt : Type :=
| Sloop: stmt -> stmt.
FEnd Csharpminor_Sloop.

Family Csharpminor extends   
  Csharpminor_Sexit, 
  Csharpminor_Sloop,
  Csharpminor_Sblock.
FEnd Csharpminor.

From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.

Family Cminor.
FInductive stmt : Type :=
| Sexit: nat -> stmt
| Sloop: stmt -> stmt.
FEnd Cminor.

Trait Cminorgen_Sblock extends Cminorgen.
Family S extends Csharpminor_Sblock. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sblock body := (fun args => do ts <- transl_stmt body (fst args, true :: snd args); OK (T.Sblock ts)).
FEnd transl_stmt with transl_lbl_stmt.
FEnd Cminorgen_Sblock.

Trait Cminorgen_Sexit extends Cminorgen.
Family S extends Csharpminor_Sexit. FEnd S.
Family T extends Cminor. FEnd T.

Inherit exit_env.

MetaData shift_exit.
Fixpoint shift_exit (e: self__Cminorgen_Sexit.exit_env) (n: nat) {struct e} : nat :=
  match e, n with
  | nil, _ => n
  | false :: e', _ => 1 + (shift_exit e' n)
  | true :: e', O => O
  | true :: e', m => 1 + (shift_exit e' (m - 1))
  end.
FEnd shift_exit.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sexit n := (fun arg => OK (T.Sexit (shift_exit (snd arg) n))).
FEnd transl_stmt with transl_lbl_stmt.
FEnd Cminorgen_Sexit.

Trait Cminorgen_Sloop extends Cminorgen.
Family S extends Csharpminor_Sloop. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sloop body := (fun arg => do ts <- transl_stmt body arg; OK (T.Sloop ts)).
FEnd transl_stmt with transl_lbl_stmt.
FEnd Cminorgen_Sloop.

Family Cminorgen extends 
    Cminorgen_Sexit,
    Cminorgen_Sloop,
    Cminorgen_Sblock.
FEnd Cminorgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Csharpminor.
FInductive stmt : Type :=
| Sbuiltin : option ident -> external_function -> list expr -> stmt.
FEnd Csharpminor.

From NFPOP Require Import Errors.
Local Open Scope error_monad_scope.

Family Cminor.
FInductive stmt : Type :=
| Sbuiltin : option ident -> external_function -> list expr -> stmt.
FEnd Cminor.

Family Cminorgen.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit transl_expr.

MetaData transl_exprlist.
Fixpoint transl_exprlist 
  (cenv: self__Cminorgen.transl_arg) (el: list self__Cminorgen.S.expr)
                     {struct el}: res (list self__Cminorgen.T.expr) :=
  match el with
  | nil =>
      OK nil
  | e1 :: e2 =>
      do te1 <- self__Cminorgen.transl_expr e1 cenv;
      do te2 <- transl_exprlist cenv e2;
      OK (te1 :: te2)
  end.
FEnd transl_exprlist.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sbuiltin optid ef el :=
   (fun cenv => 
      do tel <- transl_exprlist cenv el;
      OK (T.Sbuiltin optid ef tel)).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cminorgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Trait Csharpminor_Eaddrof extends Csharpminor.
FInductive expr : Type :=
| Eaddrof : ident -> expr. (* taking the address of a variable *)
FEnd Csharpminor_Eaddrof.

Trait Csharpminor_Eload extends Csharpminor.
FInductive expr : Type :=
| Eload : memory_chunk -> expr -> expr. (* memory read *)
FEnd Csharpminor_Eload.

Trait Csharpminor_Sstore extends Csharpminor.                                
FInductive stmt : Type :=
| Sstore : memory_chunk -> expr -> expr -> stmt.
FEnd Csharpminor_Sstore.

Family Csharpminor extends 
  Csharpminor_Sstore, 
  Csharpminor_Eload, 
  Csharpminor_Eaddrof.
FEnd Csharpminor.

Family Cminor.
FInductive expr : Type :=
| Eload : memory_chunk -> expr -> expr. (* memory read *)

FInductive stmt : Type :=
| Sstore : memory_chunk -> expr -> expr -> stmt.
FEnd Cminor.

Family Cminorgen.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit compilenv.

FDefinition var_addr : compilenv -> ident -> T.expr := fun cenv id =>
  match PTree.get id cenv with
  | Some ofs => T.Econst (T.Oaddrstack (Ptrofs.repr ofs))
  | None => T.Econst (T.Oaddrsymbol id Ptrofs.zero)
  end.

FRecursion transl_expr.
Case Eaddrof id := (fun arg => OK (var_addr (fst arg) id)).
Case Eload chunk e :=
  (fun arg => 
     do te <- transl_expr e arg;
     OK (T.Eload chunk te)).
FEnd transl_expr.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sstore chunk e1 e2 :=
(fun arg => 
   do te1 <- transl_expr e1 arg;
   do te2 <- transl_expr e2 arg;
   OK (T.Sstore chunk te1 te2)).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cminorgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Csharpminor.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt.
FEnd Csharpminor.

Family Cminor.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt
| Stailcall: signature -> expr -> list expr -> stmt.
FEnd Cminor.

Family Cminorgen.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion transl_stmt with transl_lbl_stmt.
Case Scall optid sig e el :=
  (fun arg => 
     do te <- transl_expr e arg;
     do tel <- transl_exprlist arg el;
   OK (T.Scall optid sig te tel)).
FEnd transl_stmt with transl_lbl_stmt.
FEnd Cminorgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait Csharpminor_Switch extends Csharpminor.
FInductive stmt : Type := 
| Sswitch: bool -> expr -> lbl_stmts -> stmt.
FEnd Csharpminor_Switch.

Family Csharpminor extends Csharpminor_Switch.
FEnd Csharpminor.

Trait Cminor_Switch extends Cminor.
FInductive stmt : Type := 
| Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt.
FEnd Cminor_Switch.

Family Cminor extends Cminor_Switch.
FEnd Cminor.

(*Trait Cminorgen_Switch extends Cminorgen.
Family S extends Csharpminor_Switch.*)

Family Cminorgen.
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

FRecursion transl_stmt with transl_lbl_stmt.
Case Sswitch long e ls :=
  (fun args => 
     let (tbl, dfl) := switch_table ls O in
     do te <- transl_expr e args;
     transl_lbl_stmt ls (fst args, (switch_env ls (snd args))) (T.Sswitch long te tbl dfl)).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cminorgen.

FEnd Comp_Switch.

Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin. 

Family Cminorgen.
Final Family S := Csharpminor.
Final Family T := Cminor.
FEnd Cminorgen.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
