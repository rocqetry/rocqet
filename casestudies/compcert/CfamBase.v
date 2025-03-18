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

FDefinition genv := Genv.t fundef unit.
       
(* Function env/stack space *)
FOpaque Definition fenv : Type := cheat.
FOpaque Definition empty_fenv : fenv := cheat.
       
FDefinition env := PTree.t val.            
FDefinition empty_env : env := PTree.empty val.
       
MetaData set_params.
Fixpoint set_params (vl: list val) (il: list ident) {struct il} : self__Cfam.env :=
 match il, vl with
 | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
 | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
 | _, _ => PTree.empty val
 end.
FEnd set_params.

MetaData set_locals.
Fixpoint set_locals (il: list ident) (e: self__Cfam.env) {struct il} : self__Cfam.env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.
FEnd set_locals.
       
FDefinition init_env : function -> list val -> env := fun f vargs => 
  set_locals (function_locals f) (set_params vargs (function_params f)).            

(* Semantics for allocation of variables and binding of parameters at function entry. *)
FOpaque Definition free_fenv : mem -> fenv -> function -> option mem := cheat.            
FOpaque Definition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := cheat.
       
MetaData create_undef_temps.
Fixpoint create_undef_temps (temps: list ident) : self__Cfam.env :=
 match temps with
 | nil => PTree.empty val
 | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
end.
FEnd create_undef_temps.

MetaData bind_parameters.
Fixpoint bind_parameters (formals: list ident) (args: list val)
             (le: self__Cfam.env) : option self__Cfam.env :=
 match formals, args with
 | nil, nil => Some le
 | id :: xl, v :: vl => bind_parameters xl vl (PTree.set id v le)
 | _, _ => None
 end.
FEnd bind_parameters.
            
FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.
                   
MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State:(* Execution within a function *)
      forall (f: function)(* currently executing function *)
             (s: stmt)(* statement under consideration *)
             (k:  cont)(* its continuation -- what to do next *)
             (sp: fenv) (* current "function" environment: i.e stackspace, ... *)
             (e: self__Cfam.env)(* current local environment *)
             (m: mem),(* current memory state *)
      state
  | Callstate:(* Invocation of a function *)
      forall (f: fundef)(* function to invoke *)
             (args: list val)(* arguments provided by caller *)
             (k: cont)(* what to do next *)
             (m: mem),(* memory state *)
      state
  | Returnstate:(* Return from a function *)
      forall (v: val)(* Return value *)
             (k: cont)(* what to do next *)
             (m: mem),(* memory state *)
      state.
FEnd state.
            
FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq s c := (call_cont c).             
FEnd call_cont.
               
FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
Case Kstop := True.                   
Case Kseq s c := False.
FEnd is_call_cont.              

FDefinition letenv := list val.
               
FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Evar: forall ge lenv e le m id v,
    PTree.get id le = Some v ->
    eval_expr ge e le m lenv (Evar id) v.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
    step ge (State f Sskip (Kseq s k) e le m)
      E0 (State f s k e le m)              
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->                       
    free_fenv m e f = Some m' ->
    step ge (State f Sskip k e le m)
      E0 (Returnstate Vundef k m')
| step_assign: forall lenv ge f id a k e le m v,
    eval_expr ge e le m lenv a v ->
    step ge (State f (Sassign id a) k e le m)
      E0 (State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
    step ge (State f (Sseq s1 s2) k e le m)
      E0 (State f s1 (Kseq s2 k) e le m)              
| step_return_0: forall ge f k e le m m',                       
    free_fenv m e f = Some m' ->
    step ge (State f (Sreturn None) k e le m)
      E0 (Returnstate Vundef (call_cont k) m')    
| step_return_1: forall lenv ge f a k e le m v m',
    eval_expr ge e le m lenv a v ->
    free_fenv m e f = Some m' ->
    step ge (State f (Sreturn (Some a)) k e le m)
      E0 (Returnstate v (call_cont k) m')
| step_label: forall ge f lbl s k e le m,
      step ge (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
      find_label (function_body f) lbl (call_cont k) = Some(s', k') ->
      step ge (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m).

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__Cfam.funsig f = signature_main ->               
    initial_state p (Callstate f nil Kstop m0).
FEnd initial_state.
            
MetaData final_state.
Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
   final_state (Returnstate (Vint r) Kstop m) r.
FEnd final_state.

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

Definition eval_unop (op: unary_operation) (arg: val) : option val :=
  match op with
  | Ocast8unsigned => Some (Val.zero_ext 8 arg)
  | Ocast8signed => Some (Val.sign_ext 8 arg)
  | Ocast16unsigned => Some (Val.zero_ext 16 arg)
  | Ocast16signed => Some (Val.sign_ext 16 arg)
  | Onegint => Some (Val.negint arg)
  | Onotint => Some (Val.notint arg)
  | Onegf => Some (Val.negf arg)
  | Oabsf => Some (Val.absf arg)
  | Onegfs => Some (Val.negfs arg)
  | Oabsfs => Some (Val.absfs arg)
  | Osingleoffloat => Some (Val.singleoffloat arg)
  | Ofloatofsingle => Some (Val.floatofsingle arg)
  | Ointoffloat => Val.intoffloat arg
  | Ointuoffloat => Val.intuoffloat arg
  | Ofloatofint => Val.floatofint arg
  | Ofloatofintu => Val.floatofintu arg
  | Ointofsingle => Val.intofsingle arg
  | Ointuofsingle => Val.intuofsingle arg
  | Osingleofint => Val.singleofint arg
  | Osingleofintu => Val.singleofintu arg
  | Onegl => Some (Val.negl arg)
  | Onotl => Some (Val.notl arg)
  | Ointoflong => Some (Val.loword arg)
  | Olongofint => Some (Val.longofint arg)
  | Olongofintu => Some (Val.longofintu arg)
  | Olongoffloat => Val.longoffloat arg
  | Olonguoffloat => Val.longuoffloat arg
  | Ofloatoflong => Val.floatoflong arg
  | Ofloatoflongu => Val.floatoflongu arg
  | Olongofsingle => Val.longofsingle arg
  | Olonguofsingle => Val.longuofsingle arg
  | Osingleoflong => Val.singleoflong arg
  | Osingleoflongu => Val.singleoflongu arg
  end.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val) (m: mem): option val :=
  match op with
  | Oadd => Some (Val.add arg1 arg2)
  | Osub => Some (Val.sub arg1 arg2)
  | Omul => Some (Val.mul arg1 arg2)
  | Odiv => Val.divs arg1 arg2
  | Odivu => Val.divu arg1 arg2
  | Omod => Val.mods arg1 arg2
  | Omodu => Val.modu arg1 arg2
  | Oand => Some (Val.and arg1 arg2)
  | Oor => Some (Val.or arg1 arg2)
  | Oxor => Some (Val.xor arg1 arg2)
  | Oshl => Some (Val.shl arg1 arg2)
  | Oshr => Some (Val.shr arg1 arg2)
  | Oshru => Some (Val.shru arg1 arg2)
  | Oaddf => Some (Val.addf arg1 arg2)
  | Osubf => Some (Val.subf arg1 arg2)
  | Omulf => Some (Val.mulf arg1 arg2)
  | Odivf => Some (Val.divf arg1 arg2)
  | Oaddfs => Some (Val.addfs arg1 arg2)
  | Osubfs => Some (Val.subfs arg1 arg2)
  | Omulfs => Some (Val.mulfs arg1 arg2)
  | Odivfs => Some (Val.divfs arg1 arg2)
  | Oaddl => Some (Val.addl arg1 arg2)
  | Osubl => Some (Val.subl arg1 arg2)
  | Omull => Some (Val.mull arg1 arg2)
  | Odivl => Val.divls arg1 arg2
  | Odivlu => Val.divlu arg1 arg2
  | Omodl => Val.modls arg1 arg2
  | Omodlu => Val.modlu arg1 arg2
  | Oandl => Some (Val.andl arg1 arg2)
  | Oorl => Some (Val.orl arg1 arg2)
  | Oxorl => Some (Val.xorl arg1 arg2)
  | Oshll => Some (Val.shll arg1 arg2)
  | Oshrl => Some (Val.shrl arg1 arg2)
  | Oshrlu => Some (Val.shrlu arg1 arg2)
  | Ocmp c => Some (Val.cmp c arg1 arg2)
  | Ocmpu c => Some (Val.cmpu (Mem.valid_pointer m) c arg1 arg2)
  | Ocmpf c => Some (Val.cmpf c arg1 arg2)
  | Ocmpfs c => Some (Val.cmpfs c arg1 arg2)
  | Ocmpl c => Val.cmpl c arg1 arg2
  | Ocmplu c => Val.cmplu (Mem.valid_pointer m) c arg1 arg2
  end.

FEnd Cfam.

FEnd Base.


Trait Comp_Loops extends Base.

Family Cfam.

FInductive stmt : Type :=
| Sloop: stmt -> stmt
| Sblock: stmt -> stmt
| Sexit: nat -> stmt.

FInductive cont: Type :=
| Kblock: cont -> cont.  

FRecursion call_cont.
Case Kblock k := (Kblock k).
FEnd call_cont.
               
FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label.
Case Sloop s1 :=
   (fun lbl k => find_label s1 lbl (Kseq (Sloop s1) k)).
Case Sblock s1 := 
  (fun lbl k => find_label s1 lbl (Kblock k)).
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_block: forall ge f k sp e m,
      step ge (State f Sskip (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)  
| step_loop: forall ge f s k sp e m,
      step ge (State f (Sloop s) k sp e m)
        E0 (State f s (Kseq (Sloop s) k) sp e m)
| step_block: forall ge f s k e le m,
      step ge (State f (Sblock s) k e le m)
        E0 (State f s (Kblock k) e le m)
| step_exit_seq: forall ge f n s k e le m,
      step ge (State f (Sexit n) (Kseq s k) e le m)
        E0 (State f (Sexit n) k e le m)
| step_exit_block_0: forall ge f k e le m,
      step ge (State f (Sexit O) (Kblock k) e le m)
        E0 (State f Sskip k e le m)
| step_exit_block_S: forall ge f n k e le m,
      step ge (State f (Sexit (S n)) (Kblock k) e le m)
        E0 (State f (Sexit n) k e le m).

FEnd Cfam.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

Family Cfam.
FEnd Cfam.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base.

Family Cfam.

FEnd Cfam.

FEnd Comp_Builtin.

Trait Comp_External extends Base.

Family Cfam.
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_external_function: forall ge ef vargs k m t vres m',
   external_call ef (Genv.to_senv ge) vargs m t vres m' ->
   step ge (Callstate (AST.External ef) vargs k m)
      t (Returnstate vres k m').
FEnd Cfam.

FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin.

Family Cfam.

FInductive cont: Type :=
  | Kcall: option ident -> function -> env -> fenv -> cont -> cont.

FRecursion call_cont.
Case Kcall a b c d e := (Kcall a b c d e).
FEnd call_cont.
               
FRecursion is_call_cont.
Case Kcall a b c d e := True.
FEnd is_call_cont.

FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_return: forall ge v optid f sp e k m,
      step ge (Returnstate v (Kcall optid f e sp k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).
FEnd Cfam.

FEnd Comp_Call.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Cfam.
FEnd Cfam.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Cfam.
FEnd Cfam.

FEnd Comp_Field.


(*Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  Comp_External,
  Comp_Builtin.

FEnd Comp. *)
