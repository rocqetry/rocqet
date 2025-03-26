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

Require Import CfamBase.

Trait Base.

Family Cminor.

FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant (* long integer constant *)
| Oaddrsymbol: ident -> ptrofs -> constant (* address of the symbol plus the offset *)
| Oaddrstack: ptrofs -> constant. (* stack pointer plus the given offset *)

FInductive expr : Type :=
| Evar : ident -> expr (* reading a temporary variable *)  
| Econst : constant -> expr (* constants *)
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt  
| Sifthenelse: expr -> stmt -> stmt -> stmt.
        
MetaData fn.
   Record fn : Type := mkfunction {
      fn_sig: signature;
      fn_params: list ident;
      fn_vars: list ident;
      fn_stackspace: Z;
      fn_body: self__Cminor.stmt
   }.
FEnd fn.

FDefinition function := fn.
FDefinition function_body := self__Cminor.fn_body.
FDefinition function_locals := self__Cminor.fn_vars.
FDefinition function_params := self__Cminor.fn_params.
FDefinition function_sig := self__Cminor.fn_sig.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

FDefinition genv := Genv.t fundef unit.

(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FDefinition fenv := block.
FDefinition empty_fenv : fenv := cheat.
   
FDefinition free_fenv : mem -> fenv -> function -> option mem := fun m sp f =>
  Mem.free m sp 0 f.(self__Cminor.fn_stackspace).
          
FDefinition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := fun sp m f sp' m' => 
  Mem.alloc m 0 f.(self__Cminor.fn_stackspace) = (m', sp).

FDefinition env := PTree.t val.            
FDefinition empty_env : env := PTree.empty val.

MetaData set_params.
Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
 match il, vl with
 | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
 | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
 | _, _ => PTree.empty val
 end.
FEnd set_params.

MetaData set_locals.
Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.
FEnd set_locals.
       
FDefinition init_env : function -> list val -> env := fun f vargs => 
  set_locals (function_locals f) (set_params vargs (function_params f)).            

FRecursion eval_constant about constant motive (fun (_ : constant) => genv -> fenv -> option val) by _rect.
Case Ointconst n := (fun ge sp => Some (Vint n)). 
Case Ofloatconst n := (fun ge sp => Some (Vfloat n)).
Case Osingleconst n := (fun ge sp => Some (Vsingle n)).
Case Olongconst n := (fun ge sp => Some (Vlong n)).
Case Oaddrstack ofs := (fun ge sp => Some (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs)).
Case Oaddrsymbol s ofs := (fun ge sp => Some (Genv.symbol_address ge s ofs)).
FEnd eval_constant.


MetaData create_undef_temps.
Fixpoint create_undef_temps (temps: list ident) : env :=
 match temps with
 | nil => PTree.empty val
 | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
end.
FEnd create_undef_temps.

MetaData bind_parameters.
Fixpoint bind_parameters (formals: list ident) (args: list val)
             (le: env) : option env :=
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
             (e: env)(* current local environment *)
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
    eval_expr ge e le m lenv (Evar id) v
| eval_Econst: forall ge lenv e le m cst v,
      eval_constant cst ge e = Some v ->
      eval_expr ge e le m lenv (Econst cst) v
| eval_Eunop: forall ge lenv e le m op a1 v1 v,
      eval_expr ge e le m lenv a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr ge e le m lenv (Eunop op a1) v
| eval_Ebinop: forall ge lenv e le m op a1 a2 v1 v2 v,
      eval_expr ge e le m lenv a1 v1 ->
      eval_expr ge e le m lenv a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr ge e le m lenv (Ebinop op a1 a2) v.              

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sifthenelse a s1 s2 := 
(fun lbl k => 
   match find_label s1 lbl k with
   | Some sk => Some sk
   | None => find_label s2 lbl k
   end).
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
        E0 (State f s' k' e le m)  
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Cminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Cminor.State f (if b then s1 else s2) k sp e m)
| step_internal_function: forall ge f vargs k m m' sp e,
      Val.has_argtype_list vargs (self__Cminor.fn_sig f).(sig_args) ->
      Mem.alloc m 0 (self__Cminor.fn_stackspace f) = (m', sp) ->
      set_locals (self__Cminor.fn_vars f) (set_params vargs (self__Cminor.fn_params f)) = e ->
      step ge (Callstate (AST.Internal f) vargs k m)
        E0 (State f (self__Cminor.fn_body f) k sp e m').

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->               
    initial_state p (Callstate f nil Kstop m0).
FEnd initial_state.
            
MetaData final_state.
Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
   final_state (Returnstate (Vint r) Kstop m) r.
FEnd final_state.

FEnd Cminor.

FEnd Base.

Trait Comp_Loops extends Base.

Family Cminor.
FInductive stmt : Type :=
| Sloop: stmt -> stmt
| Sblock: stmt -> stmt
| Sexit: nat -> stmt.

FInductive cont: Type :=
| Kblock: cont -> cont.  

FRecursion call_cont.
Case Kblock k := (call_cont k).
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
FEnd Cminor.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

From Rocqet Require Import Switch.

Family Cminor.

FInductive stmt : Type :=
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f islong a cases default k sp e m v n lenv,
   eval_expr ge sp e m lenv a v ->
   switch_argument islong v n ->
   step ge (State f (Sswitch islong a cases default) k sp e m)
     E0 (State f (Sexit (switch_target n default cases)) k sp e m).  

FEnd Cminor.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base.

Family Cminor.

FInductive stmt : Type :=
| Sbuiltin : option ident -> external_function -> list expr -> stmt.

Inherit eval_expr.

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> fenv -> env -> mem -> letenv -> list expr -> list val -> Prop :=
  | eval_Enil: forall ge lenv e le m,
      eval_exprlist ge le e m lenv nil nil
  | eval_Econs: forall ge le e m lenv a1 al v1 vl,
      eval_expr ge le e m lenv a1 v1 -> eval_exprlist ge le e m lenv al vl ->
      eval_exprlist ge le e m lenv (a1 :: al) (v1 :: vl).
FEnd eval_exprlist.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f lenv optid ef bl k e le m vargs t vres m',
   eval_exprlist ge e le m lenv bl vargs ->
   external_call ef ge vargs m t vres m' ->
   step ge (State f (Sbuiltin optid ef bl) k e le m)
     t (State f Sskip k e (set_optvar optid vres le) m').

FEnd Cminor.

FEnd Comp_Builtin.

Trait Comp_External extends Base.
Family Cminor.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_external_function: forall ge ef vargs k m t vres m',
   external_call ef (Genv.to_senv ge) vargs m t vres m' ->
   step ge (Callstate (AST.External ef) vargs k m)
      t (Returnstate vres k m').

FEnd Cminor.
FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Family Cminor.

FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt
| Stailcall: signature -> expr -> list expr -> stmt.

FInductive cont: Type :=
  | Kcall: option ident -> function -> env -> fenv -> cont -> cont.

FRecursion call_cont.
Case Kcall a b c d e := (Kcall a b c d e).
FEnd call_cont.
               
FRecursion is_call_cont.
Case Kcall a b c d e := True.
FEnd is_call_cont.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_return: forall ge v optid f sp e k m,
      step ge (Returnstate v (Kcall optid f e sp k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m)  
| step_call: forall ge lenv f optid sig a bl k e le m vf vargs fd,
      eval_expr ge le e m lenv a vf ->
      eval_exprlist ge le e m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step ge (State f (Scall optid sig a bl) k le e m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)
| step_tailcall: forall ge lenv f optid sig a bl k e le m m' vf vargs fd,
      eval_expr ge le e m lenv a vf ->
      eval_exprlist ge le e m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m le 0 (self__Cminor.fn_stackspace f) = Some m' ->
      step ge (State f (Scall optid sig a bl) k le e m)
        E0 (Callstate fd vargs (call_cont k) m'). 
FEnd Cminor.

FEnd Comp_Call.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Cminor.
FInductive expr : Type :=
 | Eload : memory_chunk -> expr -> expr.

FInductive stmt : Type :=                                                        
| Sstore : memory_chunk -> expr -> expr -> stmt.

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eload: forall ge sp e m chunk addr vaddr v lenv,
   eval_expr ge sp e m lenv addr vaddr ->
   Mem.loadv chunk m vaddr = Some v ->
   eval_expr ge sp e m lenv (Eload chunk addr) v.
           
FRecursion find_label.  
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_store: forall ge f chunk addr a k e le m vaddr v m' lenv,
      eval_expr ge e le m lenv addr vaddr ->
      eval_expr ge e le m lenv a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step ge (State f (Sstore chunk addr a) k e le m)
        E0 (State f Sskip k e le m').
FEnd Cminor.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Cminor.
FEnd Cminor.

FEnd Comp_Field.

Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  Comp_External,
  Comp_Builtin.

FEnd Comp.


Print Comp.Cminor.
