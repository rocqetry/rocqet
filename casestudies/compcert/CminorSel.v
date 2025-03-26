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

(* Require Import CfamBase.*)

Trait Base.

Family CminorSel. 

FInductive expr : Type :=
| Evar : ident -> expr (* reading a temporary variable *)  
| Econdition : condexpr -> expr -> expr -> expr
| Eop : operation -> exprlist -> expr
| Elet : expr -> expr -> expr
| Eletvar : nat -> expr
with exprlist : Type :=
| Enil: exprlist
| Econs: expr -> exprlist -> exprlist
with condexpr : Type :=
| CEcond : condition -> exprlist -> condexpr
| CEcondition : condexpr -> condexpr -> condexpr -> condexpr
| CElet: expr -> condexpr -> condexpr.

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt  
| Sifthenelse: condexpr -> stmt -> stmt -> stmt.

MetaData fn binds fn_sig, fn_params, fn_vars, fn_stackspace, fn_body.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: stmt
}.
FEnd fn.

FDefinition function := fn.
FDefinition function_body := fn_body.
FDefinition function_locals := fn_vars.
FDefinition function_params := fn_params.
FDefinition function_sig := fn_sig.

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
FOpaque Definition empty_fenv : fenv := cheat.

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

FDefinition free_fenv : mem -> fenv -> function -> option mem := fun m sp f => Mem.free m sp 0 (fn_stackspace f).
FDefinition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := fun sp m f sp' m' => Mem.alloc m 0 (fn_stackspace f) = (m', sp').

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

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Evar: forall ge lenv e le m id v,
    PTree.get id le = Some v ->
    eval_expr ge e le m lenv (Evar id) v  
| eval_Eop: forall ge sp e m le op al vl v,
    eval_exprlist ge sp e m le al vl ->
    eval_operation ge (Vptr sp Ptrofs.zero) op vl m = Some v ->
    eval_expr ge sp e m le (Eop op al) v              
| eval_Econdition: forall ge sp e m le a b c va v,
    eval_condexpr ge sp e m le a va ->
    eval_expr ge sp e m le (if va then b else c) v ->
    eval_expr ge sp e m le (Econdition a b c) v
| eval_Elet: forall ge sp e m le a b v1 v2,
    eval_expr ge sp e m le a v1 ->
    eval_expr ge sp e m (v1 :: le) b v2 ->
    eval_expr ge sp e m le (Elet a b) v2
| eval_Eletvar: forall ge sp e m le n v,
    nth_error le n = Some v ->
    eval_expr ge sp e m le (Eletvar n) v
with eval_exprlist: genv -> fenv -> env -> mem -> letenv -> exprlist -> list val -> Prop :=
| eval_Enil: forall ge sp e m le,
    eval_exprlist ge sp e m le Enil nil
| eval_Econs: forall ge sp e m le a1 al v1 vl,
    eval_expr ge sp e m le a1 v1 -> eval_exprlist ge sp e m le al vl ->
    eval_exprlist ge sp e m le (Econs a1 al) (v1 :: vl)                  
with eval_condexpr: genv -> fenv -> env -> mem -> letenv -> condexpr -> bool -> Prop :=
| eval_CEcond: forall ge sp e m le cond al vl vb,
    eval_exprlist ge sp e m le al vl ->
    eval_condition cond vl m = Some vb ->
    eval_condexpr ge sp e m le (CEcond cond al) vb
| eval_CEcondition: forall ge sp e m le a b c va v,
    eval_condexpr ge sp e m le a va ->
    eval_condexpr ge sp e m le (if va then b else c) v ->
    eval_condexpr ge sp e m le (CEcondition a b c) v
| eval_CElet: forall ge sp e m le a b v1 v2,
    eval_expr ge sp e m le a v1 ->
    eval_condexpr ge sp e m (v1 :: le) b v2 ->
    eval_condexpr ge sp e m le (CElet a b) v2.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sifthenelse c s1 s2 :=
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
| step_ifthenelse: forall ge f c s1 s2 k sp e m b,
   eval_condexpr ge sp e m nil c b ->
   step ge (State f (Sifthenelse c s1 s2) k sp e m)
     E0 (State f (if b then s1 else s2) k sp e m)
| step_internal_function: forall ge f vargs k m m' sp e,
      Val.has_argtype_list vargs (self__CminorSel.fn_sig f).(sig_args) ->
      Mem.alloc m 0 (self__CminorSel.fn_stackspace f) = (m', sp) ->
      set_locals (self__CminorSel.fn_vars f) (set_params vargs (self__CminorSel.fn_params f)) = e ->
      step ge (Callstate (AST.Internal f) vargs k m)
        E0 (State f (self__CminorSel.fn_body f) k sp e m').


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

FEnd CminorSel.

FEnd Base.

Trait Comp_Loops extends Base.

Family CminorSel.
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
FEnd CminorSel.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

Family CminorSel.

Inherit expr.

MetaData exitexpr.
Inductive exitexpr : Type :=
  | XEexit: nat -> exitexpr
  | XEjumptable: expr -> list nat -> exitexpr
  | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
  | XElet: expr -> exitexpr -> exitexpr.
FEnd exitexpr.

FInductive stmt : Type := 
  | Sswitch: exitexpr -> stmt.

Inherit eval_expr.

MetaData eval_exitexpr.
Inductive eval_exitexpr: genv -> fenv -> env -> mem -> letenv -> exitexpr -> nat -> Prop :=
  | eval_XEexit: forall ge sp e m le x,
      eval_exitexpr ge sp e m le (XEexit x) x
  | eval_XEjumptable: forall ge sp e m le a tbl n x,
      eval_expr ge sp e m le a (Vint n) ->
      list_nth_z tbl (Int.unsigned n) = Some x ->
      eval_exitexpr ge sp e m le (XEjumptable a tbl) x
  | eval_XEcondition: forall ge sp e m le a b c va x,
      eval_condexpr ge sp e m le a va ->
      eval_exitexpr ge sp e m le (if va then b else c) x ->
      eval_exitexpr ge sp e m le (XEcondition a b c) x
  | eval_XElet: forall ge sp e m le a b v x,
      eval_expr ge sp e m le a v ->
      eval_exitexpr ge sp e m (v :: le) b x ->
      eval_exitexpr ge sp e m le (XElet a b) x.
FEnd eval_exitexpr.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f a k sp e m n,
   eval_exitexpr ge sp e m nil a n ->
   step ge (State f (Sswitch a) k sp e m)
     E0 (State f (Sexit n) k sp e m).

FEnd CminorSel.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base.

Family CminorSel.
FInductive expr : Type :=
| Ebuiltin : external_function -> exprlist -> expr.

FInductive stmt : Type :=
| Sbuiltin : builtin_res ident -> external_function -> list (builtin_arg expr) -> stmt.

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Ebuiltin: forall ge sp e m le ef al vl v,
   eval_exprlist ge sp e m le al vl ->
   external_call ef ge vl m E0 v m ->
   eval_expr ge sp e m le (Ebuiltin ef al) v.

MetaData eval_builtin_arg.
Inductive eval_builtin_arg: genv -> fenv -> env -> mem -> builtin_arg expr -> val -> Prop :=
  | eval_BA: forall ge sp e m a v,
      eval_expr ge sp e m nil a v ->
      eval_builtin_arg ge sp e m (BA a) v
  | eval_BA_int: forall ge sp e m n,
      eval_builtin_arg ge sp e m (BA_int n) (Vint n)
  | eval_BA_long: forall ge sp e m n,
      eval_builtin_arg ge sp e m (BA_long n) (Vlong n)
  | eval_BA_float: forall ge sp e m n,
      eval_builtin_arg ge sp e m (BA_float n) (Vfloat n)
  | eval_BA_single: forall ge sp e m n,
      eval_builtin_arg ge sp e m (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall ge sp e m chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs) = Some v ->
      eval_builtin_arg ge sp e m (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ge sp e m ofs,
      eval_builtin_arg ge sp e m (BA_addrstack ofs) (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs)
  | eval_BA_loadglobal: forall ge sp e m chunk id ofs v,
      Mem.loadv chunk m (Genv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg ge sp e m (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall ge sp e m id ofs,
      eval_builtin_arg ge sp e m (BA_addrglobal id ofs) (Genv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall ge sp e m a1 a2 v1 v2,
      eval_expr ge sp e m nil a1 v1 -> eval_expr ge sp e m nil a2 v2 ->
      eval_builtin_arg ge sp e m (BA_splitlong (BA a1) (BA a2)) (Val.longofwords v1 v2)
  | eval_BA_addptr: forall ge sp e m a1 v1 a2 v2,
      eval_builtin_arg ge sp e m a1 v1 -> eval_builtin_arg ge sp e m a2 v2 ->
      eval_builtin_arg ge sp e m (BA_addptr a1 a2)
                       (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).
FEnd eval_builtin_arg.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FDefinition set_builtin_res := fun (res: builtin_res ident) (v: val) (e: env) =>
  match res with
  | BR id => PTree.set id v e
  | _ => e
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f res ef al k sp e m vl t v m',
   list_forall2 (eval_builtin_arg ge sp e m) al vl ->
   external_call ef ge vl m t v m' ->
   step ge (State f (Sbuiltin res ef al) k sp e m)
      t (State f Sskip k sp (set_builtin_res res v e) m').
FEnd CminorSel.

FEnd Comp_Builtin.

Trait Comp_External extends Base.

Family CminorSel.
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_external_function: forall ge ef vargs k m t vres m',
   external_call ef (Genv.to_senv ge) vargs m t vres m' ->
   step ge (Callstate (AST.External ef) vargs k m)
      t (Returnstate vres k m').
FEnd CminorSel.

FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Family CminorSel.
FInductive expr : Type :=
| Eexternal : ident -> signature -> exprlist -> expr.

FInductive stmt : Type :=
| Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
  | Stailcall: signature -> expr + ident -> exprlist -> stmt.

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

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eexternal: forall ge sp e m le id sg al b ef vl v,
   Genv.find_symbol ge id = Some b ->
   Genv.find_funct_ptr ge b = Some (AST.External ef) ->
   ef_sig ef = sg ->
   eval_exprlist ge sp e m le al vl ->
   external_call ef ge vl m E0 v m ->
   eval_expr ge sp e m le (Eexternal id sg al) v.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.
  
MetaData eval_expr_or_symbol.
Inductive eval_expr_or_symbol: genv -> fenv -> env -> mem -> letenv -> expr + ident -> val -> Prop :=
  | eval_eos_e: forall ge sp e m le a v,
      eval_expr ge sp e m le a v ->
      eval_expr_or_symbol ge sp e m le (inl _ a) v
  | eval_eos_s: forall ge sp e m le id b,
      Genv.find_symbol ge id = Some b ->
      eval_expr_or_symbol ge sp e m le (inr _ id) (Vptr b Ptrofs.zero).
FEnd eval_expr_or_symbol.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_return: forall ge v optid f sp e k m,
      step ge (Returnstate v (Kcall optid f e sp k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m)  
| step_call: forall ge f optid sig a bl k sp e m vf vargs fd,
   eval_expr_or_symbol ge sp e m nil a vf ->
   eval_exprlist ge sp e m nil bl vargs ->
   Genv.find_funct ge vf = Some fd ->
   funsig fd = sig ->
   step ge (State f (Scall optid sig a bl) k sp e m)
     E0 (Callstate fd vargs (Kcall optid f e sp k) m)    
| step_tailcall: forall ge f sig a bl k sp e m vf vargs fd m',
   eval_expr_or_symbol ge sp e m nil a vf ->
   eval_exprlist ge sp e m nil bl vargs ->
   Genv.find_funct ge vf = Some fd ->
   funsig fd = sig ->
   Mem.free m sp 0 (fn_stackspace f) = Some m' ->
   step ge (State f (Stailcall sig a bl) k sp e m)
     E0 (Callstate fd vargs (call_cont k) m').
FEnd CminorSel.

FEnd Comp_Call.

Trait Comp_Heap extends Base, Comp_Builtin.

Family CminorSel.
FInductive expr : Type :=
| Eload : memory_chunk -> addressing -> exprlist -> expr.

FInductive stmt : Type :=                                                        
| Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt.

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eload: forall ge sp e m le chunk addr al vl vaddr v,
   eval_exprlist ge sp e m le al vl ->
   eval_addressing ge (Vptr sp Ptrofs.zero) addr vl = Some vaddr ->
   Mem.loadv chunk m vaddr = Some v ->
   eval_expr ge sp e m le (Eload chunk addr al) v.
           
FRecursion find_label.  
Case Sstore chunk addr al a := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_store: forall ge f chunk addr al b k sp e m vl v vaddr m',
   eval_exprlist ge sp e m nil al vl ->
   eval_expr ge sp e m nil b v ->
   eval_addressing ge (Vptr sp Ptrofs.zero) addr vl = Some vaddr ->
   Mem.storev chunk m vaddr v = Some m' ->
   step ge (State f (Sstore chunk addr al b) k sp e m)
     E0 (State f Sskip k sp e m').

FEnd CminorSel.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family CminorSel.
FEnd CminorSel.

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
