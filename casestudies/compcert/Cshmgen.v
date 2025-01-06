(*only  Clight Cshminor*)
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

Family Clight.
FInductive expr : Type :=          
| Econst_int: int -> type -> expr(* integer literal *)
| Econst_float: float -> type -> expr(* double float literal *)
| Econst_single: float32 -> type -> expr(* single float literal *)
| Econst_long: int64 -> type -> expr(* long integer literal *)                                            
| Etempvar: ident -> type -> expr (* temporary variable *)          
| Esizeof: type -> type -> expr (* size of a type *)
| Ecast: expr -> type -> expr
| Ealignof: type -> type -> expr (* alignment of a type *)
| Eunop: Cop.unary_operation -> expr -> type -> expr (* unary operation *)
| Ebinop: Cop.binary_operation -> expr -> expr -> type -> expr. (* binary operation *)
       
FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect. 
Case Econst_int i ty := ty. 
Case Econst_float f ty := ty. 
Case Econst_single s ty := ty. 
Case Econst_long l ty := ty. 
Case Etempvar v ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.
Case Ecast e ty := ty.
Case Eunop op e ty := ty.
Case Ebinop op e0 e1 ty := ty.
FEnd typeof.
       
FDefinition label := ident.
FInductive stmt : Type :=                                        
| Sskip : stmt (* do nothing *)
| Sset : ident -> expr -> stmt (* assignment tempvar = rvalue *)
| Sseq : stmt -> stmt -> stmt (* sequence *)
| Sifthenelse : expr -> stmt -> stmt -> stmt (* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.
              
MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: self__Clight.stmt
}.
FEnd function.
              
FDefinition fundef := Ctypes.fundef function.
       
FDefinition type_of_function : function -> type := fun f => 
  Tfunction (type_of_params (self__Clight.fn_params f)) (self__Clight.fn_return f) (self__Clight.fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f => 
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

(* Semantics for Clight*)

MetaData genv.
Record genv := { genv_genv :> Genv.t self__Clight.fundef type; genv_cenv :> composite_env }.
FEnd genv.
FDefinition globalenv : program -> genv := fun p => 
  {| self__Clight.genv_genv := Genv.globalenv p; self__Clight.genv_cenv := p.(prog_comp_env) |}.


FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).
FDefinition temp_env := PTree.t val.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Econst_int: forall ge e le m i ty,
    eval_expr ge e le m (Econst_int i ty) (Vint i)
| eval_Econst_float: forall ge e le m f ty,
    eval_expr ge e le m (Econst_float f ty) (Vfloat f)
| eval_Econst_single: forall ge e le m f ty,
    eval_expr ge e le m (Econst_single f ty) (Vsingle f)
| eval_Econst_long: forall ge e le m i ty,
    eval_expr ge e le m (Econst_long i ty) (Vlong i)
| eval_Ecast: forall ge e le m a ty v1 v,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v ->
    eval_expr ge e le m (Ecast a ty) v
| eval_Etempvar: forall ge e le m id ty v,
    PTree.get id le = Some v ->
    eval_expr ge e le m (Etempvar id ty) v.

FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont. (* Kseq s2 k = after s1 in s1;s2 *)

FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.       
Case Kstop := Kstop.
Case Kseq s k := (Kseq s k).
FEnd call_cont.
            
FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.                   
Case Kstop := True.
Case Kseq s k := False.
FEnd is_call_cont.
            
FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect. 
Case Sskip := (fun lbl k => None). 
Case Sset id e := (fun lbl k => None).
Case Sseq s1 s2 := 
  (fun lbl k => 
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end). 
Case Sifthenelse a s1 s2 := 
 (fun lbl k => 
     match find_label s1 lbl k with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sreturn a := (fun lbl k => None).
Case Slabel lbl' s' :=  
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sgoto lbl' :=  (fun lbl k => None).
FEnd find_label.

MetaData state.
Inductive state: Type :=
  | State
      (f: self__Clight.function)
      (s: self__Clight.stmt)
      (k: self__Clight.cont)
      (e: self__Clight.env)
      (le: self__Clight.temp_env)
      (m: mem) : state
  | Callstate
      (fd: self__Clight.fundef)
      (args: list val)
      (k: self__Clight.cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: self__Clight.cont)
      (m: mem) : state.
FEnd state.

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (self__Clight.genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z)  := fun ge e => 
  List.map (block_of_binding ge) (PTree.elements e).

(* To be overriden in SimplExpr & Cshmgen *)
FOpaque Definition function_entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop := cheat.

FInductive step : genv -> state -> trace -> state -> Prop :=  
| step_skip_seq: forall ge f s k e le m,
  step ge (self__Clight.State f Sskip (Kseq s k) e le m)
    E0 (self__Clight.State f s k e le m)
| step_set: forall ge f id a k e le m v,
  eval_expr ge e le m a v ->
  step ge (self__Clight.State f (Sset id a) k e le m)
    E0 (self__Clight.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
  step ge (self__Clight.State f (Sseq s1 s2) k e le m)
    E0 (self__Clight.State f s1 (Kseq s2 k) e le m)
| step_ifthenelse: forall ge f a s1 s2 k e le m v1 b,
    eval_expr ge e le m a v1 ->
    Cop.bool_val v1 (typeof a) m = Some b ->
    step ge (self__Clight.State f (Sifthenelse a s1 s2) k e le m)
      E0 (self__Clight.State f (if b then s1 else s2) k e le m)      
| step_return_0: forall ge f k e le m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f (Sreturn None) k e le m)
      E0 (self__Clight.Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f a k e le m v v' m',
    eval_expr ge e le m a v ->
    Cop.sem_cast v (typeof a) f.(self__Clight.fn_return) m = Some v' ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f (Sreturn (Some a)) k e le m)
      E0 (self__Clight.Returnstate v' (call_cont k) m')      
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f Sskip k e le m)
      E0 (self__Clight.Returnstate Vundef k m')
| step_label: forall ge f lbl s k e le m,
  step ge (self__Clight.State f (Slabel lbl s) k e le m)
    E0 (self__Clight.State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
  find_label  f.(self__Clight.fn_body) lbl (call_cont k) = Some (s', k') ->
  step ge (self__Clight.State f (Sgoto lbl) k e le m)
    E0 (self__Clight.State f s' k' e le m)    
| step_internal_function: forall ge f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      step ge (self__Clight.Callstate (Internal f) vargs k m)
        E0 (self__Clight.State f f.(self__Clight.fn_body) k e le m1).

MetaData initial_state.
Inductive initial_state (p: self__Clight.program): self__Clight.state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      self__Clight.type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (self__Clight.Callstate f nil self__Clight.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Clight.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__Clight.Returnstate (Vint r) self__Clight.Kstop m) r.
FEnd final_state.
FEnd Clight.


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

(* Semantics for Cfam *)
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
                   
MetaData state.
Inductive state: Type :=
  | State:(* Execution within a function *)
      forall (f: self__Cfam.function)(* currently executing function *)
             (s: self__Cfam.stmt)(* statement under consideration *)
             (k: self__Cfam.cont)(* its continuation -- what to do next *)
             (sp: self__Cfam.fenv) (* current "function" environment: i.e stackspace, ... *)
             (e: self__Cfam.env)(* current local environment *)
             (m: mem),(* current memory state *)
      state
  | Callstate:(* Invocation of a function *)
      forall (f: self__Cfam.fundef)(* function to invoke *)
             (args: list val)(* arguments provided by caller *)
             (k: self__Cfam.cont)(* what to do next *)
             (m: mem),(* memory state *)
      state
  | Returnstate:(* Return from a function *)
      forall (v: val)(* Return value *)
             (k: self__Cfam.cont)(* what to do next *)
             (m: mem),(* memory state *)
      state.
FEnd state.
            
FRecursion call_cont about cont motive (fun (_ : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq := (fun s c call_cont_c => call_cont_c).             
FEnd call_cont.
               
FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
Case Kstop := True.                   
Case Kseq := (fun s c call_cont_c => False).
FEnd is_call_cont.              

FDefinition letenv := list val.
               
FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Evar: forall ge lenv e le m id v,
    PTree.get id le = Some v ->
    eval_expr ge e le m lenv (Evar id) v.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
    step ge (self__Cfam.State f Sskip (Kseq s k) e le m)
      E0 (self__Cfam.State f s k e le m)              
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->                       
    free_fenv m e f = Some m' ->
    step ge (self__Cfam.State f Sskip k e le m)
      E0 (self__Cfam.Returnstate Vundef k m')
| step_assign: forall lenv ge f id a k e le m v,
    eval_expr ge e le m lenv a v ->
    step ge (self__Cfam.State f (Sassign id a) k e le m)
      E0 (self__Cfam.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
    step ge (self__Cfam.State f (Sseq s1 s2) k e le m)
      E0 (self__Cfam.State f s1 (Kseq s2 k) e le m)              
| step_return_0: forall ge f k e le m m',                       
    free_fenv m e f = Some m' ->
    step ge (self__Cfam.State f (Sreturn None) k e le m)
      E0 (self__Cfam.Returnstate Vundef (call_cont k) m')    
| step_return_1: forall lenv ge f a k e le m v m',
    eval_expr ge e le m lenv a v ->
    free_fenv m e f = Some m' ->
    step ge (self__Cfam.State f (Sreturn (Some a)) k e le m)
      E0 (self__Cfam.Returnstate v (call_cont k) m')
| step_internal_function: forall ge f vargs k m m1 e le,                                          
    alloc_fenv empty_fenv m f e m1 ->
    init_env f vargs = le ->                        
     step ge (self__Cfam.Callstate (AST.Internal f) vargs k m)
       E0 (self__Cfam.State f (function_body f) k e le m1).
            
MetaData initial_state.
Inductive initial_state (p: self__Cfam.program): self__Cfam.state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__Cfam.funsig f = signature_main ->               
    initial_state p (self__Cfam.Callstate f nil self__Cfam.Kstop m0).
FEnd initial_state.
            
MetaData final_state.
Inductive final_state: self__Cfam.state -> int -> Prop :=
| final_state_intro: forall r m,
   final_state (self__Cfam.Returnstate (Vint r) self__Cfam.Kstop m) r.
FEnd final_state.

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

(* Semantics for Csharpminor*)
(* function stack environment *)       
FOverride Definition fenv := PTree.t (block * Z).
FOverride Definition empty_fenv := PTree.empty (block * Z).

FDefinition block_of_binding := fun (id_b_sz: ident * (block * Z)) => 
 match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

FDefinition blocks_of_env : fenv -> list (block * Z * Z) := fun e => 
  List.map block_of_binding (PTree.elements e).

FOverride Definition free_fenv := fun m e f => Mem.free_list m (blocks_of_env e).
   
MetaData alloc_variables.
Inductive alloc_variables: self__Csharpminor.fenv -> mem ->
               list (ident * Z) ->
               self__Csharpminor.fenv -> mem -> Prop :=
| alloc_variables_nil:
  forall e m,
    alloc_variables e m nil e m
| alloc_variables_cons:
  forall e m id sz vars m1 b1 m2 e2,
    Mem.alloc m 0 sz = (m1, b1) ->
    alloc_variables (PTree.set id (b1, sz) e) m1 vars e2 m2 ->
    alloc_variables e m ((id, sz) :: vars) e2 m2.
FEnd alloc_variables.
         
FOverride Definition alloc_fenv := fun e m f e' m' => 
  list_norepet (map fst f.(self__Csharpminor.fn_vars)) /\
  list_norepet f.(self__Csharpminor.fn_params) /\
  list_disjoint f.(self__Csharpminor.fn_params) f.(self__Csharpminor.fn_temps) /\
  alloc_variables self__Csharpminor.empty_fenv m (self__Csharpminor.fn_vars f) e m'.

FRecursion eval_constant about constant motive (fun (_ : constant) => option val) by _rect.
Case Ointconst := (fun n => Some (Vint n)). 
Case Ofloatconst := (fun n => Some (Vfloat n)).
Case Osingleconst := (fun n => Some (Vsingle n)).
Case Olongconst := (fun n => Some (Vlong n)).
FEnd eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Econst: forall ge lenv e le m cst v,
    eval_constant cst = Some v ->
    eval_expr ge e le m lenv (Econst cst) v.
                           
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Csharpminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Csharpminor.State f (if b then s1 else s2) k sp e m).
FEnd Csharpminor.


(* Clight -> Csharpminor *)
Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

FDefinition make_intconst := fun (n: int) => T.Econst (T.Ointconst n).
FDefinition make_longconst := fun (f: int64) => T.Econst (T.Olongconst f).
FDefinition make_floatconst := fun (f: float) => T.Econst (T.Ofloatconst f).
FDefinition make_singleconst := fun (f: float32) => T.Econst (T.Osingleconst f).
FDefinition make_ptrofsconst := fun (n: Z) =>
  if Archi.ptr64 then make_longconst (Int64.repr n) else make_intconst (Int.repr n).            

FDefinition make_singleoffloat := fun (e: T.expr) => T.Eunop Osingleoffloat e.
FDefinition make_floatofsingle := fun (e: T.expr) => T.Eunop Ofloatofsingle e.

FDefinition make_floatofint := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ofloatofint e
  | Unsigned => T.Eunop Ofloatofintu e
  end.

FDefinition make_singleofint := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Osingleofint e
  | Unsigned => T.Eunop Osingleofintu e
  end.

FDefinition make_intoffloat := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ointoffloat e
  | Unsigned => T.Eunop Ointuoffloat e
  end.

FDefinition make_intofsingle := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ointofsingle e
  | Unsigned => T.Eunop Ointuofsingle e
  end.

FDefinition make_longofint := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Olongofint e
  | Unsigned => T.Eunop Olongofintu e
  end.

FDefinition make_floatoflong := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Ofloatoflong e
  | Unsigned => T.Eunop Ofloatoflongu e
  end.

FDefinition make_singleoflong := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Osingleoflong e
  | Unsigned => T.Eunop Osingleoflongu e
  end.

FDefinition make_longoffloat := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Olongoffloat e
  | Unsigned => T.Eunop Olonguoffloat e
  end.

FDefinition make_longofsingle := fun (e: T.expr) (sg: signedness) =>
  match sg with
  | Signed => T.Eunop Olongofsingle e
  | Unsigned => T.Eunop Olonguofsingle e
  end.

FDefinition sizeof : composite_env -> type -> res Z := fun ce t => 
  if complete_type ce t
  then OK (Ctypes.sizeof ce t)
  else Error (msg "incomplete type").

FDefinition alignof : composite_env -> type -> res Z := fun ce t => 
  if complete_type ce t
  then OK (Ctypes.alignof ce t)
  else Error (msg "incomplete type").

FDefinition make_cmpu_ne_zero_helper := fun (op: binary_operation) (e: T.expr) =>
  match op with                                           
  | Ocmp c => e
  | Ocmpu c => e
  | Ocmpf c => e
  | Ocmpfs c => e
  | Ocmpl c => e
  | Ocmplu c => e
  | _ => T.Ebinop (Ocmpu Cne) e (make_intconst Int.zero)
  end.                  

FRecursion make_cmpu_ne_zero about T.expr motive (fun (_ : T.expr) => T.expr) by _rect.
Case Ebinop op e1 e2 := (make_cmpu_ne_zero_helper op (T.Ebinop op e1 e2)).
Case Evar v := (T.Ebinop (Ocmpu Cne) (T.Evar v) (make_intconst Int.zero)).
Case Eunop op e := (T.Ebinop (Ocmpu Cne) (T.Eunop op e) (make_intconst Int.zero)).
Case Econst c := (T.Ebinop (Ocmpu Cne) (T.Econst c) (make_intconst Int.zero)).
FEnd make_cmpu_ne_zero.

FDefinition make_cast_int := fun (e: T.expr) (sz: intsize) (si: signedness) =>
  match sz, si with
  | I8, Signed => T.Eunop Ocast8signed e
  | I8, Unsigned => T.Eunop Ocast8unsigned e
  | I16, Signed => T.Eunop Ocast16signed e
  | I16, Unsigned => T.Eunop Ocast16unsigned e
  | I32, _ => e
  | IBool, _ => make_cmpu_ne_zero e
  end.

FDefinition make_cast := fun (from to: type) (e: T.expr) =>
  match classify_cast from to with
  | cast_case_pointer => OK e
  | cast_case_i2i sz2 si2 => OK (make_cast_int e sz2 si2)
  | cast_case_f2f => OK e
  | cast_case_s2s => OK e
  | cast_case_f2s => OK (make_singleoffloat e)
  | cast_case_s2f => OK (make_floatofsingle e)
  | cast_case_i2f si1 => OK (make_floatofint e si1)
  | cast_case_i2s si1 => OK (make_singleofint e si1)
  | cast_case_f2i sz2 si2 => OK (make_cast_int (make_intoffloat e si2) sz2 si2)
  | cast_case_s2i sz2 si2 => OK (make_cast_int (make_intofsingle e si2) sz2 si2)
  | cast_case_l2l => OK e
  | cast_case_i2l si1 => OK (make_longofint e si1)
  | cast_case_l2i sz2 si2 => OK (make_cast_int (T.Eunop Ointoflong e) sz2 si2)
  | cast_case_l2f si1 => OK (make_floatoflong e si1)
  | cast_case_l2s si1 => OK (make_singleoflong e si1)
  | cast_case_f2l si2 => OK (make_longoffloat e si2)
  | cast_case_s2l si2 => OK (make_longofsingle e si2)
  | cast_case_i2bool => OK (make_cmpu_ne_zero e)
  | cast_case_f2bool => OK (T.Ebinop (Ocmpf Cne) e (make_floatconst Float.zero))
  | cast_case_s2bool => OK (T.Ebinop (Ocmpfs Cne) e (make_singleconst Float32.zero))
  | cast_case_l2bool => OK (T.Ebinop (Ocmplu Cne) e (make_longconst Int64.zero))
  | cast_case_struct id1 id2 => OK e
  | cast_case_union id1 id2 => OK e
  | cast_case_void => OK e
  | cast_case_default => Error (msg "Cshmgen.make_cast")
  end.

FDefinition make_boolean := fun (e: T.expr) (ty: type) =>
  match classify_bool ty with
  | bool_case_i => make_cmpu_ne_zero e
  | bool_case_f => T.Ebinop (Ocmpf Cne) e (make_floatconst Float.zero)
  | bool_case_s => T.Ebinop (Ocmpfs Cne) e (make_singleconst Float32.zero)
  | bool_case_l => T.Ebinop (Ocmplu Cne) e (make_longconst Int64.zero)
  | bool_default => e (* should not happen *)
  end.

FDefinition make_notbool := fun (e: T.expr) (ty: type) =>
  match classify_bool ty with
  | bool_case_i => OK (T.Ebinop (Ocmpu Ceq) e (make_intconst Int.zero))
  | bool_case_f => OK (T.Ebinop (Ocmpf Ceq) e (make_floatconst Float.zero))
  | bool_case_s => OK (T.Ebinop (Ocmpfs Ceq) e (make_singleconst Float32.zero))
  | bool_case_l => OK (T.Ebinop (Ocmplu Ceq) e (make_longconst Int64.zero))
  | bool_default => Error (msg "Cshmgen.make_notbool")
  end.

FDefinition make_neg := fun (e: T.expr) (ty: type) =>
  match classify_neg ty with
  | neg_case_i _ => OK (T.Eunop Onegint e)
  | neg_case_f => OK (T.Eunop Onegf e)
  | neg_case_s => OK (T.Eunop Onegfs e)
  | neg_case_l _ => OK (T.Eunop Onegl e)
  | neg_default => Error (msg "Cshmgen.make_neg")
  end.

FDefinition make_absfloat := fun (e: T.expr) (ty: type) =>
  match classify_neg ty with
  | neg_case_i sg => OK (T.Eunop Oabsf (make_floatofint e sg))
  | neg_case_f => OK (T.Eunop Oabsf e)
  | neg_case_s => OK (T.Eunop Oabsf (make_floatofsingle e))
  | neg_case_l sg => OK (T.Eunop Oabsf (make_floatoflong e sg))
  | neg_default => Error (msg "Cshmgen.make_absfloat")
  end.

FDefinition make_notint := fun (e: T.expr) (ty: type) =>
  match classify_notint ty with
  | notint_case_i _ => OK (T.Eunop Onotint e)
  | notint_case_l _ => OK (T.Eunop Onotl e)
  | notint_default => Error (msg "Cshmgen.make_notint")
  end.

FDefinition transl_unop := fun (op: Cop.unary_operation) (a: T.expr) (ta: type) =>
  match op with
  | Cop.Onotbool => make_notbool a ta
  | Cop.Onotint => make_notint a ta
  | Cop.Oneg => make_neg a ta
  | Cop.Oabsfloat => make_absfloat a ta
  end.
Local Open Scope error_monad_scope.
FDefinition make_binarith := fun (iop iopu fop sop lop lopu: binary_operation)
                         (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  let c := classify_binarith ty1 ty2 in
  let ty := binarith_type c in
  do e1' <- make_cast ty1 ty e1;
  do e2' <- make_cast ty2 ty e2;
  match c with
  | bin_case_i Signed => OK (T.Ebinop iop e1' e2')
  | bin_case_i Unsigned => OK (T.Ebinop iopu e1' e2')
  | bin_case_f => OK (T.Ebinop fop e1' e2')
  | bin_case_s => OK (T.Ebinop sop e1' e2')
  | bin_case_l Signed => OK (T.Ebinop lop e1' e2')
  | bin_case_l Unsigned => OK (T.Ebinop lopu e1' e2')
  | bin_default => Error (msg "Cshmgen.make_binarith")
  end.

FDefinition make_add_ptr_int := fun (ce: composite_env) (ty: type) (si: signedness) (e1 e2: T.expr) =>
  do sz <- sizeof ce ty;
  if Archi.ptr64 then
    let n := make_longconst (Int64.repr sz) in
    OK (T.Ebinop Oaddl e1 (T.Ebinop Omull n (make_longofint e2 si)))
  else
    let n := make_intconst (Int.repr sz) in
    OK (T.Ebinop Oadd e1 (T.Ebinop Omul n e2)).

FDefinition make_add_ptr_long := fun (ce: composite_env) (ty: type) (e1 e2: T.expr) =>
  do sz <- sizeof ce ty;
  if Archi.ptr64 then
    let n := make_longconst (Int64.repr sz) in
    OK (T.Ebinop Oaddl e1 (T.Ebinop Omull n e2))
  else
    let n := make_intconst (Int.repr sz) in
    OK (T.Ebinop Oadd e1 (T.Ebinop Omul n (T.Eunop Ointoflong e2))).

FDefinition make_add := fun (ce: composite_env) (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_add ty1 ty2 with
  | add_case_pi ty si => make_add_ptr_int ce ty si e1 e2
  | add_case_pl ty => make_add_ptr_long ce ty e1 e2
  | add_case_ip si ty => make_add_ptr_int ce ty si e2 e1
  | add_case_lp ty => make_add_ptr_long ce ty e2 e1
  | add_default => make_binarith Oadd Oadd Oaddf Oaddfs Oaddl Oaddl e1 ty1 e2 ty2
  end.

FDefinition make_sub := fun (ce: composite_env) (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_sub ty1 ty2 with
  | sub_case_pi ty si =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (T.Ebinop Osubl e1 (T.Ebinop Omull n (make_longofint e2 si)))
      else
        let n := make_intconst (Int.repr sz) in
        OK (T.Ebinop Osub e1 (T.Ebinop Omul n e2))
  | sub_case_pp ty =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (T.Ebinop Odivl (T.Ebinop Osubl e1 e2) n)
      else
        let n := make_intconst (Int.repr sz) in
        OK (T.Ebinop Odiv (T.Ebinop Osub e1 e2) n)
  | sub_case_pl ty =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (T.Ebinop Osubl e1 (T.Ebinop Omull n e2))
      else
        let n := make_intconst (Int.repr sz) in
        OK (T.Ebinop Osub e1 (T.Ebinop Omul n (T.Eunop Ointoflong e2)))
  | sub_default =>
      make_binarith Osub Osub Osubf Osubfs Osubl Osubl e1 ty1 e2 ty2
  end.

FDefinition make_mul := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith Omul Omul Omulf Omulfs Omull Omull e1 ty1 e2 ty2.

FDefinition make_div := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith Odiv Odivu Odivf Odivfs Odivl Odivlu e1 ty1 e2 ty2.

FDefinition make_binarith_int :=
  fun (iop iopu lop lopu: binary_operation)
      (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  let c := classify_binarith ty1 ty2 in
  let ty := binarith_type c in
  do e1' <- make_cast ty1 ty e1;
  do e2' <- make_cast ty2 ty e2;
  match c with
  | bin_case_i Signed => OK (T.Ebinop iop e1' e2')
  | bin_case_i Unsigned => OK (T.Ebinop iopu e1' e2')
  | bin_case_l Signed => OK (T.Ebinop lop e1' e2')
  | bin_case_l Unsigned => OK (T.Ebinop lopu e1' e2')
  | bin_case_f | bin_case_s | bin_default => Error (msg "Cshmgen.make_binarith_int")
  end.

FDefinition make_mod := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Omod Omodu Omodl Omodlu e1 ty1 e2 ty2.

FDefinition make_and := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Oand Oand Oandl Oandl e1 ty1 e2 ty2.

FDefinition make_or := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Oor Oor Oorl Oorl e1 ty1 e2 ty2.

FDefinition make_xor := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  make_binarith_int Oxor Oxor Oxorl Oxorl e1 ty1 e2 ty2.

FDefinition make_shl := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_shift ty1 ty2 with
  | shift_case_ii _ => OK (T.Ebinop Oshl e1 e2)
  | shift_case_li _ => OK (T.Ebinop Oshll e1 e2)
  | shift_case_il _ => OK (T.Ebinop Oshl e1 (T.Eunop Ointoflong e2))
  | shift_case_ll _ => OK (T.Ebinop Oshll e1 (T.Eunop Ointoflong e2))
  | shift_default => Error (msg "Cshmgen.make_shl")
  end.

FDefinition make_shr := fun (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_shift ty1 ty2 with
  | shift_case_ii Signed => OK (T.Ebinop Oshr e1 e2)
  | shift_case_ii Unsigned => OK (T.Ebinop Oshru e1 e2)
  | shift_case_li Signed => OK (T.Ebinop Oshrl e1 e2)
  | shift_case_li Unsigned => OK (T.Ebinop Oshrlu e1 e2)
  | shift_case_il Signed => OK (T.Ebinop Oshr e1 (T.Eunop Ointoflong e2))
  | shift_case_il Unsigned => OK (T.Ebinop Oshru e1 (T.Eunop Ointoflong e2))
  | shift_case_ll Signed => OK (T.Ebinop Oshrl e1 (T.Eunop Ointoflong e2))
  | shift_case_ll Unsigned => OK (T.Ebinop Oshrlu e1 (T.Eunop Ointoflong e2))
  | shift_default => Error (msg "Cshmgen.make_shr")
  end.

FDefinition make_cmp_ptr := fun (c: comparison) (e1 e2: T.expr) =>
  T.Ebinop (if Archi.ptr64 then Ocmplu c else Ocmpu c) e1 e2.

FDefinition make_cmp := fun (c: comparison) (e1: T.expr) (ty1: type) (e2: T.expr) (ty2: type) =>
  match classify_cmp ty1 ty2 with
  | cmp_case_pp => OK (make_cmp_ptr c e1 e2)
  | cmp_case_pi si =>
      OK (make_cmp_ptr c e1 (if Archi.ptr64 then make_longofint e2 si else e2))
  | cmp_case_ip si =>
      OK (make_cmp_ptr c (if Archi.ptr64 then make_longofint e1 si else e1) e2)
  | cmp_case_pl =>
      OK (make_cmp_ptr c e1 (if Archi.ptr64 then e2 else T.Eunop Ointoflong e2))
  | cmp_case_lp =>
      OK (make_cmp_ptr c (if Archi.ptr64 then e1 else T.Eunop Ointoflong e1) e2)
  | cmp_default =>
      make_binarith
        (Ocmp c) (Ocmpu c) (Ocmpf c) (Ocmpfs c) (Ocmpl c) (Ocmplu c)
        e1 ty1 e2 ty2
  end.

FDefinition transl_binop
  := fun (ce: composite_env)
         (op: Cop.binary_operation)
         (a: T.expr) (ta: type)
         (b: T.expr) (tb: type) =>
  match op with
  | Cop.Oadd => make_add ce a ta b tb
  | Cop.Osub => make_sub ce a ta b tb
  | Cop.Omul => make_mul a ta b tb
  | Cop.Odiv => make_div a ta b tb
  | Cop.Omod => make_mod a ta b tb
  | Cop.Oand => make_and a ta b tb
  | Cop.Oor => make_or a ta b tb
  | Cop.Oxor => make_xor a ta b tb
  | Cop.Oshl => make_shl a ta b tb
  | Cop.Oshr => make_shr a ta b tb
  | Cop.Oeq => make_cmp Ceq a ta b tb
  | Cop.One => make_cmp Cne a ta b tb
  | Cop.Olt => make_cmp Clt a ta b tb
  | Cop.Ogt => make_cmp Cgt a ta b tb
  | Cop.Ole => make_cmp Cle a ta b tb
  | Cop.Oge => make_cmp Cge a ta b tb
  end.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => composite_env -> res T.expr) by _rect.
Case Econst_int n ty := (fun ce => OK(make_intconst n)). 
Case Econst_float n ty := (fun ce => OK(make_floatconst n)).
Case Econst_single n ty := (fun ce => OK(make_singleconst n)).
Case Econst_long n ty := (fun ce => OK(make_longconst n)).
Case Etempvar id ty := (fun ce => OK(T.Evar id)). 
Case Esizeof ty' ty := (fun ce => do sz <- sizeof ce ty'; OK(make_ptrofsconst sz)).
Case Ealignof ty' ty := (fun ce => do al <- alignof ce ty'; OK(make_ptrofsconst al)).
Case Ecast b ty := (fun ce => do tb <- transl_expr b ce; make_cast (S.typeof b) ty tb).
Case Eunop op b ty :=
(fun ce =>
   do tb <- transl_expr b ce;
    transl_unop op tb (S.typeof b)).
Case Ebinop op b c ty :=
(fun ce =>
   do tb <- transl_expr b ce;
   do tc <- transl_expr c ce;
   transl_binop ce op tb (S.typeof b) tc (S.typeof c)).
FEnd transl_expr.
      
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => composite_env -> type -> nat -> nat -> res T.stmt)
     with transl_lbl_stmt about T.lbl_stmts motive (fun (_: S.lbl_stmts) => composite_env -> type -> nat -> nat -> res T.lbl_stmts) by _rect.
Case Sskip := (fun ce tyret nbrk ncnt => OK T.Sskip).   
Case Sset x b :=
(fun ce tyret nbrk ncnt => 
  do tb <- transl_expr b ce;
  OK (T.Sassign x tb)).
Case Sseq s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (T.Sseq ts1 ts2)).
Case Sifthenelse e s1 s2 :=
(fun ce tyret nbrk ncnt => 
  do te <- transl_expr e ce;
  do ts1 <- transl_stmt s1 ce tyret nbrk ncnt;
  do ts2 <- transl_stmt s2 ce tyret nbrk ncnt;
  OK (T.Sifthenelse (make_boolean te (S.typeof e)) ts1 ts2)).
Case Sreturn e :=
(fun ce tyret nbrk ncnt =>
   match e with
   | None => OK (T.Sreturn None)
   | Some e => 
       do te <- transl_expr e ce;
       do te' <- make_cast (S.typeof e) tyret te;
       OK (T.Sreturn (Some te'))
   end).
Case Slabel lbl s :=
(fun ce tyret nbrk ncnt => 
  do ts <- transl_stmt s ce tyret nbrk ncnt;
  OK (T.Slabel lbl ts)).
Case Sgoto lbl := (fun ce tyret nbrk ncnt => OK (T.Sgoto lbl)).

Case LSnil := (fun ce tyret nbrk ncnt => OK T.LSnil).
Case LScons n s sl' :=
  (fun ce tyret nbrk ncnt =>
      do ts <- transl_stmt s ce tyret nbrk ncnt;
      do tsl' <- transl_lbl_stmt sl' ce tyret nbrk ncnt;
      OK (T.LScons n ts tsl')).
FEnd transl_stmt with transl_lbl_stmt.

(* Translation of functions *)
FDefinition transl_var := fun (ce: composite_env) (v: ident * type) =>
  do sz <- sizeof ce (snd v); OK (fst v, sz).
      
FDefinition signature_of_function := fun (f: S.function) =>
  {| sig_args := map typ_of_type (map snd (S.fn_params f));
    sig_res  := rettype_of_type (S.fn_return f);
    sig_cc   := S.fn_callconv f |}.
      
FDefinition transl_function : composite_env -> S.function -> res T.function :=
  fun (ce: composite_env) (f: S.function)  =>
  do tbody <- transl_stmt (S.fn_body f) ce (S.fn_return f) 1%nat 0%nat;
  do tvars <- mmap (transl_var ce) (S.fn_vars f);
  OK (T.mkfunction
        (signature_of_function f)
        (map fst (S.fn_params f))
        tvars
        (map fst (S.fn_temps f))
        tbody).      

FDefinition transl_fundef : composite_env -> ident -> S.fundef -> res T.fundef :=
  fun (ce: composite_env) (id: ident) (f: S.fundef) =>
  match f with
  | Internal g =>
      do tg <- transl_function ce g; OK(AST.Internal tg)
  | External ef args res cconv =>
      if signature_eq (ef_sig ef) (signature_of_type args res cconv)
      then OK(AST.External ef)
      else Error(msg "Cshmgen.transl_fundef: wrong external signature")
  end.

FDefinition transl_globvar := fun (id: ident) (ty: type) => OK tt.

FDefinition transl_program : S.program -> res T.program := fun p => 
  transform_partial_program2 (transl_fundef p.(prog_comp_env)) transl_globvar p.

(* Cshmgen specifications *)
(* correctness of translation *)

MetaData match_fundef.
Inductive match_fundef (p: self__Cshmgen.S.program) : self__Cshmgen.S.fundef -> self__Cshmgen.T.fundef -> Prop :=
  | match_fundef_internal: forall f tf,
      self__Cshmgen.transl_function p.(prog_comp_env) f = OK tf ->
      match_fundef p (Ctypes.Internal f) (AST.Internal tf)
  | match_fundef_external: forall ef args res cc,
      ef_sig ef = signature_of_type args res cc ->
      match_fundef p (Ctypes.External ef args res cc) (AST.External ef).
FEnd match_fundef.

FDefinition match_varinfo : type -> unit -> Prop := fun v tv => True.

FDefinition match_prog : S.program -> T.program -> Prop := fun p tp =>
  match_program_gen match_fundef match_varinfo p p tp.

FInductive match_transl
  : self__Cshmgen.T.stmt -> self__Cshmgen.T.cont ->
    self__Cshmgen.T.stmt -> self__Cshmgen.T.cont -> Prop :=
| match_transl_0: forall ts tk,
    match_transl ts tk ts tk.

(* | match_transl_1: forall ts tk,
    match_transl (self__Cshmgen.T.Sblock ts) tk ts
      (self__Cshmgen.T.Kblock tk).*)

FInductive match_cont : composite_env -> type -> nat -> nat -> S.cont -> T.cont -> Prop :=
| match_Kstop: forall ce tyret nbrk ncnt,
    match_cont ce tyret nbrk ncnt S.Kstop T.Kstop      
| match_Kseq: forall ce tyret nbrk ncnt s k ts tk,
    transl_stmt s ce tyret nbrk ncnt = OK ts ->
    match_cont ce tyret nbrk ncnt k tk ->
    match_cont ce tyret nbrk ncnt (S.Kseq s k) (T.Kseq ts tk).
               
(*| match_Kloop1: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
    transl_stmt s1 tyret 1%nat 0%nat = OK ts1 ->
    transl_stmt s2 tyret 0%nat (S ncnt) = OK ts2 ->
    match_cont tyret nbrk ncnt k tk ->
    match_cont tyret 1%nat 0%nat
               (Clight.Sem.Kloop1 s1 s2 k)
               (Csharpminor.Sem.Kblock
                  (Csharpminor.Sem.Kseq ts2
                     (Csharpminor.Sem.Kseq
                        (Csharpminor.Sloop
                           (Csharpminor.Sseq
                              (Csharpminor.Sblock ts1) ts2))
                        (Csharpminor.Sem.Kblock tk))))
| match_Kloop2: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
    transl_stmt s1 tyret 1%nat 0%nat = OK ts1 ->
    transl_stmt s2 tyret 0%nat (S ncnt) = OK ts2 ->
    match_cont tyret nbrk ncnt k tk ->
    match_cont tyret 0%nat (S ncnt)
               (Clight.Sem.Kloop2 s1 s2 k)
               (Csharpminor.Sem.Kseq
                  (Csharpminor.Sloop
                     (Csharpminor.Sseq
                        (Csharpminor.Sblock ts1) ts2))
                  (Csharpminor.Sem.Kblock tk)).*)

(*
Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := globalenv prog.
Let tge := Genv.globalenv tprog.
*)

MetaData match_env.
Compute (_!_).
Check (_!_).
Compute self__Cshmgen.S.env.
Compute self__Cshmgen.T.fenv.
Compute Z.
Compute res.
(*res
defined in: lib/Errors.v

_!_
te is PTree.t (block * Z)
 *)

Record match_env
  (prog: S.program)
  (e: S.env) (te: T.fenv) : Prop :=
 mk_match_env {
   me_local:
     forall id b ty,
       e!id = Some (b, ty) ->
       let ge := S.globalenv prog in 
       te!id = Some (b, Ctypes.sizeof (S.genv_cenv ge) ty);
   me_local_inv:
     forall id b sz,
     te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
}.
FEnd match_env.


MetaData match_states.
Inductive match_states : self__Cshmgen.S.state -> self__Cshmgen.T.state -> Prop :=
| match_state:
    forall f nbrk ncnt s k e le m tf ts tk te ts' tk' (cu : self__Cshmgen.S.program)
        (* (LINK: linkorder cu prog)*)
        (TRF: self__Cshmgen.transl_function cu.(prog_comp_env) f = OK tf)
        (TR: self__Cshmgen.transl_stmt s cu.(prog_comp_env) (self__Cshmgen.S.fn_return f) nbrk ncnt = OK ts)
        (MTR: self__Cshmgen.match_transl ts tk ts' tk')
        (MENV: self__Cshmgen.match_env cu e te)
        (MK: self__Cshmgen.match_cont cu.(prog_comp_env) (self__Cshmgen.S.fn_return f) nbrk ncnt k tk),
    match_states (self__Cshmgen.S.State f s k e le m)
      (self__Cshmgen.T.State tf ts' tk' te le m)      
| match_callstate:
    forall fd args k m tfd tk targs tres cconv cu ce
        (* (LINK: linkorder cu prog)*)
        (TR: self__Cshmgen.match_fundef cu fd tfd)
        (MK: self__Cshmgen.match_cont ce tres 0%nat 0%nat k tk)
        (ISCC: self__Cshmgen.S.is_call_cont k)
        (TY: self__Cshmgen.S.type_of_fundef fd = Tfunction targs tres cconv),
    match_states (self__Cshmgen.S.Callstate fd args k m)
      (self__Cshmgen.T.Callstate tfd args tk m)      
| match_returnstate:
    forall res tres k m tk ce
        (MK: self__Cshmgen.match_cont ce tres 0%nat 0%nat k tk),
        (* (WT: wt_val res tres),*) (* Need Ctyping.v? *)
    match_states (self__Cshmgen.S.Returnstate res k m)
      (self__Cshmgen.T.Returnstate res tk m).
FEnd match_states.

(* Work Here *)
(* use closing fact for inversion*)
Closing Fact match_transl_0_inv :
  forall ts tk ts' tk',
    match_transl ts tk ts' tk' ->
    ts' = ts /\ tk' = tk
    by plain {intros until tmp; intros H; inv H; eauto}.

FInduction transl_step about S.step
  motive (fun ge S1 t S2 (_ : S.step ge S1 t S2) => 
            forall prog tprog tge, match_prog prog tprog ->
            S.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall T1, match_states S1 T1 -> 
  exists T2, plus T.step tge T1 t T2 /\ match_states S2 T2).
FProof.

(* skip *)
- intros. revert H2. intro MST.
  inv MST. fsimpl in TR. monadInv TR.
  (* inv MTR. *)

            
  assert (ts' = self__Cshmgen.T.Sskip /\ tk' = tk).
  { apply cheat. } destruct H0. subst.
  (* inv MK. *)
  
  apply self__Cshmgen.match_Kseq in MK.
  (* apply self__Cshmgen.match_transl_0 in MTR. inv MTR.
  apply cheat.*)
  (*inv MTR. inv MK.*)
  econstructor; split.
  apply plus_one. fconstructor;eauto.
  + econstructor.
  econstructor; eauto. constructor.

(* set *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* seq *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* if then else *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* return None *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* return Some *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* a second skip? *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* label *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* goto *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.
(* internal function *)
- intros. revert H2. intro MST.
  inv MST. apply cheat.  
Qed. FEnd transl_step.
                
FLemma transl_initial_states:
  forall S' prog tprog, S.initial_state prog S' -> transl_program prog = OK tprog ->
  exists R, T.initial_state tprog R /\ match_states S' R.
FProofLemma. apply cheat. Qed. CloseFLemma.          
          
FLemma transl_final_states:
  forall S' R r,
  match_states S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma. apply cheat. Qed. CloseFLemma.

FEnd Cshmgen.

FEnd Base.

Trait Comp_Loops extends Base.

Trait Clight_Sloop extends Clight.
FInductive stmt : Type := 
  | Sloop: stmt -> stmt -> stmt (* infinite loop *)
  | Sbreak : stmt (* break statement *)
  | Scontinue : stmt. (* continue statement *) 
FEnd Clight_Sloop.

Family Clight extends Clight_Sloop.
FEnd Clight.

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

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Trait Cshmgen_Sloop extends Cshmgen.
Family S extends Clight_Sloop. FEnd S.

FRecursion transl_stmt with transl_lbl_stmt.

Case Sloop s1 s2 :=
(fun ce tyret nbrk ncnt =>
  do ts1 <- transl_stmt s1 ce tyret 1%nat 0%nat;
  do ts2 <- transl_stmt s2 ce tyret 0%nat ((1 + ncnt)%nat);
  OK (T.Sblock (T.Sloop (T.Sseq (T.Sblock ts1) ts2)))).
Case Sbreak := (fun ce tyret nbrk ncnt => OK (T.Sexit nbrk)).
Case Scontinue := (fun ce tyret nbrk ncnt => OK (T.Sexit ncnt)).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cshmgen_Sloop.

Family Cshmgen extends Cshmgen_Sloop.
FEnd Cshmgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Clight.
FInductive stmt : Type :=
| Sbuiltin: option ident -> external_function -> list type -> list expr -> stmt. (* builtin invocation *)
FEnd Clight.

Family Csharpminor.
FInductive stmt : Type :=
| Sbuiltin : option ident -> external_function -> list expr -> stmt.
FEnd Csharpminor.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Family Cshmgen.

Inherit transl_expr.

MetaData transl_arglist.
Fixpoint transl_arglist (ce: composite_env) (al: list self__Cshmgen.S.expr) (tyl: list type)
                         {struct al}: res (list self__Cshmgen.T.expr) :=
  match al, tyl with
  | nil, nil => OK nil
  | a1 :: a2, ty1 :: ty2 =>
      do ta1 <- self__Cshmgen.transl_expr a1 ce;
      do ta1' <- self__Cshmgen.make_cast (self__Cshmgen.S.typeof a1) ty1 ta1;
      do ta2 <- transl_arglist ce a2 ty2;
      OK (ta1' :: ta2)
  | a1 :: a2, nil =>
      do ta1 <- self__Cshmgen.transl_expr a1 ce;
      do ta1' <- self__Cshmgen.make_cast (self__Cshmgen.S.typeof a1) (default_argument_conversion (self__Cshmgen.S.typeof a1)) ta1;
      do ta2 <- transl_arglist ce a2 nil;
      OK (ta1' :: ta2)
  | _, _ =>
      Error(msg "Cshmgen.transl_arglist: arity mismatch")
  end.
FEnd transl_arglist.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sbuiltin x ef tyargs bl :=
(fun ce tyret nbrk ncnt =>
  do tbl <- transl_arglist ce bl tyargs;
  OK(T.Sbuiltin x ef tbl)).
FEnd transl_stmt with transl_lbl_stmt.
FEnd Cshmgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Trait Clight_Evar extends Clight.
FInductive expr : Type :=
| Evar: ident -> type -> expr. (* variable *)

FRecursion typeof.
Case Evar i t := t.
FEnd typeof.
FEnd Clight_Evar.

Trait Clight_Ederef extends Clight.
FInductive expr : Type :=
| Ederef: expr -> type -> expr. (* pointer dereference (unary *)

FRecursion typeof.
Case Ederef i t := t.
FEnd typeof.
FEnd Clight_Ederef.

Trait Clight_Eaddrof extends Clight.
FInductive expr : Type :=
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Eaddrof e t := t.
FEnd typeof.
FEnd Clight_Eaddrof.

Trait Clight_Sassign extends Clight.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)
FEnd Clight_Sassign.

Family Clight extends 
  Clight_Sassign, 
  Clight_Eaddrof,
  Clight_Ederef,
  Clight_Evar.
FEnd Clight.

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

Trait Cshmgen_Sassign extends Cshmgen.
Family S extends Clight_Sassign. FEnd S.

Inherit alignof.
From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

FDefinition make_store_bitfield : intsize -> signedness -> Z -> Z -> T.expr -> T.expr -> res T.stmt := 
fun sz signedness pos width addr val => 
  if zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz) then
    let amount := first_bit sz pos width in
    let mask := Int.shl (Int.repr (two_p width - 1)) (Int.repr amount) in
    let e1 := T.Eload (chunk_for_carrier sz) addr in
    let e2 := T.Ebinop Oshl val (make_intconst (Int.repr amount)) in
    let e3 := T.Ebinop Oor (T.Ebinop Oand e2 (make_intconst mask))
                         (T.Ebinop Oand e1 (make_intconst (Int.not mask))) in
    OK (T.Sstore (chunk_for_carrier sz) addr e3)
  else
    Error(msg "Cshmgen.make_store_bitfield").

FDefinition make_memcpy : composite_env -> T.expr -> T.expr -> type -> res T.stmt := 
  fun ce dst src ty => 
  do sz <- sizeof ce ty;
  OK (T.Sbuiltin None (EF_memcpy sz (Ctypes.alignof_blockcopy ce ty))
                    (dst :: src :: nil)).

FDefinition make_store := fun (ce: composite_env) (addr: T.expr) (ty: type) (bf: bitfield) (rhs: T.expr) =>
  match bf with
  | Full =>
      match access_mode ty with
      | By_value chunk => OK (T.Sstore chunk addr rhs)
      | By_copy => make_memcpy ce addr rhs ty
      | _ => Error (msg "Cshmgen.make_store")
      end
  | Bits sz sg pos width =>
      make_store_bitfield sz sg pos width addr rhs
  end.

FRecursion make_cmpu_ne_zero.
Case Eaddrof v := (T.Ebinop (Ocmpu Cne) (T.Eaddrof v) (make_intconst Int.zero)).
Case Eload ck e := (T.Ebinop (Ocmpu Cne) (T.Eload ck e) (make_intconst Int.zero)).
FEnd make_cmpu_ne_zero.

FOpaque Definition transl_lvalue :
  composite_env -> S.expr -> res (T.expr * bitfield) := cheat.

FRecursion transl_stmt with transl_lbl_stmt.
Case Sassign b c :=
(fun ce tyret nbrk ncnt => 
   do (tb, bf) <- transl_lvalue ce b;
   do tc <- transl_expr c ce;
   do tc' <- make_cast (S.typeof c) (S.typeof b) tc;
   make_store ce tb (S.typeof b) bf tc').
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cshmgen_Sassign.

Trait Cshmgen_Eaddrof extends Cshmgen.
Family S extends Clight_Eaddrof. FEnd S.

FRecursion make_cmpu_ne_zero.
Case Eaddrof v := (T.Ebinop (Ocmpu Cne) (T.Eaddrof v) (make_intconst Int.zero)).
Case Eload ck e := (T.Ebinop (Ocmpu Cne) (T.Eload ck e) (make_intconst Int.zero)).
FEnd make_cmpu_ne_zero.

FOpaque Definition transl_lvalue :
  composite_env -> S.expr -> res (T.expr * bitfield) := cheat.

FRecursion transl_expr.
Case Eaddrof b c :=
(fun ce => 
   do (tb, bf) <- transl_lvalue ce b;
   match bf with
   | Full => OK tb
   | Bits _ _ _ _ => Error (msg "Cshmgen.transl_expr: addrof bitfield")
   end).
FEnd transl_expr.

FEnd Cshmgen_Eaddrof.

Trait Cshmgen_Ederef_Evar extends Cshmgen.
Family S extends Clight_Ederef, Clight_Evar. FEnd S.

Inherit alignof.

FDefinition make_extract_bitfield 
 : intsize -> signedness -> Z -> Z -> T.expr -> res T.expr := 
fun sz sg pos width addr =>   
  if zle 0 pos && zlt 0 width && zle (pos + width) (bitsize_carrier sz) then
    let amount1 := Int.repr (Int.zwordsize - first_bit sz pos width - width) in
    let amount2 := Int.repr (Int.zwordsize - width) in
    let e1 := T.Eload (chunk_for_carrier sz) addr in
    let e2 := T.Ebinop Oshl e1 (make_intconst amount1) in
    let e3 := T.Ebinop (if intsize_eq sz IBool
                      || signedness_eq sg Unsigned then Oshru else Oshr)
                     e2 (make_intconst amount2) in
    OK e3
  else
    Error(msg "Cshmgen.extract_bitfield").

FDefinition make_load := fun (addr: T.expr) (ty_res: type) (bf: bitfield) =>
  match bf with
  | Full =>
      match access_mode ty_res with
      | By_value chunk => OK (T.Eload chunk addr)
      | By_reference => OK addr
      | By_copy => OK addr
      | By_nothing => Error (msg "Cshmgen.make_load")
      end
  | Bits sz sg pos width =>
      make_extract_bitfield sz sg pos width addr
  end.

FRecursion make_cmpu_ne_zero.
Case Eaddrof v := (T.Ebinop (Ocmpu Cne) (T.Eaddrof v) (make_intconst Int.zero)).
Case Eload ck e := (T.Ebinop (Ocmpu Cne) (T.Eload ck e) (make_intconst Int.zero)).
FEnd make_cmpu_ne_zero.

FRecursion transl_expr.
Case Ederef b ty :=
(fun ce => 
  do tb <- transl_expr b ce;
      make_load tb ty Full).
Case Evar id ty :=
   (fun ce => make_load (T.Eaddrof id) ty Full).
FEnd transl_expr.

FEnd Cshmgen_Ederef_Evar.

Family Cshmgen extends 
  Cshmgen_Ederef_Evar, 
  Cshmgen_Eaddrof, 
  Cshmgen_Sassign.
FEnd Cshmgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Clight.
FInductive expr : Type :=
| Efield: expr -> ident -> type -> expr. (* access to a member of a struct or union *)

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FEnd Clight.

Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.
From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

(*Inherit alignof.

Inherit make_extract_bitfield.
FDefinition make_extract_bitfield 
 : intsize -> signedness -> Z -> Z -> T.expr -> res T.expr := 
fun sz sg pos width addr => cheat. (*we need the Eload expr *)

FDefinition make_load := fun (addr: T.expr) (ty_res: type) (bf: bitfield) =>
  match bf with
  | Full =>
      cheat
  | Bits sz sg pos width =>
      make_extract_bitfield sz sg pos width addr
  end.*)

Inherit make_load.

FDefinition make_field_access
  := fun (ce: composite_env) (ty: type) (f: ident) (a: T.expr) =>
  do (ofs, bf) <-
    match ty with
    | Tstruct id _ =>
        match ce!id with
        | None => Error (MSG "Undefined struct " :: CTX id :: nil)
        | Some co => field_offset ce f (co_members co)
        end
    | Tunion id _ =>
        match ce!id with
        | None => Error (MSG "Undefined union " :: CTX id :: nil)
        | Some co => union_field_offset ce f (co_members co)
        end
    | _ =>
        Error(msg "Cshmgen.make_field_access")
    end;
  let a' :=
    if Archi.ptr64
    then T.Ebinop Oaddl a (make_longconst (Int64.repr ofs))
    else T.Ebinop Oadd a (make_intconst (Int.repr ofs)) in
  OK (a', bf).

FRecursion transl_expr.
Case Efield b i ty := 
  (fun ce =>
     do tb <- transl_expr b ce;
     do (addr, bf) <- make_field_access ce (S.typeof b) i tb;
    make_load addr ty bf).
FEnd transl_expr.

FEnd Cshmgen.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Clight.
FInductive stmt : Type :=
| Scall: option ident -> expr -> list expr -> stmt. (* function call *)

FEnd Clight.

Family Csharpminor.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt.
FEnd Csharpminor.

Family Cshmgen.
Family S extends Clight. FEnd S.
Family T extends Csharpminor. FEnd T.

FDefinition make_normalization := fun (t: type) (a: T.expr) =>
  match t with
  | Tint IBool _ _ => T.Eunop Ocast8unsigned a
  | Tint I8 Signed _ => T.Eunop Ocast8signed a
  | Tint I8 Unsigned _ => T.Eunop Ocast8unsigned a
  | Tint I16 Signed _ => T.Eunop Ocast16signed a
  | Tint I16 Unsigned _ => T.Eunop Ocast16unsigned a
  | _ => a
  end.

From Rocqet Require Import Conventions1.
FDefinition return_value_needs_normalization := fun (_: rettype) => false.

FDefinition make_funcall :=
  fun (x: option ident) (tres: type) (sg: signature)
      (fn: T.expr) (args: list T.expr) =>
  match x, return_value_needs_normalization sg.(sig_res) with
  | Some id, true =>
      T.Sseq (T.Scall x sg fn args)
             (T.Sassign id (make_normalization tres (T.Evar id)))
  | _, _ =>
      T.Scall x sg fn args
  end.

MetaData typlist_of_arglist.
Fixpoint typlist_of_arglist (al: list self__Cshmgen.S.expr) (tyl: list type)
                            {struct al}: list AST.typ :=
  match al, tyl with
  | nil, _ => nil
  | a1 :: a2, ty1 :: ty2 =>
      typ_of_type ty1 :: typlist_of_arglist a2 ty2
  | a1 :: a2, nil =>
      typ_of_type (default_argument_conversion (self__Cshmgen.S.typeof a1)) :: typlist_of_arglist a2 nil
  end.
FEnd typlist_of_arglist.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.
FRecursion transl_stmt with transl_lbl_stmt.
Case Scall x b cl := 
  (fun ce tyret nbrk ncnt =>
     match classify_fun (S.typeof b) with
      | fun_case_f args res cconv =>
          do tb <- transl_expr b ce;
          do tcl <- transl_arglist ce cl args; 
          let sg := {| sig_args := typlist_of_arglist cl args;
                       sig_res  := rettype_of_type res;
                       sig_cc   := cconv |} in
          OK (make_funcall x res sg tb tcl)
      | _ => Error(msg "Cshmgen.transl_stmt(call)")
      end).
FEnd transl_stmt with transl_lbl_stmt.

FEnd Cshmgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait Clight_Switch extends Clight.
FInductive stmt : Type := 
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)
FEnd Clight_Switch.

Family Clight extends Clight_Switch.
FEnd Clight.

Trait Csharpminor_Switch extends Csharpminor.
FInductive stmt : Type := 
| Sswitch: bool -> expr -> lbl_stmts -> stmt.
FEnd Csharpminor_Switch.

Family Csharpminor extends Csharpminor_Switch.
FEnd Csharpminor.

Trait Cshmgen_Switch extends Cshmgen.
Family S extends Clight_Switch. FEnd S.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.
FRecursion transl_stmt with transl_lbl_stmt.
Case Sswitch a sl := 
(fun ce tyret nbrk ncnt =>
   do ta <- transl_expr a ce;
   do tsl <- transl_lbl_stmt sl ce tyret 0%nat ((1 + ncnt)%nat);
    match classify_switch (S.typeof a) with
    | switch_case_i => OK (T.Sblock (T.Sswitch false ta tsl))
    | switch_case_l => OK (T.Sblock (T.Sswitch true ta tsl ))
    | switch_default => Error(msg "Cshmgen.transl_stmt(switch)")
    end).
FEnd transl_stmt with transl_lbl_stmt.
FEnd Cshmgen_Switch.

Family Cshmgen extends Cshmgen_Switch.
FEnd Cshmgen.

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

Family Cshmgen.
Final Family S := Clight.
Final Family T := Csharpminor.
FEnd Cshmgen.

FEnd Comp.

Require Extraction.
Cd "extraction".

Separate Extraction Comp.Cshmgen.

Extraction Library AST.
Recursive Library AST. 


Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
