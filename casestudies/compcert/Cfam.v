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
| Sifthenelse: expr -> stmt -> stmt -> stmt.
       
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
(* ------------------------------------------------ *)
(*             Semantics for Csharpminor            *)
(* ------------------------------------------------ *)
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

FRecursion find_label.
Case Sifthenelse a s1 s2 := 
(fun lbl k => 
   match find_label s1 lbl k with
   | Some sk => Some sk
   | None => find_label s2 lbl k
   end).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Csharpminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Csharpminor.State f (if b then s1 else s2) k sp e m).
(*| step_internal_function: forall ge f vargs k m m1 e le,
   Val.has_argtype_list vargs (self__Csharpminor.fn_sig f).(sig_args) ->
   list_norepet (map fst (self__Csharpminor.fn_vars f)) ->
   list_norepet (self__Csharpminor.fn_params f) ->
   list_disjoint (self__Csharpminor.fn_params f) (self__Csharpminor.fn_temps f) ->
   alloc_variables empty_fenv m (self__Csharpminor.fn_vars f) e m1 ->
   bind_parameters (self__Csharpminor.fn_params f) vargs (create_undef_temps (self__Csharpminor.fn_temps f)) = Some le ->
   step ge (Callstate (AST.Internal f) vargs k m)
     E0 (State f (self__Csharpminor.fn_body f) k e le m1). *)

FEnd Csharpminor.

Family Cminor extends Cfam.

FInductive constant : Type :=
| Ointconst: int -> constant (* integer constant *)
| Ofloatconst: float -> constant (* double-precision floating-point constant *)
| Osingleconst: float32 -> constant (* single-precision floating-point constant *)
| Olongconst: int64 -> constant (* long integer constant *)
| Oaddrsymbol: ident -> ptrofs -> constant (* address of the symbol plus the offset *)
| Oaddrstack: ptrofs -> constant. (* stack pointer plus the given offset *)

FInductive expr : Type :=
| Econst : constant -> expr (* constants *)
| Eunop : unary_operation -> expr -> expr(* unary operation *)
| Ebinop : binary_operation -> expr -> expr -> expr. (* binary operation *)

FInductive stmt : Type :=
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

FOverride Definition function := fn.
FOverride Definition function_body := self__Cminor.fn_body.
FOverride Definition function_locals := self__Cminor.fn_vars.
FOverride Definition function_params := self__Cminor.fn_params.
FOverride Definition function_sig := self__Cminor.fn_sig.

(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FOverride Definition fenv := block.
   
FOverride Definition free_fenv := fun m sp f =>
  Mem.free m sp 0 f.(self__Cminor.fn_stackspace).
          
FOverride Definition alloc_fenv := fun sp m f sp' m' => 
   Mem.alloc m 0 f.(self__Cminor.fn_stackspace) = (m', sp).

FRecursion eval_constant about constant motive (fun (_ : constant) => genv -> fenv -> option val) by _rect.
Case Ointconst n := (fun ge sp => Some (Vint n)). 
Case Ofloatconst n := (fun ge sp => Some (Vfloat n)).
Case Osingleconst n := (fun ge sp => Some (Vsingle n)).
Case Olongconst n := (fun ge sp => Some (Vlong n)).
Case Oaddrstack ofs := (fun ge sp => Some (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs)).
Case Oaddrsymbol s ofs := (fun ge sp => Some (Genv.symbol_address ge s ofs)).
FEnd eval_constant.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
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

FRecursion find_label.
Case Sifthenelse a s1 s2 := 
(fun lbl k => 
   match find_label s1 lbl k with
   | Some sk => Some sk
   | None => find_label s2 lbl k
   end).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall lenv ge f a s1 s2 k sp e m v b,
    eval_expr ge sp e m lenv a v ->
    Val.bool_of_val v b ->
    step ge (self__Cminor.State f (Sifthenelse a s1 s2) k sp e m)
      E0 (self__Cminor.State f (if b then s1 else s2) k sp e m).

FEnd Cminor.

Family CminorSel extends Cfam.

FInductive expr : Type :=
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
       
FInductive stmt : Type := Sifthenelse: condexpr -> stmt -> stmt -> stmt.

MetaData fn binds fn_sig, fn_params, fn_vars, fn_stackspace, fn_body.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: stmt
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_body := fn_body.
FOverride Definition function_locals := fn_vars.
FOverride Definition function_params := fn_params.
FOverride Definition function_sig := fn_sig.

(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FOverride Definition fenv := block.   
FOverride Definition free_fenv := fun m sp f => Mem.free m sp 0 (fn_stackspace f).          
FOverride Definition alloc_fenv := fun sp m f sp' m' => Mem.alloc m 0 (fn_stackspace f) = (m', sp').

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
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

FRecursion find_label.
Case Sifthenelse c s1 s2 :=
  (fun lbl k =>
    match find_label s1 lbl k with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall ge f c s1 s2 k sp e m b,
   eval_condexpr ge sp e m nil c b ->
   step ge (State f (Sifthenelse c s1 s2) k sp e m)
     E0 (State f (if b then s1 else s2) k sp e m).

FEnd CminorSel.

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

Family Csharpminor extends Cfam. FEnd Csharpminor.
Family Cminor extends Cfam. FEnd Cminor.
Family CminorSel extends Cfam. FEnd CminorSel.

FEnd Comp_Loops.

Trait Comp_Switch extends Base, Comp_Loops.

Family Csharpminor.

FInductive stmt : Type :=
| Sswitch: bool -> expr -> lbl_stmts -> stmt
with lbl_stmts : Type :=
  | LSnil: lbl_stmts
  | LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

From Rocqet Require Import Switch.

FRecursion select_switch_default about lbl_stmts motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons opt s sl' :=
  (match opt with
   | None => LScons opt s sl'
   | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons opt s sl' :=
  (fun n =>
     match opt with
     | None => select_switch_case sl' n
     | Some c => if zeq c n then Some (LScons opt s sl')  else select_switch_case sl' n
     end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FRecursion seq_of_lbl_stmt about lbl_stmts motive (fun (_: lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons c s sl' := (Sseq s (seq_of_lbl_stmt sl')).
FEnd seq_of_lbl_stmt.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) 
  with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sswitch long a sl := 
  (fun lbl k => find_label_ls sl lbl k).

Case LSnil := (fun lbl k => None).
Case LScons x s sl' :=
  (fun lbl k =>
     match find_label s lbl (Kseq (seq_of_lbl_stmt sl') k) with
     | Some sk => Some sk
     | None => find_label_ls sl' lbl k
     end).
FEnd find_label with find_label_ls.
      
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f islong a cases k e le m v n lenv,
      eval_expr ge e le m lenv a v ->
      switch_argument islong v n ->
      step ge (State f (Sswitch islong a cases) k e le m)
        E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m).

FEnd Csharpminor.

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

Family Cfam.

Inherit env.
  
FDefinition set_optvar := fun (optid: option ident) (v: val) (e: env) =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

FEnd Cfam.

Family Csharpminor extends Cfam.
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

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f lenv optid ef bl k e le m vargs t vres m',
   eval_exprlist ge e le m lenv bl vargs ->
   external_call ef ge vargs m t vres m' ->
   step ge (State f (Sbuiltin optid ef bl) k e le m)
     t (State f Sskip k e (set_optvar optid vres le) m').
FEnd Csharpminor.

Family Cminor extends Cfam.

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

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f lenv optid ef bl k e le m vargs t vres m',
   eval_exprlist ge e le m lenv bl vargs ->
   external_call ef ge vargs m t vres m' ->
   step ge (State f (Sbuiltin optid ef bl) k e le m)
     t (State f Sskip k e (set_optvar optid vres le) m').

FEnd Cminor.

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

Family Cfam.
FInductive step : genv -> state -> trace -> state -> Prop :=
| step_external_function: forall ge ef vargs k m t vres m',
   external_call ef (Genv.to_senv ge) vargs m t vres m' ->
   step ge (Callstate (AST.External ef) vargs k m)
      t (Returnstate vres k m').
FEnd Cfam.

Family Csharpminor extends Cfam. FEnd Csharpminor.
Family Cminor extends Cfam. FEnd Cminor.
Family CminorSel extends Cfam. FEnd CminorSel.

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

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_return: forall ge v optid f sp e k m,
      step ge (Returnstate v (Kcall optid f e sp k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).
FEnd Cfam.

Family Csharpminor extends Cfam.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge lenv f optid sig a bl k e le m vf vargs fd,
      eval_expr ge e le m lenv a vf ->
      eval_exprlist ge e le m lenv bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step ge (State f (Scall optid sig a bl) k e le m)
        E0 (Callstate fd vargs (Kcall optid f le e k) m).
FEnd Csharpminor.

Family Cminor extends Cfam.

FInductive stmt : Type :=
| Scall : option ident -> signature -> expr -> list expr -> stmt
| Stailcall: signature -> expr -> list expr -> stmt.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
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


Family CminorSel extends Cfam.
FInductive expr : Type :=
| Eexternal : ident -> signature -> exprlist -> expr.

FInductive stmt : Type :=
| Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
| Stailcall: signature -> expr + ident -> exprlist -> stmt.

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

Trait Comp_Heap extends Base.

Trait Csharpminor_Eaddrof extends Csharpminor.
FInductive expr : Type :=
| Eaddrof : ident -> expr. (* taking the address of a variable *)

Inherit letenv.

MetaData eval_var_addr.
Inductive eval_var_addr: genv -> fenv -> ident -> block -> Prop :=
  | eval_var_addr_local:
      forall ge e id b sz,
      PTree.get id e = Some (b, sz) ->
      eval_var_addr ge e id b
  | eval_var_addr_global:
      forall ge e id b,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      eval_var_addr ge e id b.
FEnd eval_var_addr.

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eaddrof: forall ge le e lenv m id b,
      eval_var_addr ge le id b ->
      eval_expr ge le e m lenv (Eaddrof id) (Vptr b Ptrofs.zero).
                
FEnd Csharpminor_Eaddrof.

Trait Csharpminor_Eload extends Csharpminor.
FInductive expr : Type :=
| Eload : memory_chunk -> expr -> expr. (* memory read *)

FInductive eval_expr :  genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eload: forall ge le e lenv m chunk a v1 v,
      eval_expr ge le e m lenv a v1 ->
      Mem.loadv chunk m v1 = Some v ->
      eval_expr ge le e m lenv (Eload chunk a) v.
  
FEnd Csharpminor_Eload.

Trait Csharpminor_Sstore extends Csharpminor.
FInductive stmt : Type :=
| Sstore : memory_chunk -> expr -> expr -> stmt.

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
  
FEnd Csharpminor_Sstore.

Family Csharpminor extends 
  Csharpminor_Sstore, 
  Csharpminor_Eload, 
  Csharpminor_Eaddrof.
FEnd Csharpminor.

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
