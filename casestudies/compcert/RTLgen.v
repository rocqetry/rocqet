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

MetaData fn.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: self__CminorSel.stmt
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_body := self__CminorSel.fn_body.
FOverride Definition function_locals := self__CminorSel.fn_vars.
FOverride Definition function_params := self__CminorSel.fn_params.
FOverride Definition function_sig := self__CminorSel.fn_sig.

(* stack pointer *)
(* Vptr sp Ptrofs.zero *)
FOverride Definition fenv := block.   
FOverride Definition free_fenv := fun m sp f => Mem.free m sp 0 f.(self__CminorSel.fn_stackspace).          
FOverride Definition alloc_fenv := fun sp m f sp' m' => Mem.alloc m 0 f.(self__CminorSel.fn_stackspace) = (m', sp).

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

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_ifthenelse: forall ge f c s1 s2 k sp e m b,
   eval_condexpr ge sp e m nil c b ->
   step ge (self__CminorSel.State f (Sifthenelse c s1 s2) k sp e m)
     E0 (self__CminorSel.State f (if b then s1 else s2) k sp e m).

FEnd CminorSel.

Family RTL.
FDefinition node := positive.

From Rocqet Require Import Registers.
      
FInductive instruction: Type :=
| Inop: node -> instruction
| Iop: operation -> list reg -> reg -> node -> instruction          
| Icond: condition -> list reg -> node -> node -> instruction
| Ireturn: option reg -> instruction.

FDefinition code: Type := PTree.t instruction.

MetaData function.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: self__RTL.code;
  fn_entrypoint: self__RTL.node
}.
FEnd function.

FDefinition fundef := AST.fundef function.

FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => self__RTL.fn_sig f
  | AST.External ef => ef_sig ef
  end.

(* operational semantics *)             
FDefinition genv := Genv.t fundef unit.
FDefinition regset := Regmap.t val.

MetaData init_regs.
Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : self__RTL.regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.
FEnd init_regs.

MetaData stackframe binds Stackframe.
Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)(* where to store the result *)
             (f: self__RTL.function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (pc: self__RTL.node)(* program point in calling function *)
             (rs: self__RTL.regset),(* register state in calling function *)
      stackframe.
FEnd stackframe.

MetaData state binds State, CallState, Returnstate.
Inductive state : Type :=
  | State:
      forall (stack: list self__RTL.stackframe)(* call stack *)
             (f: self__RTL.function)(* current function *)
             (sp: val)(* stack pointer *)
             (pc: self__RTL.node)(* current program point in c *)
             (rs: self__RTL.regset)(* register state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list self__RTL.stackframe)(* call stack *)
             (f: self__RTL.fundef)(* function to call *)
             (args: list val)(* arguments to the call *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list self__RTL.stackframe)(* call stack *)
             (v: val)(* return value for the call *)
             (m: mem),(* memory state *)
      state.           
FEnd state.
           
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Inop:
    forall ge s f sp pc rs m pc',
    (self__RTL.fn_code f)!pc = Some(Inop pc') ->
    step ge (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Iop:
    forall ge s f sp pc rs m op args res pc' v,
    (self__RTL.fn_code f)!pc = Some(Iop op args res pc') ->
    eval_operation ge sp op rs##args m = Some v ->
    step ge (State s f sp pc rs m)
      E0 (State s f sp pc' (rs#res <- v) m)
| exec_Icond:
    forall ge s f sp pc rs m cond args ifso ifnot b pc',
    (self__RTL.fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
    eval_condition cond rs##args m = Some b ->
    pc' = (if b then ifso else ifnot) ->
    step ge (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Ireturn:
    forall ge s f stk pc rs m or m',
    (self__RTL.fn_code f)!pc = Some(Ireturn or) ->
    Mem.free m stk 0 f.(self__RTL.fn_stacksize) = Some m' ->
    step ge (State s f (Vptr stk Ptrofs.zero) pc rs m)
      E0 (Returnstate s (regmap_optget or Vundef rs) m')
| exec_return:
    forall ge res f sp pc rs s vres m,
    step ge (Returnstate (Stackframe res f sp pc rs :: s) vres m)
      E0 (State s f sp pc (rs#res <- vres) m).

MetaData initial_state.
Inductive initial_state (p: self__RTL.program): self__RTL.state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    self__RTL.funsig f = signature_main ->
    initial_state p (self__RTL.Callstate nil f nil m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__RTL.state -> int -> Prop :=
   | final_state_intro: forall r m,
      final_state (self__RTL.Returnstate nil (Vint r) m) r.
FEnd final_state.

FEnd RTL.

From Rocqet Require Import RTLmonad.

(* CminorSel -> RTL *)
Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FDefinition res := fun (A : Type) => res A T.instruction.
FDefinition mon := fun (A : Type) => mon A T.instruction.
FDefinition state := state T.instruction.

FLemma init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty T.instruction)!pc = None.
FProofLemma. intros; right; apply PTree.gempty. Qed. CloseFLemma.

FDefinition init_state : state :=
  mkstate T.instruction 1%positive 1%positive (PTree.empty T.instruction) init_state_wf.

FLemma add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode T.instruction) in
  Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code T.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_instr_incr:
  forall s i,
  let n := s.(st_nextnode T.instruction) in
  state_incr T.instruction s (mkstate T.instruction s.(st_nextreg T.instruction)
                (Pos.succ n)
                (PTree.set n i s.(st_code T.instruction))
                (add_instr_wf s i)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition add_instr : T.instruction -> mon T.node := fun (i: T.instruction) =>
  fun s =>
    let n := s.(st_nextnode T.instruction) in
    OK n
       (mkstate T.instruction s.(st_nextreg T.instruction) (Pos.succ n) (PTree.set n i s.(st_code T.instruction))
                (add_instr_wf s i))
       (add_instr_incr s i).

FLemma reserve_instr_wf:
  forall s pc,
    Plt pc (Pos.succ s.(st_nextnode T.instruction)) \/ s.(st_code T.instruction)!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode T.instruction) in
  state_incr T.instruction s (mkstate T.instruction s.(st_nextreg T.instruction)
                (Pos.succ n)
                s.(st_code T.instruction)
                    (reserve_instr_wf s)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition reserve_instr : mon T.node :=
  fun (s: state) =>
  let n := s.(st_nextnode T.instruction) in
  OK n
     (mkstate T.instruction s.(st_nextreg T.instruction) (Pos.succ n) s.(st_code T.instruction) (reserve_instr_wf s))
     (reserve_instr_incr s).

FLemma update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode T.instruction) ->
  forall pc,
    Plt pc s.(st_nextnode T.instruction) \/ (PTree.set n i s.(st_code T.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode T.instruction)),
  s.(st_code T.instruction)!n = None ->
  state_incr T.instruction s
             (mkstate T.instruction s.(st_nextreg T.instruction) s.(st_nextnode T.instruction) (PTree.set n i s.(st_code T.instruction))
                     (update_instr_wf s n i LT)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma check_empty_node:
  forall (s: state) (n: T.node), { s.(st_code T.instruction)!n = None } + { True }.
FProofLemma.  intros. case (s.(st_code self__RTLgen.T.instruction)!n); intros. right; auto. left; auto. Qed. CloseFLemma.

FDefinition update_instr : T.node -> T.instruction -> mon unit := fun (n: T.node) (i: T.instruction) => 
  fun s =>
    match plt n s.(st_nextnode T.instruction), check_empty_node s n with
    | left L, left EMPTY =>
        OK tt
           (mkstate T.instruction s.(st_nextreg T.instruction) s.(st_nextnode T.instruction) (PTree.set n i s.(st_code T.instruction))
                    (update_instr_wf s n i L))
           (update_instr_incr s n i L EMPTY)
    | _, _ =>
        Error (Errors.msg "RTLgen.update_instr")
    end.

FLemma new_reg_incr:
  forall s,
  state_incr T.instruction s (mkstate T.instruction (Pos.succ s.(st_nextreg T.instruction))
                        s.(st_nextnode T.instruction) s.(st_code T.instruction) s.(st_wf T.instruction)).
FProofLemma. constructor; simpl. apply Ple_refl. apply Ple_succ. auto. Qed. CloseFLemma.

FDefinition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg T.instruction)
       (mkstate T.instruction (Pos.succ s.(st_nextreg T.instruction)) s.(st_nextnode T.instruction) s.(st_code T.instruction) s.(st_wf T.instruction))
       (new_reg_incr s).

FDefinition init_mapping : mapping :=
  mkmapping (PTree.empty reg) nil.

FDefinition add_var : mapping -> ident -> mon (reg * mapping) := fun map name => 
  do r <- new_reg;
     ret (r, mkmapping (PTree.set name r map.(map_vars))
                       map.(map_letvars)).

MetaData add_vars.
Fixpoint add_vars (map: mapping) (names: list ident)
                  {struct names} : self__RTLgen.mon (list reg * mapping) :=
  match names with
  | nil => ret (nil, map)
  | n1 :: nl =>
      do (rl, map1) <- add_vars map nl;
      do (r1, map2) <- self__RTLgen.add_var map1 n1;
      ret (r1 :: rl, map2)
  end.
FEnd add_vars.

FDefinition find_var : mapping -> ident -> mon reg := fun (map: mapping) (name: ident) =>
  match PTree.get name map.(map_vars) with
  | None => error (Errors.MSG "RTLgen: unbound variable " :: Errors.CTX name :: nil)
  | Some r => ret r
  end.

FDefinition add_letvar : mapping -> reg -> mapping := fun (map: mapping) (r: reg) =>
  mkmapping map.(map_vars) (r :: map.(map_letvars)).

FDefinition find_letvar : mapping -> nat -> mon reg := fun (map: mapping) (idx: nat) =>
  match List.nth_error map.(map_letvars) idx with
  | None => error (Errors.msg "RTLgen: unbound let variable")
  | Some r => ret r
  end.

FDefinition add_move : reg -> reg -> T.node -> mon T.node := fun (rs rd: reg) (nd: T.node) => 
  if Reg.eq rs rd
  then ret nd
  else add_instr (T.Iop Op.Omove (rs::nil) rd nd).

FRecursion alloc_reg about S.expr motive (fun (_ : S.expr) => mapping -> mon reg) by _rect.
Case Evar id := (fun map => find_var map id).
Case Eletvar n := (fun map => find_letvar map n).
Case Eop := (fun op args => fun map => new_reg).
Case Econdition c a0 a1 := (fun map => new_reg).
Case Elet a b := (fun map => new_reg).
FEnd alloc_reg.

FRecursion alloc_regs about S.exprlist motive (fun (_ : S.exprlist) => mapping -> mon (list reg)) by _rect.
Case Enil := (fun map => ret nil).
Case Econs a bl :=
(fun map =>
  do r <- alloc_reg a map;
  do rl <- alloc_regs bl map;
  ret (r :: rl)).
FEnd alloc_regs.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => mapping -> reg -> T.node -> mon T.node)
  with transl_exprlist about S.exprlist motive (fun (_ : S.exprlist) => mapping -> list reg -> T.node -> mon T.node)
  with transl_condexpr about S.condexpr motive (fun (_ : S.condexpr) => mapping  -> T.node -> T.node -> mon T.node) by _rect.
Case Evar v := (fun map rd nd => do r <- find_var map v; add_move r rd nd).
Case Elet b c :=
(fun map rd nd => 
   do r <- new_reg;
   do nc <- transl_expr c (add_letvar map r) rd nd;
   transl_expr b map r nc).
Case Eop op al :=
(fun map rd nd => 
    do rl <- alloc_regs al map;
    do no <- add_instr (T.Iop op rl rd nd);
    transl_exprlist al map rl no).
Case Econdition a b c :=
(fun map rd nd => 
  do nfalse <- transl_expr c map rd nd;
  do ntrue <- transl_expr b map rd nd;
  transl_condexpr a map ntrue nfalse).
Case Eletvar n := (fun map rd nd => do r <- find_letvar map n; add_move r rd nd).

(* exprlist *)
Case Enil := (fun map rl nd => match rl with nil => ret nd | _ => error (Errors.msg "RTLgen.transl_exprlist") end).
Case Econs b bs :=
(fun map rl nd => 
   match rl with 
   | r :: rs =>  
       do no <- transl_exprlist bs map rs nd; 
       transl_expr b map r no
   | _ => error (Errors.msg "RTLgen.transl_exprlist") end).

(* condexpr *)
Case CEcond c al :=
(fun map ntrue nfalse => 
   do rl <- alloc_regs al map;
   do nt <- add_instr (T.Icond c rl ntrue nfalse);
   transl_exprlist al map rl nt).
Case CEcondition a b c :=
(fun map ntrue nfalse => 
   do nc <- transl_condexpr c map ntrue nfalse;
   do nb <- transl_condexpr b map ntrue nfalse;
   transl_condexpr a map nb nc).
Case CElet b c :=
(fun map ntrue nfalse => 
   do r <- new_reg;
   do nc <- transl_condexpr c (add_letvar map r) ntrue nfalse;
   transl_expr b map r nc).
FEnd transl_expr with transl_exprlist with transl_condexpr.
        
FDefinition labelmap : Type := PTree.t T.node.
        
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => mapping -> T.node -> list T.node -> labelmap -> T.node -> option reg -> mon T.node) by _rect.
Case Sskip := (fun map nd nexits ngoto nret rret => ret nd).
Case Sassign v b :=
(fun map nd nexits ngoto nret rret => 
   do r <- find_var map v;
   transl_expr b map r nd). 
Case Sseq s1 s2 :=
(fun map nd nexits ngoto nret rret =>  
   do ns <- transl_stmt s2 map nd nexits ngoto nret rret;
   transl_stmt s1 map ns nexits ngoto nret rret).
Case Sifthenelse c strue sfalse :=
(fun map nd nexits ngoto nret rret => 
   (* Don't use "more likely" heuristic *)
   do ntrue <- transl_stmt strue map nd nexits ngoto nret rret;
   do nfalse <- transl_stmt sfalse map nd nexits ngoto nret rret;
   transl_condexpr c map ntrue nfalse).
Case Sreturn opt_a :=
(fun map nd nexits ngoto nret rret => 
  match opt_a, rret with
  | None, _ => ret nret
  | Some a, Some r => transl_expr a map r nret
  | _, _ => error (Errors.msg "RTLgen: type mismatch on return")
  end).
Case Slabel lbl s' :=
(fun map nd nexits ngoto nret rret => 
  do ns <- transl_stmt s' map nd nexits ngoto nret rret;
  match ngoto!lbl with
  | None => error (Errors.msg "RTLgen: unbound label")
  | Some n =>
      do xx <-
        (handle_error (update_instr n (T.Inop ns))
                      (error (Errors.MSG "Multiply-defined label " ::
                              Errors.CTX lbl :: nil)));
      ret ns
  end).
Case Sgoto lbl :=
(fun map nd nexits ngoto nret rret => 
  match ngoto!lbl with
  | None => error (Errors.MSG "Undefined defined label " ::
                  Errors.CTX lbl :: nil)
  | Some n => ret n
  end).
FEnd transl_stmt.

FDefinition alloc_label : S.label -> labelmap -> mon labelmap :=
  fun (lbl: S.label) (map: labelmap) =>
  do n <- reserve_instr;
  ret (PTree.set lbl n map).   

FRecursion reserve_labels about S.stmt
  motive (fun (_ : S.stmt) => labelmap -> mon labelmap) by _rect.
Case Sseq s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Sifthenelse e s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Slabel lbl s1 := (fun lm => do lm' <- reserve_labels s1 lm; alloc_label lbl lm').
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FDefinition ret_reg : signature -> reg -> option reg :=
  fun (sig: signature) (rd: reg) =>
  if rettype_eq sig.(AST.sig_res) AST.Tvoid then None else Some rd.

FDefinition transl_fun : S.function -> mon (T.node * list reg) :=
  fun (f: S.function) => 
  do ngoto <- reserve_labels (S.fn_body f) (PTree.empty T.node);
  do (rparams, map1) <- add_vars init_mapping (S.fn_params f);
  do (rvars, map2) <- add_vars map1 (S.fn_vars f);
  do rret <- new_reg;
  let orret := ret_reg (S.fn_sig f) rret in
  do nret <- add_instr (T.Ireturn orret);
  do nentry <- transl_stmt (S.fn_body f) map2 nret nil ngoto nret orret;
  ret (nentry, rparams).

FDefinition transl_function : S.function -> Errors.res T.function := 
    fun (f: S.function) => 
  match transl_fun f init_state with
  | Error msg => Errors.Error msg
  | OK (nentry, rparams) s i =>
      Errors.OK (T.mkfunction
                   (S.fn_sig f)
                   rparams
                   (S.fn_stackspace f)
                   s.(st_code T.instruction)
                   nentry)
  end.

FDefinition transl_fundef := transf_partial_fundef transl_function.

FDefinition transl_program : S.program -> Errors.res T.program := 
  fun (p: S.program) =>
     transform_partial_program transl_fundef p.                 

(* relational spec *)

FDefinition reg_in_map : mapping -> reg -> Prop := fun (m: mapping) (r: reg) =>
  (exists id, m.(map_vars)!id = Some r) \/ In r m.(map_letvars).

MetaData tr_move.
Inductive tr_move (c: self__RTLgen.T.code): self__RTLgen.T.node -> reg -> self__RTLgen.T.node -> reg -> Prop :=
| tr_move_0: forall n r,
    tr_move c n r n r
| tr_move_1: forall ns rs nd rd,
    c!ns = Some (self__RTLgen.T.Iop Op.Omove (rs :: nil) rd nd) ->
    tr_move c ns rs nd rd.
FEnd tr_move.

MetaData reg_map_ok.
Inductive reg_map_ok: mapping -> reg -> option AST.ident -> Prop :=
| reg_map_ok_novar: forall map rd,
    ~self__RTLgen.reg_in_map map rd ->
    reg_map_ok map rd None
| reg_map_ok_somevar: forall map rd id,
    map.(map_vars)!id = Some rd ->
    reg_map_ok map rd (Some id).

Global Hint Resolve reg_map_ok_novar: rtlg.
FEnd reg_map_ok.

(*MetaData reg_map_ok_open.
Import self__RTLgen.
FEnd reg_map_ok_open.*)
                 
FInductive tr_expr : T.code -> mapping -> list reg -> S.expr -> T.node -> T.node -> reg -> option AST.ident -> Prop :=
| tr_Evar: forall c map pr id ns nd r rd dst,
    map.(map_vars)!id = Some r ->
    ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
    tr_move c ns r nd rd ->
    tr_expr c map pr (S.Evar id) ns nd rd dst            
| tr_Eop: forall c map pr op al ns nd rd n1 rl dst,
    tr_exprlist c map pr al ns n1 rl ->
    c!n1 = Some (T.Iop op rl rd nd) ->
    reg_map_ok map rd dst -> ~In rd pr ->
    tr_expr c map pr (S.Eop op al) ns nd rd dst            
| tr_Econdition: forall c map pr a ifso ifnot ns nd rd ntrue nfalse dst,
    tr_condition c map pr a ns ntrue nfalse ->
    tr_expr c map pr ifso ntrue nd rd dst ->
    tr_expr c map pr ifnot nfalse nd rd dst ->
    tr_expr c map pr (S.Econdition a ifso ifnot) ns nd rd dst
| tr_Elet: forall c map pr b1 b2 ns nd rd n1 r dst,
    ~reg_in_map map r ->
    tr_expr c map pr b1 ns n1 r None ->
    tr_expr c (add_letvar map r) pr b2 n1 nd rd dst ->
    tr_expr c map pr (S.Elet b1 b2) ns nd rd dst
| tr_Eletvar: forall c map pr n ns nd rd r dst,
    List.nth_error map.(map_letvars) n = Some r ->
    ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
    tr_move c ns r nd rd ->
    tr_expr c map pr (S.Eletvar n) ns nd rd dst
with tr_condition : T.code -> mapping -> list reg -> S.condexpr -> T.node -> T.node -> T.node -> Prop :=
| tr_CEcond: forall c map pr cond bl ns ntrue nfalse n1 rl,
    tr_exprlist c map pr bl ns n1 rl ->
    c!n1 = Some (T.Icond cond rl ntrue nfalse) ->
    tr_condition c map pr (S.CEcond cond bl) ns ntrue nfalse
| tr_CEcondition: forall c map pr a1 a2 a3 ns ntrue nfalse n2 n3,
    tr_condition c map pr a1 ns n2 n3 ->
    tr_condition c map pr a2 n2 ntrue nfalse ->
    tr_condition c map pr a3 n3 ntrue nfalse ->
    tr_condition c map pr (S.CEcondition a1 a2 a3) ns ntrue nfalse
| tr_CElet: forall c map pr a b ns ntrue nfalse r n1,
    ~reg_in_map map r ->
    tr_expr c map pr a ns n1 r None ->
    tr_condition c (add_letvar map r) pr b n1 ntrue nfalse ->
    tr_condition c map pr (S.CElet a b) ns ntrue nfalse
with tr_exprlist : T.code -> mapping -> list reg -> S.exprlist -> T.node -> T.node -> list reg -> Prop :=
| tr_Enil: forall c map pr n,
    tr_exprlist c map pr S.Enil n n nil
| tr_Econs: forall c map pr a1 al ns nd r1 rl n1,
    tr_expr c map pr a1 ns n1 r1 None ->
    tr_exprlist c map (r1 :: pr) al n1 nd rl ->
    tr_exprlist c map pr (S.Econs a1 al) ns nd (r1 :: rl).
    
FInductive tr_stmt : T.code -> mapping -> S.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=
| tr_Sskip: forall c map ns nexits ngoto nret rret,
    tr_stmt c map S.Sskip ns ns nexits ngoto nret rret            
| tr_Sassign: forall c map id a ns nd nexits ngoto nret rret r,
  map.(map_vars)!id = Some r ->
  tr_expr c map nil a ns nd r (Some id) ->
  tr_stmt c map (S.Sassign id a) ns nd nexits ngoto nret rret          
| tr_Sseq: forall c map s1 s2 ns nd nexits ngoto nret rret n,
  tr_stmt c map s2 n nd nexits ngoto nret rret ->
  tr_stmt c map s1 ns n nexits ngoto nret rret ->
  tr_stmt c map (S.Sseq s1 s2) ns nd nexits ngoto nret rret
| tr_Sifthenelse: forall c map a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse,
  tr_stmt c map strue ntrue nd nexits ngoto nret rret ->
  tr_stmt c map sfalse nfalse nd nexits ngoto nret rret ->
  tr_condition c map nil a ns ntrue nfalse ->
  tr_stmt c map (S.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
| tr_Sreturn_none: forall c map nret nd nexits ngoto rret,
  tr_stmt c map (S.Sreturn None) nret nd nexits ngoto nret rret
| tr_Sreturn_some: forall c map a ns nd nexits ngoto nret rret,
  tr_expr c map nil a ns nret rret None ->
  tr_stmt c map (S.Sreturn (Some a)) ns nd nexits ngoto nret (Some rret)
| tr_Slabel: forall c map lbl s ns nd nexits ngoto nret rret n,
  ngoto!lbl = Some n ->
  c!n = Some (T.Inop ns) ->
  tr_stmt c map s ns nd nexits ngoto nret rret ->
  tr_stmt c map (S.Slabel lbl s) ns nd nexits ngoto nret rret
| tr_Sgoto: forall c map lbl ns nd nexits ngoto nret rret,
  ngoto!lbl = Some ns ->
  tr_stmt c map (S.Sgoto lbl) ns nd nexits ngoto nret rret.   

MetaData tr_function.
Inductive tr_function: self__RTLgen.S.function -> self__RTLgen.T.function -> Prop :=
| tr_function_intro:
    forall f code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret,
    self__RTLgen.add_vars self__RTLgen.init_mapping f.(self__RTLgen.S.fn_params) s0 = OK (rparams, map1) s1 i1 ->
    self__RTLgen.add_vars map1 f.(self__RTLgen.S.fn_vars) s1 = OK (rvars, map2) s2 i2 ->
    orret = self__RTLgen.ret_reg f.(self__RTLgen.S.fn_sig) rret ->
    self__RTLgen.tr_stmt code map2 f.(self__RTLgen.S.fn_body) nentry nret nil ngoto nret orret ->
    code!nret = Some(self__RTLgen.T.Ireturn orret) ->
    tr_function f (self__RTLgen.T.mkfunction
                    f.(self__RTLgen.S.fn_sig)
                    rparams
                    f.(self__RTLgen.S.fn_stackspace)
                    code
                    nentry).
FEnd tr_function.

MetaData tr_fun.
Inductive tr_fun (tf: self__RTLgen.T.function) (map: mapping)
                 (f: self__RTLgen.S.function)
                 (ngoto: self__RTLgen.labelmap) (nret: self__RTLgen.T.node) (rret: option reg) : Prop :=
  | tr_fun_intro: forall nentry r,
      rret = self__RTLgen.ret_reg f.(self__RTLgen.S.fn_sig) r ->
      self__RTLgen.tr_stmt tf.(self__RTLgen.T.fn_code) map f.(self__RTLgen.S.fn_body) nentry nret nil ngoto nret rret ->
      tf.(self__RTLgen.T.fn_stacksize) = f.(self__RTLgen.S.fn_stackspace) ->
      tr_fun tf map f ngoto nret rret.
FEnd tr_fun.

MetaData tr_cont binds match_stacks.
Import self__RTLgen.
Inductive tr_cont: T.code -> mapping ->
                   S.cont -> T.node -> list T.node -> labelmap -> T.node -> option reg ->
                   list T.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont c map k n nexits ngoto nret rret cs ->
      tr_cont c map (S.Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(T.Ireturn rret) ->
      match_stacks S.Kstop cs ->
      tr_cont c map S.Kstop nret nil ngoto nret rret cs             
with match_stacks: S.cont -> list T.stackframe -> Prop :=
  | match_stacks_stop:
    match_stacks S.Kstop nil.
FEnd tr_cont.

MetaData map_wf.
Import self__RTLgen.
Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.
FEnd map_wf.

MetaData match_env.
Import self__RTLgen.
Record match_env
      (map: mapping) (e: S.env) (le: S.letenv) (rs: T.regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ Val.lessdef v rs#r);
    me_letvars:
      Val.lessdef_list le rs##(map.(map_letvars))
  }.
FEnd match_env.

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

MetaData match_states.
Import self__RTLgen.
Inductive match_states: S.state -> T.state -> Prop :=
  | match_state:
      forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret
        (MWF: map_wf map)
        (TS: tr_stmt tf.(T.fn_code) map s ns ncont nexits ngoto nret rret)
        (TF: tr_fun tf map f ngoto nret rret)
        (TK: tr_cont tf.(T.fn_code) map k ncont nexits ngoto nret rret cs)
        (ME: match_env map e nil rs)
        (MEXT: Mem.extends m tm),
      match_states (S.State f s k sp e m)
                   (T.State cs tf (Vptr sp Ptrofs.zero) ns rs tm)
  | match_callstate:
      forall f args targs k m tm cs tf
        (TF: transl_fundef f = Errors.OK tf)
        (MS: match_stacks k cs)
        (LD: Val.lessdef_list args targs)
        (MEXT: Mem.extends m tm),
      match_states (S.Callstate f args k m)
                   (T.Callstate cs tf targs tm)
  | match_returnstate:
      forall v tv k m tm cs
        (MS: match_stacks k cs)
        (LD: Val.lessdef v tv)
        (MEXT: Mem.extends m tm),
      match_states (S.Returnstate v k m)
        (T.Returnstate cs tv tm).
FEnd match_states.

FRecursion size_stmt about S.stmt motive (fun (_ : S.stmt) => nat) by _rect.
Local Open Scope nat_scope.
Case Sskip := 0.
Case Sseq s1 s2 := (size_stmt s1 + size_stmt s2 + 1).
Case Sifthenelse c s1 s2 := (size_stmt s1 + size_stmt s2 + 1).
Case Slabel lbl s1 := (size_stmt s1 + 1).
Case _ := 1.
FEnd size_stmt.

FRecursion size_cont about S.cont motive (fun (_ : S.cont) => nat) by _rect.
Case Kseq s k1 := (size_stmt s + size_cont k1 + 1).
Case _ := 0.
FEnd size_cont.

FDefinition measure_state := fun (s: S.state) =>
  match s with
  | self__RTLgen.S.State _ s k _ _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _ => (0, 0)
  end.

FDefinition lt_state := fun (S1 S2: S.state) =>
  lex_ord lt lt (measure_state S1) (measure_state S2).

FLemma lt_state_intro:
  forall f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (S.State f1 s1 k1 sp1 e1 m1)
           (S.State f2 s2 k2 sp2 e2 m2).
FProofLemma.
intros. unfold self__RTLgen.lt_state. simpl. destruct H as [A | [A B]].
  left. auto. rewrite A. right. auto. 
Qed. CloseFLemma.

MetaData Lt_state.
Import self__RTLgen.
Ltac Lt_state :=
  apply lt_state_intro; simpl; try lia.
FEnd Lt_state.

(* Inductive tr_stmt (c: code) (map: mapping):
     stmt -> node -> node -> list node -> labelmap -> node -> option reg -> Prop :=
  | tr_Sskip: forall ns nexits ngoto nret rret,
     tr_stmt c map Sskip ns ns nexits ngoto nret rret *)

Closing Fact tr_stmt_skip_inv: 
  forall c map ns ncont nexits ngoto nret rret,
  tr_stmt c map S.Sskip ns ncont nexits ngoto nret rret -> 
  ncont = ns 
by plain { intros until rret; intros H; inv H; eauto }.  

Closing Fact Kseq_inv : forall s0 k0 s k,
    self__RTLgen.S.Kseq s0 k0 = self__RTLgen.S.Kseq s k -> 
    s0 = s /\ k0 = k
  by plain { intros until k; intros H; inversion H; eauto }.
 
FInduction transl_step_correct about S.step
  motive (fun ge S1 t S2 (_ : S.step ge S1 t S2) =>
  forall prog tprog tge, match_prog prog tprog -> 
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->            
  forall R1 (MS : match_states S1 R1),
  exists R2,
  (plus T.step tge R1 t R2 \/ (star T.step tge R1 t R2 /\ lt_state S2 S1))
  /\ match_states S2 R2).
FProof.
+ intros until tge. intros A B C.
  intros R1 MSTATE; inv MSTATE. 
  apply self__RTLgen.tr_stmt_skip_inv in TS. rewrite <- TS. inv TK. econstructor; split. 
  right; split. apply star_refl. self__RTLgen.Lt_state.
  apply self__RTLgen.Kseq_inv in H.   
  do 2 fsimpl. econstructor; eauto. 
  destruct H as [Y Z]. rewrite Y. rewrite Z. 
  lia. econstructor. apply MWF. 
  apply self__RTLgen.Kseq_inv in H. destruct H as [Y Z]. rewrite <- Y. apply H0. apply TF.
  apply self__RTLgen.Kseq_inv in H. destruct H as [Y Z]. rewrite <- Z.
  apply H3. apply ME. apply MEXT. 
  
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
Qed. FEnd transl_step_correct.

(*
Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.
*)

FLemma transl_initial_states: 
  forall prog tprog, match_prog prog tprog -> 
  forall S', S.initial_state prog S' ->
  exists R, T.initial_state tprog R /\ match_states S' R.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma transl_final_states:
  forall S' R r,
  match_states S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma. apply cheat. Qed. CloseFLemma.

FEnd RTLgen.

FEnd Base.

Trait Comp_Loops extends Base.

Family CminorSel.
FInductive stmt : Type :=
| Sblock: stmt -> stmt
| Sexit: nat -> stmt
| Sloop: stmt -> stmt.
FEnd CminorSel.

Trait RTL_jumptable extends RTL.
FInductive instruction: Type :=
| Ijumptable: reg -> list node -> instruction.  
FEnd RTL_jumptable.

Family RTL extends RTL_jumptable.
FEnd RTL.

From Rocqet Require Import RTLmonad.

Trait RTLgen_Sloop extends RTLgen.

Inherit labelmap.

FDefinition transl_exit : list T.node -> nat -> mon T.node := fun nexits n =>
  match nth_error nexits n with
  | None => error (Errors.msg "RTLgen: wrong exit")
  | Some ne => ret ne
  end.

FRecursion transl_stmt.
Case Sloop sbody :=
(fun map nd nexits ngoto nret rret =>
  do n1 <- reserve_instr;
  do n2 <- transl_stmt sbody map n1 nexits ngoto nret rret;
  do xx <- update_instr n1 (T.Inop n2);
  add_instr (T.Inop n2)).
Case Sblock sbody :=
(fun map nd nexits ngoto nret rret =>
   transl_stmt sbody map nd (nd :: nexits) ngoto nret rret).
Case Sexit n := (fun map nd nexits ngoto nret rret => transl_exit nexits n).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sloop s1 := (fun lm => reserve_labels s1 lm).
Case Sblock s1 := (fun lm => reserve_labels s1 lm).
Case Sexit n := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen_Sloop.

Family RTLgen extends RTLgen_Sloop.
FEnd RTLgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family CminorSel.
FInductive expr : Type :=
| Ebuiltin : external_function -> exprlist -> expr
| Eexternal : ident -> signature -> exprlist -> expr.

FInductive stmt : Type :=
| Sbuiltin : builtin_res ident -> external_function -> list (builtin_arg expr) -> stmt.
FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction.
FEnd RTL.

Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FDefinition exprlist_of_expr_list : list S.expr -> S.exprlist := fun l =>
  List.fold_right S.Econs S.Enil l.

MetaData params_of_builtin_arg.
Fixpoint params_of_builtin_arg (A: Type) (a: builtin_arg A) : list A :=
  match a with
  | BA x => x :: nil
  | BA_splitlong hi lo => params_of_builtin_arg A hi ++ params_of_builtin_arg A lo
  | BA_addptr a1 a2 => params_of_builtin_arg A a1 ++ params_of_builtin_arg A a2
  | _ => nil
  end.
FEnd params_of_builtin_arg.

FDefinition params_of_builtin_args := fun (A: Type) (al: list (builtin_arg A)) =>
  List.fold_right (fun a l => params_of_builtin_arg A a ++ l) nil al.

MetaData convert_builtin_arg.
Fixpoint convert_builtin_arg {A: Type} (a: builtin_arg self__RTLgen.S.expr) (rl: list A) : builtin_arg A * list A :=
  match a with
  | BA a =>
      match rl with
      | r :: rs => (BA r, rs)
      | nil => (BA_int Int.zero, nil)(* never happens *)
      end
  | BA_int n => (BA_int n, rl)
  | BA_long n => (BA_long n, rl)
  | BA_float n => (BA_float n, rl)
  | BA_single n => (BA_single n, rl)
  | BA_loadstack chunk ofs => (BA_loadstack chunk ofs, rl)
  | BA_addrstack ofs => (BA_addrstack ofs, rl)
  | BA_loadglobal chunk id ofs => (BA_loadglobal chunk id ofs, rl)
  | BA_addrglobal id ofs => (BA_addrglobal id ofs, rl)
  | BA_splitlong hi lo =>
      let (hi', rl1) := convert_builtin_arg hi rl in
      let (lo', rl2) := convert_builtin_arg lo rl1 in
      (BA_splitlong hi' lo', rl2)
  | BA_addptr a1 a2 =>
      let (a1', rl1) := convert_builtin_arg a1 rl in
      let (a2', rl2) := convert_builtin_arg a2 rl1 in
      (BA_addptr a1' a2', rl2)
  end.
FEnd convert_builtin_arg.

MetaData convert_builtin_args.
Fixpoint convert_builtin_args {A: Type} (al: list (builtin_arg self__RTLgen.S.expr)) (rl: list A) : list (builtin_arg A) :=
  match al with
  | nil => nil
  | a1 :: al =>
      let (a1', rl1) := self__RTLgen.convert_builtin_arg a1 rl in
      a1' :: convert_builtin_args al rl1
  end.
FEnd convert_builtin_args.

From Rocqet Require Import RTLmonad.

FRecursion alloc_reg.
Case _ := (fun map => new_reg).
FEnd alloc_reg.

FRecursion transl_expr with transl_exprlist with transl_condexpr.
Case Ebuiltin ef al :=
  (fun map rd nd =>
     do rl <- alloc_regs al map;
     do no <- add_instr (T.Ibuiltin ef (List.map (@BA reg) rl) (BR rd) nd);
     transl_exprlist al map rl no).
Case Eexternal id sg al :=
  (fun map rd nd =>
    do rl <- alloc_regs al map;
    do no <- add_instr cheat (* (T.Icall sg (inr id) rl rd nd)*);
    transl_exprlist al map rl no).
FEnd transl_expr with transl_exprlist with transl_condexpr.

Inherit labelmap.

FDefinition convert_builtin_res : mapping -> rettype -> builtin_res ident -> self__RTLgen.mon (builtin_res reg)
 := fun map ty r =>                                                                                            
  match r with
  | BR id => do r <- find_var map id; ret (BR r)
  | BR_none => if rettype_eq ty AST.Tvoid then ret BR_none else (do r <- new_reg; ret (BR r))
  | _ => error (Errors.msg "RTLgen: bad builtin_res")
  end.

FRecursion transl_stmt.
Case Sbuiltin r ef args :=
(fun map nd nexits ngoto nret rret =>  
   let al := exprlist_of_expr_list (params_of_builtin_args S.expr args) in
   do rargs <- alloc_regs al map;
   let args' := convert_builtin_args args rargs in
   do res' <- convert_builtin_res map (sig_res (ef_sig ef)) r;
   do n1 <- add_instr (T.Ibuiltin ef args' res' nd);
   transl_exprlist al map rargs n1).
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family CminorSel.
(*CminorSel *)
FInductive expr : Type :=
| Eload : memory_chunk -> addressing -> exprlist -> expr.

FInductive stmt : Type :=                                                        
| Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt.

FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
| Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction.
FEnd RTL.

Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FRecursion alloc_reg.
Case Eload chunkn addr al := (fun map => new_reg).
FEnd alloc_reg.

From Rocqet Require Import RTLmonad.
FRecursion transl_expr
  with transl_exprlist
  with transl_condexpr.
Case Eload chunk addr al := 
  (fun map rd nd =>
     do rl <- alloc_regs al map;
     do no <- add_instr (T.Iload chunk addr rl rd nd);
     transl_exprlist al map rl no).
FEnd transl_expr with transl_exprlist with transl_condexpr.

FRecursion transl_stmt.
Case Sstore chunk addr al b :=
 (fun map nd nexits ngoto nret rret =>
  do rl <- alloc_regs al map;
  do r <- alloc_reg b map;
  do no <- add_instr (T.Istore chunk addr rl r nd);
  do ns <- transl_expr b map r no;
  transl_exprlist al map rl ns).
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family CminorSel.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
| Stailcall: signature -> expr + ident -> exprlist -> stmt.                                                           
FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
| Itailcall: signature -> reg + ident -> list reg -> instruction.

FEnd RTL.

Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

Inherit alloc_regs.
From Rocqet Require Import RTLmonad.

FDefinition alloc_optreg : mapping -> option ident -> mon reg := fun map dest =>
  match dest with
  | Some id => find_var map id
  | None => new_reg
  end.

FRecursion transl_stmt.
Case Scall optid sig expr_ident cl :=
 (fun map nd nexits ngoto nret rret =>
    match expr_ident with
     | inl b => 
        do rf <- alloc_reg b map;
        do rargs <- alloc_regs cl map;
        do r <- alloc_optreg map optid;
        do n1 <- add_instr (T.Icall sig (inl _ rf) rargs r nd);
        do n2 <- transl_exprlist cl map rargs n1;
        transl_expr b map rf n2
    | (inr id) =>
        do rargs <- alloc_regs cl map;
        do r <- alloc_optreg map optid;
        do n1 <- add_instr (T.Icall sig (inr _ id) rargs r nd);
        transl_exprlist cl map rargs n1
     end).
Case Stailcall sig expr_ident cl :=
(fun map nd nexits ngoto nret rret =>
     match expr_ident with 
     | inl b =>
         do rf <- alloc_reg b map;
         do rargs <- alloc_regs cl map;
         do n1 <- add_instr (T.Itailcall sig (inl _ rf) rargs);
         do n2 <- transl_exprlist cl map rargs n1;
         transl_expr b map rf n2
     | (inr id) =>
         do rargs <- alloc_regs cl map;
         do n1 <- add_instr (T.Itailcall sig (inr _ id) rargs);
         transl_exprlist cl map rargs n1
     end).         
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait CminorSel_Switch extends CminorSel.

Inherit expr.

MetaData exitexpr.
Inductive exitexpr : Type :=
  | XEexit: nat -> exitexpr
  | XEjumptable: self__CminorSel_Switch.expr -> list nat -> exitexpr
  | XEcondition: self__CminorSel_Switch.condexpr -> exitexpr -> exitexpr -> exitexpr
  | XElet: self__CminorSel_Switch.expr -> exitexpr -> exitexpr.
FEnd exitexpr.

FInductive stmt : Type := 
| Sswitch: exitexpr -> stmt.
FEnd CminorSel_Switch.

Family CminorSel extends CminorSel_Switch.
FEnd CminorSel.

Trait RTLgen_Switch extends RTLgen.

Inherit labelmap.

From Rocqet Require Import RTLmonad.

Inherit transl_exit.

MetaData transl_jumptable.
Fixpoint transl_jumptable (nexits: list self__RTLgen_Switch.T.node) (tbl: list nat) : self__RTLgen_Switch.mon (list self__RTLgen_Switch.T.node) :=
  match tbl with
  | nil => ret nil
  | t1 :: tl =>
      do n1 <- self__RTLgen_Switch.transl_exit nexits t1;
      do nl <- transl_jumptable nexits tl;
      ret (n1 :: nl)
  end.
FEnd transl_jumptable.

MetaData transl_exitexpr.
Fixpoint transl_exitexpr (map: mapping) (a: self__RTLgen_Switch.S.exitexpr) (nexits: list self__RTLgen_Switch.T.node)
                         {struct a} : self__RTLgen_Switch.mon self__RTLgen_Switch.T.node :=
  match a with
  | self__RTLgen_Switch.S.XEexit n =>
      self__RTLgen_Switch.transl_exit nexits n
  | self__RTLgen_Switch.S.XEjumptable a tbl =>
      do r <- self__RTLgen_Switch.alloc_reg a map;
      do tbl' <- self__RTLgen_Switch.transl_jumptable nexits tbl;
      do n1 <- self__RTLgen_Switch.add_instr (self__RTLgen_Switch.T.Ijumptable r tbl');
         self__RTLgen_Switch.transl_expr a map r n1
  | self__RTLgen_Switch.S.XEcondition a b c =>
      do nc <- transl_exitexpr map c nexits;
      do nb <- transl_exitexpr map b nexits;
         self__RTLgen_Switch.transl_condexpr a map nb nc
  | self__RTLgen_Switch.S.XElet a b =>
      do r <- self__RTLgen_Switch.new_reg;
      do n1 <- transl_exitexpr (self__RTLgen_Switch.add_letvar map r) b nexits;
         self__RTLgen_Switch.transl_expr a map r n1
  end.
FEnd transl_exitexpr.

FRecursion transl_stmt.
Case Sswitch a := (fun map nd nexits ngoto nret rret => transl_exitexpr map a nexits).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sswitch a := (fun lm => ret lm).
FEnd reserve_labels.
FEnd RTLgen_Switch.

Family RTLgen extends RTLgen_Switch.
FEnd RTLgen.

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

Family RTLgen.
Final Family S := CminorSel.
Final Family T := RTL.
FEnd RTLgen.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction Comp.RTLgen.
           
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
