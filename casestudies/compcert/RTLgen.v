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

(** * Reasoning over monadic computations *)

(** The [monadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
    By definition of the bind operation, both computations [a] and
    [b] must succeed for their composition to succeed.  The tactic
    therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
*)

Ltac FmonadInv1 H :=
  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (FmonadInv1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (FmonadInv1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X; [try (FmonadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; simpl negb in H; [discriminate | try (FmonadInv1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (FmonadInv1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac FmonadInv H :=
  FmonadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  | (?F _ = OK _) =>
      ((progress fsimpl in H) || unfold F in H); FmonadInv1 H
  end.

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

(* Semantics for allocation of variables and binding of parameters at function entry. *)
FOpaque Definition free_fenv : mem -> fenv -> function -> option mem := cheat.            
FOpaque Definition alloc_fenv : fenv -> mem -> function -> fenv -> mem -> Prop := cheat.
       
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

FDefinition set_optvar : option ident -> val -> env -> env := fun optid v e =>
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.
            
FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.
                   
MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State:(* Execution within a function *)
      forall (f: function)(* currently executing function *)
             (s: stmt)(* statement under consideration *)
             (k: cont)(* its continuation -- what to do next *)
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

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont)) by _rect.
Case Sseq s1 s2 :=
  (fun lbl k =>
     match find_label s1 lbl (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Slabel lbl' s' := (fun lbl k => if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
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
| step_assign: forall ge f id a k e le m v,
    eval_expr ge e le m nil a v ->
    step ge (State f (Sassign id a) k e le m)
      E0 (State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
    step ge (State f (Sseq s1 s2) k e le m)
      E0 (State f s1 (Kseq s2 k) e le m)              
| step_return_0: forall ge f k e le m m',                       
    free_fenv m e f = Some m' ->
    step ge (State f (Sreturn None) k e le m)
      E0 (Returnstate Vundef (call_cont k) m')            
| step_return_1: forall ge f a k e le m v m',
    eval_expr ge e le m nil a v ->
    free_fenv m e f = Some m' ->
    step ge (State f (Sreturn (Some a)) k e le m)
      E0 (Returnstate v (call_cont k) m')
| step_goto: forall ge f lbl k sp e m s' k',
      find_label (function_body f) lbl (call_cont k) = Some(s', k') ->
      step ge (State f (Sgoto lbl) k sp e m)
        E0 (State f s' k' sp e m)      
| step_internal_function: forall ge f vargs k m m1 sp le,                                               
    alloc_fenv empty_fenv m f sp m1 ->
    init_env f vargs = le ->                        
     step ge (Callstate (AST.Internal f) vargs k m)
       E0 (State f (function_body f) k sp le m1).
            
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
Inductive final_state: self__Cfam.state -> int -> Prop :=
| final_state_intro: forall r m,
   final_state (Returnstate (Vint r) Kstop m) r.
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

Family RTL.
FDefinition node := positive.

From Rocqet Require Import Registers.
      
FInductive instruction: Type :=
| Inop: node -> instruction
| Iop: operation -> list reg -> reg -> node -> instruction          
| Icond: condition -> list reg -> node -> node -> instruction
| Ireturn: option reg -> instruction.

FDefinition code: Type := PTree.t instruction.

MetaData function binds fn_sig, fn_params, fn_stacksize, fn_code, fn_entrypoint.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.
FEnd function.

FDefinition fundef := AST.fundef function.

FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => fn_sig f
  | AST.External ef => ef_sig ef
  end.

(* operational semantics *)             
FDefinition genv := Genv.t fundef unit.
FDefinition regset := Regmap.t val.

MetaData init_regs.
Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.
FEnd init_regs.

MetaData stackframe binds Stackframe.
Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)(* where to store the result *)
             (f: function)(* calling function *)
             (sp: val)(* stack pointer in calling function *)
             (pc: node)(* program point in calling function *)
             (rs: regset),(* register state in calling function *)
      stackframe.
FEnd stackframe.

MetaData state binds State, Callstate, Returnstate.
Inductive state : Type :=
  | State:
      forall (stack: list stackframe)(* call stack *)
             (f: function)(* current function *)
             (sp: val)(* stack pointer *)
             (pc: node)(* current program point in c *)
             (rs: regset)(* register state *)
             (m: mem),(* memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)(* call stack *)
             (f: fundef)(* function to call *)
             (args: list val)(* arguments to the call *)
             (m: mem),(* memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)(* call stack *)
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
| exec_function_internal:
    forall ge s f args m m' stk,
    Mem.alloc m 0 (fn_stacksize f) = (m', stk) ->
    step ge (Callstate s (AST.Internal f) args m)
      E0 (State s
                f
                (Vptr stk Ptrofs.zero)
                (fn_entrypoint f)
                (init_regs args (fn_params f))
                m')      
| exec_return:
    forall ge res f sp pc rs s vres m,
    step ge (Returnstate (Stackframe res f sp pc rs :: s) vres m)
      E0 (State s f sp pc (rs#res <- vres) m).

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    funsig f = signature_main ->
    initial_state p (Callstate nil f nil m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
   | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.
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
                  {struct names} : mon (list reg * mapping) :=
  match names with
  | nil => ret (nil, map)
  | n1 :: nl =>
      do (rl, map1) <- add_vars map nl;
      do (r1, map2) <- add_var map1 n1;
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

FDefinition reg_valid : reg -> state -> Prop := fun r s =>
  Plt r s.(st_nextreg T.instruction).

FDefinition regs_valid : list reg -> state -> Prop := fun rl s =>
  forall r, In r rl -> reg_valid r s.

FDefinition reg_fresh : reg -> state -> Prop := fun r s =>
  ~(Plt r s.(st_nextreg T.instruction)).

FDefinition reg_in_map : mapping -> reg -> Prop := fun (m: mapping) (r: reg) =>
  (exists id, m.(map_vars)!id = Some r) \/ In r m.(map_letvars).

FDefinition map_valid : mapping -> state -> Prop := fun m s =>
  forall r, reg_in_map m r -> reg_valid r s.

FLemma add_vars_valid:
  forall namel s1 s2 map1 map2 rl i,
  add_vars map1 namel s1 = OK (rl, map2) s2 i ->
  map_valid map1 s1 ->
  regs_valid rl s2 /\ map_valid map2 s2.
FProofLemma. apply cheat. Qed. CloseFLemma.

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

(* translation meets spec *)
FLemma init_mapping_valid:
  forall s, map_valid init_mapping s.
FProofLemma.
unfold map_valid, init_mapping.
  intros s r [[id A] | B].
  simpl in A. rewrite PTree.gempty in A; discriminate.
  simpl in B. tauto.
Qed. CloseFLemma.
  
FLemma transl_function_charact:
  forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
FProofLemma.
  intros until tf. unfold transl_function.
  caseEq (transl_fun f init_state). congruence.
  intros [nentry rparams] sfinal INCR TR E. inv E.
  apply cheat.
  (*FmonadInv TR.
  exploit add_vars_valid. eexact EQ1. apply init_mapping_valid.
  intros [A B].
  exploit add_vars_valid. eexact EQ0. auto.
  intros [C D].
  eapply tr_function_intro; eauto with rtlg.
  eapply transl_stmt_charact; eauto with rtlg.
  unfold ret_reg. destruct (rettype_eq (sig_res (CminorSel.fn_sig f)) Tvoid).
  constructor.
  constructor; eauto with rtlg.*)
Qed. CloseFLemma.

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

FInductive tr_cont: T.code -> mapping ->
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

Closing Fact match_stacks_inv : forall k l,
    match_stacks k l ->
    k = S.Kstop /\
    l = nil
    by { apply cheat }.      

(* We can prove this easily with FInduction *)
Closing Fact tr_cont_inversion : forall c map k nd nexits ngoto nret rret cs,
  tr_cont c map k nd nexits ngoto nret rret cs -> 
  (exists n s k0,
      k = (S.Kseq s k0) /\
      tr_stmt c map s nd n nexits ngoto nret rret /\
        tr_cont c map k n nexits ngoto nret rret cs)
  \/
    (nd = nret /\
     k = S.Kstop /\
     nexits = nil /\
     c!nret = Some(T.Ireturn rret) /\
       match_stacks S.Kstop cs)
  by { apply cheat }.
  
Closing Fact tr_cont_tr_kseq_inv :
  forall c map s k nd nexits ngoto nret rret cs,
    tr_cont c map (S.Kseq s k) nd nexits ngoto nret rret cs ->
    exists n,
      tr_stmt c map s nd n nexits ngoto nret rret /\
      tr_cont c map k n nexits ngoto nret rret cs
      by plain { intros until cs; intros H; inv H; eauto }.


FLemma tr_move_correct:
  forall tge r1 ns r2 nd cs f sp rs m,
  tr_move (T.fn_code f) ns r1 nd r2 ->
  exists rs',
  star T.step tge (T.State cs f sp ns rs m) E0 (T.State cs f sp nd rs' m) /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
FProofLemma.
  intros. inv H.
  exists rs; split. constructor. auto.
  exists (rs#r2 <- (rs#r1)); split.
  apply star_one. eapply T.exec_Iop. eauto. auto.
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed. CloseFLemma.

MetaData map_wf.
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

FLemma init_mapping_wf:
  map_wf init_mapping.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_var_wf:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_vars_wf:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_letvar_wf:
  forall map r,
  map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
FProofLemma. apply cheat. Qed. CloseFLemma.

MetaData match_env.
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

FLemma match_env_find_var:
  forall map e le rs id v r,
  match_env map e le rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  Val.lessdef v rs#r.
FProofLemma.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed. CloseFLemma.

FLemma match_env_invariant:
  forall map e le rs rs',
  match_env map e le rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env map e le rs'.
FProofLemma.
  intros. inversion H. apply mk_match_env.
  intros. exploit me_vars0; eauto. intros [r [A B]].
  exists r; split. auto. rewrite H0; auto. left; exists id; auto.
  replace (rs'##(map_letvars map)) with (rs ## (map_letvars map)). auto.
  apply list_map_exten. intros. apply H0. right; auto.
Qed. CloseFLemma.

FLemma match_env_update_temp:
  forall map e le rs r v,
  match_env map e le rs ->
  ~(reg_in_map map r) ->
  match_env map e le (rs#r <- v).
FProofLemma.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro.
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed. CloseFLemma.
(*Global Hint Resolve match_env_update_temp: rtlg.*)

FLemma match_env_update_var:
  forall map e le rs id r v tv,
  Val.lessdef v tv ->
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env map e le rs ->
  match_env map (PTree.set id v e) le (rs#r <- tv).
FProofLemma.
  intros. inversion H0. inversion H2. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H3. exists r; split. auto. rewrite PMap.gss. auto.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'. elim n. eauto.
  erewrite list_map_exten. eauto.
  intros. symmetry. apply PMap.gso. red; intros. subst x. eauto.
Qed. CloseFLemma.

FLemma match_env_update_dest:
  forall map e le rs dst r v tv,
  Val.lessdef v tv ->
  map_wf map ->
  reg_map_ok map r dst ->
  match_env map e le rs ->
  match_env map (S.set_optvar dst v e) le (rs#r <- tv).
FProofLemma.
  intros. inv H1; simpl.
  eapply match_env_update_temp; eauto.
  eapply match_env_update_var; eauto.
Qed. CloseFLemma.
(* Global Hint Resolve match_env_update_dest: rtlg.*)

FLemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl tvl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  Val.lessdef_list vl tvl ->
  match_env map2 (S.set_params vl il) nil (T.init_regs tvl rl)
  /\ (forall r, reg_fresh r s2 -> (T.init_regs tvl rl)#r = Vundef).
FProofLemma.
apply cheat.
Qed. CloseFLemma.

FLemma match_set_locals:
  forall map1 s1,
  map_wf map1 ->
  forall il rl map2 s2 e le rs i,
  match_env map1 e le rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env map2 (S.set_locals il e) le rs.
FProofLemma.
apply cheat.
Qed. CloseFLemma.

FLemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  Val.lessdef_list vparams tvparams ->
  match_env map2 (S.set_locals vars (S.set_params vparams params))
    nil (T.init_regs tvparams rparams).
FProofLemma.
intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed. CloseFLemma.  

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Closing Fact tr_expr_tr_evar_inv : forall c map pr id ns nd rd dst,
   tr_expr c map pr (S.Evar id) ns nd rd dst ->
   exists r, 
   map.(map_vars)!id = Some r /\
   (((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr))) /\
   tr_move c ns r nd rd
   by plain { intros until dst; intros H; inv H; eauto }.    

FInduction transl_expr_correct about S.eval_expr motive
   (fun ge sp e m le a v
     (_ : S.eval_expr ge sp e m le a v) =>
   forall prog tprog tge, match_prog prog tprog ->
   ge = Genv.globalenv prog ->
   tge = Genv.globalenv tprog -> 
   forall tm cs f map pr ns nd rd rs dst   
   (TE : tr_expr (T.fn_code f) map pr a ns nd rd dst)
   (MWF: map_wf map)  
   (ME: match_env map e le rs)
   (EXT: Mem.extends m tm),
      exists rs', exists tm',
         star T.step tge (T.State cs f (Vptr sp Ptrofs.zero) ns rs tm) E0 (T.State cs f (Vptr sp Ptrofs.zero) nd rs' tm')
      /\ match_env map (S.set_optvar dst v e) le rs'
      /\ Val.lessdef v rs'#rd
      /\ (forall r, In r pr -> rs'#r = rs#r)
         /\ Mem.extends m tm')
   
with transl_exprlist_correct about S.eval_exprlist motive
  (fun ge sp e m le al vl
       (_ : S.eval_exprlist ge sp e m le al vl) =>
      forall prog tprog tge, match_prog prog tprog ->
      ge = Genv.globalenv prog ->
      tge = Genv.globalenv tprog -> 
      forall tm cs f map pr ns nd rl rs
      (MWF: map_wf map)
      (TE: tr_exprlist (T.fn_code f) map pr al ns nd rl)
      (ME: match_env map e le rs)
      (EXT: Mem.extends m tm),
      exists rs', exists tm',
         star T.step tge (T.State cs f (Vptr sp Ptrofs.zero) ns rs tm) E0 (T.State cs f (Vptr sp Ptrofs.zero) nd rs' tm')
      /\ match_env map e le rs'
      /\ Val.lessdef_list vl rs'##rl
      /\ (forall r, In r pr -> rs'#r = rs#r)
      /\ Mem.extends m tm')

with transl_condexpr_correct about S.eval_condexpr motive
  (fun ge sp e m le a v
     (_ : S.eval_condexpr ge sp e m le a v) =>
    forall prog tprog tge, match_prog prog tprog ->
    ge = Genv.globalenv prog ->
    tge = Genv.globalenv tprog ->  
    forall tm cs f map pr ns ntrue nfalse rs
    (MWF: map_wf map)
    (TE: tr_condition (T.fn_code f) map pr a ns ntrue nfalse)
    (ME: match_env map e le rs)
    (EXT: Mem.extends m tm),
    exists rs', exists tm',
       plus T.step tge (T.State cs f (Vptr sp Ptrofs.zero) ns rs tm) E0 (T.State cs f (Vptr sp Ptrofs.zero) (if v then ntrue else nfalse) rs' tm')
    /\ match_env map e le rs'
    /\ (forall r, In r pr -> rs'#r = rs#r)
    /\ Mem.extends m tm').     
FProof.

(* Evar *)
+ intros; (*red*) intros. apply tr_expr_tr_evar_inv in TE; unpack TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]].
  exists rs'; exists tm; split. eauto.
  destruct TEMP as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto.
  split. eapply match_env_invariant; eauto.
  split. congruence.
  split; auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto.
  split. congruence.
  split. intros. apply C. intuition congruence.
  auto.

(* Eop *)  
+ apply cheat.

(* Econdition *)  
+ apply cheat.

(* Elet *)  
+ apply cheat.

(* Eletvar *)  
+ apply cheat.

(* Enil *)  
+ apply cheat.

(* Econs *)  
+ apply cheat.

(* CEcond *)  
+ apply cheat.

(* CEcondition *)  
+ apply cheat.

(* CElet *)  
+ apply cheat.  
Qed. FEnd transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.

MetaData match_states.
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
intros. unfold lt_state. simpl. destruct H as [A | [A B]].
  left. auto. rewrite A. right. auto. 
Qed. CloseFLemma.

MetaData Lt_state.
Ltac Lt_state :=  
  apply lt_state_intro; do 2 fsimpl; simpl; try lia.
FEnd Lt_state.

Closing Fact tr_stmt_skip_inv: 
  forall c map ns ncont nexits ngoto nret rret,
  tr_stmt c map S.Sskip ns ncont nexits ngoto nret rret -> 
  ncont = ns 
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_assign_inv :
  forall id a c map ns nd nexits ngoto nret rret,
  tr_stmt c map (S.Sassign id a) ns nd nexits ngoto nret rret ->
  exists r,
    map.(map_vars)!id = Some r /\
    tr_expr c map nil a ns nd r (Some id)
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sseq_inv : 
  forall c map s1 s2 ns nd nexits ngoto nret rret,
  tr_stmt c map (S.Sseq s1 s2) ns nd nexits ngoto nret rret ->
  exists n,  
  tr_stmt c map s2 n nd nexits ngoto nret rret /\
  tr_stmt c map s1 ns n nexits ngoto nret rret 
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sifthenelse_inv :
  forall c map a strue sfalse ns nd nexits ngoto nret rret,
  tr_stmt c map (S.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret ->
  exists ntrue nfalse,  
  tr_stmt c map strue ntrue nd nexits ngoto nret rret /\
  tr_stmt c map sfalse nfalse nd nexits ngoto nret rret /\
  tr_condition c map nil a ns ntrue nfalse
  by plain { intros until rret; intros H; inv H; eauto }.       

Closing Fact tr_stmt_sreturn_none_inv : 
  forall c map ns nd nexits ngoto nret rret,
  tr_stmt c map (S.Sreturn None) ns nd nexits ngoto nret rret ->
  ns = nret
  by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sreturn_some_inv :
  forall c map a ns nd nexits ngoto nret rret,
  tr_stmt c map (S.Sreturn (Some a)) ns nd nexits ngoto nret rret ->
  exists rret0, 
  tr_expr c map nil a ns nret rret0 None /\ rret = Some rret0
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sgoto_inv :
  forall c map lbl ns nd nexits ngoto nret rret,
    tr_stmt c map (S.Sgoto lbl) ns nd nexits ngoto nret rret ->
    ngoto!lbl = Some ns
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_slabel_inv :
  forall c map lbl s ns nd nexits ngoto nret rret,
    tr_stmt c map (S.Slabel lbl s) ns nd nexits ngoto nret rret  ->
    exists n,
      ngoto!lbl = Some n /\
      c!n = Some (T.Inop ns) /\
      tr_stmt c map s ns nd nexits ngoto nret rret  
    by plain { intros until rret; intros H; inv H; eauto }.             
          
Closing Fact Kseq_inv : forall s0 k0 s k,
    self__RTLgen.S.Kseq s0 k0 = self__RTLgen.S.Kseq s k -> 
    s0 = s /\ k0 = k
  by plain { intros until k; intros H; inversion H; eauto }.

Closing Fact stop_kseq_discriminate: forall s k, S.Kstop = S.Kseq s k -> False
    by plain { intros until k; intros H; discriminate }.

FInduction match_stacks_call_cont about tr_cont motive
  (fun c map k ncont nexits ngoto nret rret cs
       (_ : tr_cont c map k ncont nexits ngoto nret rret cs) =>
       match_stacks (S.call_cont k) cs /\ c!nret = Some(T.Ireturn rret)).
FProof.
all: intros; fsimpl; auto.
Qed. FEnd match_stacks_call_cont.

FInduction tr_cont_call_cont about tr_cont motive 
  (fun c map k ncont nexits ngoto nret rret cs
    (_ : tr_cont c map k ncont nexits ngoto nret rret cs) =>
    tr_cont c map (S.call_cont k) nret nil ngoto nret rret cs).
FProof.
all: intros; fsimpl; auto; fconstructor; eauto.
Qed. FEnd tr_cont_call_cont.

FInduction tr_find_label about S.stmt motive
  (fun (s : S.stmt) =>
    forall c map lbl n (ngoto: labelmap) nret rret s' k' cs,
    ngoto!lbl = Some n ->
    forall k ns1 nd1 nexits1,
    S.find_label s lbl k = Some (s', k') ->
    tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
    tr_cont c map k nd1 nexits1 ngoto nret rret cs ->
    exists ns2, exists nd2, exists nexits2,
       c!n = Some(T.Inop ns2)
    /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
    /\ tr_cont c map k' nd2 nexits2 ngoto nret rret cs).
FProof.
all: intros until nexits1; fsimpl; try congruence.
(* seq *)
+ caseEq (S.find_label __i lbl (S.Kseq __i0 k)); intros.
  inv H3. apply tr_stmt_sseq_inv in H4; unpack H4; subst.
  eapply H; eauto. fconstructor; eauto.
  apply tr_stmt_sseq_inv in H4; unpack H4; subst. eapply H0; eauto.
  
(* label *)
+ destruct (ident_eq lbl l); intros.
  inv H1. apply tr_stmt_slabel_inv in H2; unpack H2; subst.
  assert (n0 = n). change positive with node in TEMP0. congruence. subst n0.
  exists ns1; exists nd1; exists nexits1; auto.
  apply tr_stmt_slabel_inv in H2; unpack H2; subst. eapply H; eauto.

(* ifthenelse *)  
+ caseEq (S.find_label __i lbl k); intros.
  inv H3. apply tr_stmt_sifthenelse_inv in H4; unpack H4; subst.
  eapply H; eauto.
  apply tr_stmt_sifthenelse_inv in H4; unpack H4; subst. eapply H0; eauto.
Qed. FEnd tr_find_label.
                               
FInduction transl_step_correct about S.step
  motive (fun ge S1 t S2 (_ : S.step ge S1 t S2) =>
  forall prog tprog tge, match_prog prog tprog -> 
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall R1 (MS : match_states S1 R1),
  exists R2,
  (plus T.step tge R1 t R2 \/ (star T.step tge R1 t R2 /\ lt_state S2 S1))
  /\ match_states S2 R2).
FProof.
all: intros until tge; intros TRANSL A B; intros R1 MSTATE; inv MSTATE.

(* skip seq *)
+ apply tr_stmt_skip_inv in TS. subst ns.
  apply tr_cont_tr_kseq_inv in TK; unpack TK; subst. 
  econstructor; split.
  right; split. apply star_refl.  
  Lt_state. econstructor; eauto.

(* skip call *)  
+ apply tr_stmt_skip_inv in TS; subst ns. 
  assert ((T.fn_code tf)!ncont = Some(T.Ireturn rret)
          /\ match_stacks k cs).
  apply tr_cont_inversion in TK. destruct TK; unpack H; subst; fsimpl in i;
  try contradiction; auto.                                                             
  destruct H.
  assert (T.fn_stacksize tf = S.fn_stackspace f).
    inv TF. auto.
  edestruct Mem.free_parallel_extends as [tm' []]; eauto.
  econstructor; split.
  left; apply plus_one. eapply T.exec_Ireturn. eauto. 
  rewrite H1. eauto.
  constructor; auto.

(* assign *)
+ apply tr_stmt_assign_inv in TS; unpack TS; subst. 
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D E]]]]]].
  econstructor; split.
  right; split. eauto. Lt_state.
  econstructor; eauto. fconstructor.

(* seq *)  
+ apply tr_stmt_sseq_inv in TS; unpack TS.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. fconstructor; eauto.

(* return none *)
+ apply tr_stmt_sreturn_none_inv in TS; subst. (*ns.*)
  exploit match_stacks_call_cont.  
  instantiate (1 := TK).   
  intros [U V].  
  inversion TF.
  edestruct Mem.free_parallel_extends as [tm'' []]; eauto.
  econstructor; split.
  left; apply plus_one. eapply T.exec_Ireturn; eauto.
  rewrite H1; eauto.
  constructor; auto.
    
(* return some *)  
+ apply tr_stmt_sreturn_some_inv in TS; unpack TS; subst. (*rret.*)
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D E]]]]]].
  exploit match_stacks_call_cont; eauto.
  instantiate (1 := TK).
  intros [U V].
  inversion TF.
  edestruct Mem.free_parallel_extends as [tm'' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eexact A. eapply T.exec_Ireturn; eauto.
  rewrite H1; eauto. traceEq.
  simpl. constructor; auto.

  (* tr_cont (T.fn_code tf) map k ncont nexits ngoto nret (ret_reg (S.fn_sig f) r) cs *)
(* goto *)  
+ apply tr_stmt_sgoto_inv in TS.  inversion TF; subst.
  exploit tr_find_label; eauto.
  apply (tr_cont_call_cont _ _ _ _ _ _ _ _ _ TK); eauto.
  intros [ns2 [nd2 [nexits2 [A [B C]]]]].
  econstructor; split.
  left; apply plus_one. eapply T.exec_Inop; eauto.
  econstructor; eauto.
  
(* internal function *)  
+ monadInv TF. exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0.
  pose (e0 := S.set_locals (S.fn_vars f) (S.set_params vargs (S.fn_params f))).
  pose (rs := T.init_regs targs rparams).
  assert (ME: match_env map2 e0 nil rs).
    unfold rs, e0. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (S.fn_params f)); eauto. intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
  edestruct Mem.alloc_extends as [tm' []]; eauto; try apply Z.le_refl.
  econstructor; split.
  left; apply plus_one. eapply T.exec_function_internal; fsimpl; simpl; eauto.
  fsimpl; simpl. econstructor; eauto.
  econstructor; eauto.
  apply match_stacks_inv in MS; unpack MS; subst.
  (*inversion MS; subst;*) fconstructor; auto. fconstructor.

(* ifthenelse *)  
+ apply tr_stmt_sifthenelse_inv in TS; unpack TS.
  exploit transl_condexpr_correct; eauto. intros [rs' [tm' [A [B [C D]]]]].
  econstructor; split.
  left. eexact A.
  destruct b; econstructor; eauto.
Qed. FEnd transl_step_correct.

(*
Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.
 *)

FLemma function_ptr_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (b: block) (f: S.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply Genv.find_funct_ptr_transf_partial; eauto.
Qed. CloseFLemma.

FLemma symbols_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_symbol_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma sig_transl_function:
  forall (f: S.fundef) (tf: T.fundef),
  transl_fundef f = Errors.OK tf ->
  T.funsig tf = S.funsig f.
FProofLemma.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function.
  case (transl_fun f0 (init_state)); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed. CloseFLemma.

FLemma transl_initial_states: 
  forall prog tprog, match_prog prog tprog -> 
  forall S', S.initial_state prog S' ->
  exists R, T.initial_state tprog R /\ match_states S' R.
FProofLemma.
 induction 2.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  econstructor; split.
  econstructor. apply (Genv.init_mem_transf_partial H); eauto.
  replace (AST.prog_main tprog) with (AST.prog_main prog). rewrite symbols_preserved with (prog:=prog) (tprog:=tprog) (ge:=ge); eauto.
  symmetry; eapply match_program_main; eauto.
  eexact A.
  rewrite <- H3. apply sig_transl_function; auto.
  constructor. auto. constructor.
  constructor. apply Mem.extends_refl.
Qed. CloseFLemma.

FLemma transl_final_states:
  forall S' R r,
  match_states S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma. intros. inv H0. inv H. inv MS. inv LD. constructor. Qed. CloseFLemma.

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
