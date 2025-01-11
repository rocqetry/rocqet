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
    Mem.free m stk 0 (fn_stacksize f) = Some m' ->
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
Family So extends CminorSel. FEnd So.
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

FRecursion alloc_reg about So.expr motive (fun (_ : So.expr) => mapping -> mon reg) by _rect.
Case Evar id := (fun map => find_var map id).
Case Eletvar n := (fun map => find_letvar map n).
Case Eop := (fun op args => fun map => new_reg).
Case Econdition c a0 a1 := (fun map => new_reg).
Case Elet a b := (fun map => new_reg).
FEnd alloc_reg.

FRecursion alloc_regs about So.exprlist motive (fun (_ : So.exprlist) => mapping -> mon (list reg)) by _rect.
Case Enil := (fun map => ret nil).
Case Econs a bl :=
(fun map =>
  do r <- alloc_reg a map;
  do rl <- alloc_regs bl map;
  ret (r :: rl)).
FEnd alloc_regs.

FRecursion transl_expr about So.expr motive (fun (_ : So.expr) => mapping -> reg -> T.node -> mon T.node)
  with transl_exprlist about So.exprlist motive (fun (_ : So.exprlist) => mapping -> list reg -> T.node -> mon T.node)
  with transl_condexpr about So.condexpr motive (fun (_ : So.condexpr) => mapping  -> T.node -> T.node -> mon T.node) by _rect.
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
        
FRecursion transl_stmt about So.stmt motive (fun (_ : So.stmt) => mapping -> T.node -> list T.node -> labelmap -> T.node -> option reg -> mon T.node) by _rect.
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

FDefinition alloc_label : So.label -> labelmap -> mon labelmap :=
  fun (lbl: So.label) (map: labelmap) =>
  do n <- reserve_instr;
  ret (PTree.set lbl n map).   

FRecursion reserve_labels about So.stmt
  motive (fun (_ : So.stmt) => labelmap -> mon labelmap) by _rect.
Case Sseq s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Sifthenelse e s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Slabel lbl s1 := (fun lm => do lm' <- reserve_labels s1 lm; alloc_label lbl lm').
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FDefinition ret_reg : signature -> reg -> option reg :=
  fun (sig: signature) (rd: reg) =>
  if rettype_eq sig.(AST.sig_res) AST.Tvoid then None else Some rd.

FDefinition transl_fun : So.function -> mon (T.node * list reg) :=
  fun (f: So.function) => 
  do ngoto <- reserve_labels (So.fn_body f) (PTree.empty T.node);
  do (rparams, map1) <- add_vars init_mapping (So.fn_params f);
  do (rvars, map2) <- add_vars map1 (So.fn_vars f);
  do rret <- new_reg;
  let orret := ret_reg (So.fn_sig f) rret in
  do nret <- add_instr (T.Ireturn orret);
  do nentry <- transl_stmt (So.fn_body f) map2 nret nil ngoto nret orret;
  ret (nentry, rparams).

FDefinition transl_function : So.function -> Errors.res T.function := 
    fun (f: So.function) => 
  match transl_fun f init_state with
  | Error msg => Errors.Error msg
  | OK (nentry, rparams) s i =>
      Errors.OK (T.mkfunction
                   (So.fn_sig f)
                   rparams
                   (So.fn_stackspace f)
                   s.(st_code T.instruction)
                   nentry)
  end.

FDefinition transl_fundef := transf_partial_fundef transl_function.

FDefinition transl_program : So.program -> Errors.res T.program := 
  fun (p: So.program) =>
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
                 
FInductive tr_expr : T.code -> mapping -> list reg -> So.expr -> T.node -> T.node -> reg -> option AST.ident -> Prop :=
| tr_Evar: forall c map pr id ns nd r rd dst,
    map.(map_vars)!id = Some r ->
    ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
    tr_move c ns r nd rd ->
    tr_expr c map pr (So.Evar id) ns nd rd dst            
| tr_Eop: forall c map pr op al ns nd rd n1 rl dst,
    tr_exprlist c map pr al ns n1 rl ->
    c!n1 = Some (T.Iop op rl rd nd) ->
    reg_map_ok map rd dst -> ~In rd pr ->
    tr_expr c map pr (So.Eop op al) ns nd rd dst            
| tr_Econdition: forall c map pr a ifso ifnot ns nd rd ntrue nfalse dst,
    tr_condition c map pr a ns ntrue nfalse ->
    tr_expr c map pr ifso ntrue nd rd dst ->
    tr_expr c map pr ifnot nfalse nd rd dst ->
    tr_expr c map pr (So.Econdition a ifso ifnot) ns nd rd dst
| tr_Elet: forall c map pr b1 b2 ns nd rd n1 r dst,
    ~reg_in_map map r ->
    tr_expr c map pr b1 ns n1 r None ->
    tr_expr c (add_letvar map r) pr b2 n1 nd rd dst ->
    tr_expr c map pr (So.Elet b1 b2) ns nd rd dst
| tr_Eletvar: forall c map pr n ns nd rd r dst,
    List.nth_error map.(map_letvars) n = Some r ->
    ((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr)) ->
    tr_move c ns r nd rd ->
    tr_expr c map pr (So.Eletvar n) ns nd rd dst
with tr_condition : T.code -> mapping -> list reg -> So.condexpr -> T.node -> T.node -> T.node -> Prop :=
| tr_CEcond: forall c map pr cond bl ns ntrue nfalse n1 rl,
    tr_exprlist c map pr bl ns n1 rl ->
    c!n1 = Some (T.Icond cond rl ntrue nfalse) ->
    tr_condition c map pr (So.CEcond cond bl) ns ntrue nfalse
| tr_CEcondition: forall c map pr a1 a2 a3 ns ntrue nfalse n2 n3,
    tr_condition c map pr a1 ns n2 n3 ->
    tr_condition c map pr a2 n2 ntrue nfalse ->
    tr_condition c map pr a3 n3 ntrue nfalse ->
    tr_condition c map pr (So.CEcondition a1 a2 a3) ns ntrue nfalse
| tr_CElet: forall c map pr a b ns ntrue nfalse r n1,
    ~reg_in_map map r ->
    tr_expr c map pr a ns n1 r None ->
    tr_condition c (add_letvar map r) pr b n1 ntrue nfalse ->
    tr_condition c map pr (So.CElet a b) ns ntrue nfalse
with tr_exprlist : T.code -> mapping -> list reg -> So.exprlist -> T.node -> T.node -> list reg -> Prop :=
| tr_Enil: forall c map pr n,
    tr_exprlist c map pr So.Enil n n nil
| tr_Econs: forall c map pr a1 al ns nd r1 rl n1,
    tr_expr c map pr a1 ns n1 r1 None ->
    tr_exprlist c map (r1 :: pr) al n1 nd rl ->
    tr_exprlist c map pr (So.Econs a1 al) ns nd (r1 :: rl).
    
FInductive tr_stmt : T.code -> mapping -> So.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=
| tr_Sskip: forall c map ns nexits ngoto nret rret,
    tr_stmt c map So.Sskip ns ns nexits ngoto nret rret            
| tr_Sassign: forall c map id a ns nd nexits ngoto nret rret r,
  map.(map_vars)!id = Some r ->
  tr_expr c map nil a ns nd r (Some id) ->
  tr_stmt c map (So.Sassign id a) ns nd nexits ngoto nret rret          
| tr_Sseq: forall c map s1 s2 ns nd nexits ngoto nret rret n,
  tr_stmt c map s2 n nd nexits ngoto nret rret ->
  tr_stmt c map s1 ns n nexits ngoto nret rret ->
  tr_stmt c map (So.Sseq s1 s2) ns nd nexits ngoto nret rret
| tr_Sifthenelse: forall c map a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse,
  tr_stmt c map strue ntrue nd nexits ngoto nret rret ->
  tr_stmt c map sfalse nfalse nd nexits ngoto nret rret ->
  tr_condition c map nil a ns ntrue nfalse ->
  tr_stmt c map (So.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
| tr_Sreturn_none: forall c map nret nd nexits ngoto rret,
  tr_stmt c map (So.Sreturn None) nret nd nexits ngoto nret rret
| tr_Sreturn_some: forall c map a ns nd nexits ngoto nret rret,
  tr_expr c map nil a ns nret rret None ->
  tr_stmt c map (So.Sreturn (Some a)) ns nd nexits ngoto nret (Some rret)
| tr_Slabel: forall c map lbl s ns nd nexits ngoto nret rret n,
  ngoto!lbl = Some n ->
  c!n = Some (T.Inop ns) ->
  tr_stmt c map s ns nd nexits ngoto nret rret ->
  tr_stmt c map (So.Slabel lbl s) ns nd nexits ngoto nret rret
| tr_Sgoto: forall c map lbl ns nd nexits ngoto nret rret,
  ngoto!lbl = Some ns ->
  tr_stmt c map (So.Sgoto lbl) ns nd nexits ngoto nret rret.   

MetaData tr_function.
Inductive tr_function: self__RTLgen.So.function -> self__RTLgen.T.function -> Prop :=
| tr_function_intro:
    forall f code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret,
    self__RTLgen.add_vars self__RTLgen.init_mapping f.(self__RTLgen.So.fn_params) s0 = OK (rparams, map1) s1 i1 ->
    self__RTLgen.add_vars map1 f.(self__RTLgen.So.fn_vars) s1 = OK (rvars, map2) s2 i2 ->
    orret = self__RTLgen.ret_reg f.(self__RTLgen.So.fn_sig) rret ->
    self__RTLgen.tr_stmt code map2 f.(self__RTLgen.So.fn_body) nentry nret nil ngoto nret orret ->
    code!nret = Some(self__RTLgen.T.Ireturn orret) ->
    tr_function f (self__RTLgen.T.mkfunction
                    f.(self__RTLgen.So.fn_sig)
                    rparams
                    f.(self__RTLgen.So.fn_stackspace)
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
                 (f: self__RTLgen.So.function)
                 (ngoto: self__RTLgen.labelmap) (nret: self__RTLgen.T.node) (rret: option reg) : Prop :=
  | tr_fun_intro: forall nentry r,
      rret = self__RTLgen.ret_reg f.(self__RTLgen.So.fn_sig) r ->
      self__RTLgen.tr_stmt tf.(self__RTLgen.T.fn_code) map f.(self__RTLgen.So.fn_body) nentry nret nil ngoto nret rret ->
      tf.(self__RTLgen.T.fn_stacksize) = f.(self__RTLgen.So.fn_stackspace) ->
      tr_fun tf map f ngoto nret rret.
FEnd tr_fun.

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

MetaData match_env.
Record match_env
      (map: mapping) (e: So.env) (le: So.letenv) (rs: T.regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ Val.lessdef v rs#r);
    me_letvars:
      Val.lessdef_list le rs##(map.(map_letvars))
  }.
FEnd match_env.

FInductive tr_cont: T.code -> mapping ->
                   So.cont -> T.node -> list T.node -> labelmap -> T.node -> option reg ->
                   list T.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont c map k n nexits ngoto nret rret cs ->
      tr_cont c map (So.Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(T.Ireturn rret) ->
      match_stacks So.Kstop cs ->
      tr_cont c map So.Kstop nret nil ngoto nret rret cs             
with match_stacks: So.cont -> list T.stackframe -> Prop :=
  | match_stacks_stop:
    match_stacks So.Kstop nil.


(* TODO: This is not really true *)
Closing Fact match_stacks_inv : forall k l,
    match_stacks k l ->
    k = So.Kstop /\
    l = nil
    by { apply cheat }.

Closing Fact match_stacks_stop_inv : forall l,
    match_stacks So.Kstop l ->    
    l = nil
    by { intros l H; inv H; eauto }.      

(* We can prove this easily with FInduction *)
Closing Fact tr_cont_inversion : forall c map k nd nexits ngoto nret rret cs,
  tr_cont c map k nd nexits ngoto nret rret cs -> 
  (exists n s k0,
      k = (So.Kseq s k0) /\
      tr_stmt c map s nd n nexits ngoto nret rret /\
        tr_cont c map k n nexits ngoto nret rret cs)
  \/
    (nd = nret /\
     k = So.Kstop /\
     nexits = nil /\
     c!nret = Some(T.Ireturn rret) /\
       match_stacks So.Kstop cs)
  by { apply cheat }.
  
Closing Fact tr_cont_tr_kseq_inv :
  forall c map s k nd nexits ngoto nret rret cs,
    tr_cont c map (So.Kseq s k) nd nexits ngoto nret rret cs ->
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

FLemma match_env_find_letvar:
  forall map e le rs idx v r,
  match_env map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  Val.lessdef v rs#r.
FProofLemma.
  intros. exploit me_letvars; eauto.
  clear H. revert le H0 H1. generalize (map_letvars map). clear map.
  induction idx; simpl; intros.
  inversion H; subst le; inversion H0. subst v1.
  destruct l; inversion H1. subst r0.
  inversion H2. subst v2. auto.
  destruct l; destruct le; try discriminate.
  eapply IHidx; eauto.
  inversion H. auto.
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
  match_env map (So.set_optvar dst v e) le (rs#r <- tv).
FProofLemma.
  intros. inv H1; simpl.
  eapply match_env_update_temp; eauto.
  eapply match_env_update_var; eauto.
Qed. CloseFLemma.
(* Global Hint Resolve match_env_update_dest: rtlg.*)

FLemma match_env_bind_letvar:
  forall map e le rs r v,
  match_env map e le rs ->
  Val.lessdef v rs#r ->
  match_env (add_letvar map r) e (v :: le) rs.
FProofLemma.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed. CloseFLemma.

FLemma match_env_unbind_letvar:
  forall map e le rs r v,
  match_env (add_letvar map r) e (v :: le) rs ->
  match_env map e le rs.
FProofLemma.
  unfold add_letvar; intros. inv H. simpl in *.
  constructor. auto. inversion me_letvars0. auto.
Qed. CloseFLemma.

FLemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl tvl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  Val.lessdef_list vl tvl ->
  match_env map2 (So.set_params vl il) nil (T.init_regs tvl rl)
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
  match_env map2 (So.set_locals il e) le rs.
FProofLemma.
apply cheat.
Qed. CloseFLemma.

FLemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  Val.lessdef_list vparams tvparams ->
  match_env map2 (So.set_locals vars (So.set_params vparams params))
    nil (T.init_regs tvparams rparams).
FProofLemma.
intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed. CloseFLemma.  

FDefinition match_prog := fun (p: So.program) (tp: T.program) =>
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Closing Fact tr_expr_tr_evar_inv : forall c map pr id ns nd rd dst,
   tr_expr c map pr (So.Evar id) ns nd rd dst ->
   exists r, 
   map.(map_vars)!id = Some r /\
   (((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr))) /\
   tr_move c ns r nd rd
   by plain { intros until dst; intros H; inv H; eauto }.   

Closing Fact tr_expr_tr_eop_inv : forall c map pr op al ns nd rd dst,
   tr_expr c map pr (So.Eop op al) ns nd rd dst ->
   exists n1 rl, 
   tr_exprlist c map pr al ns n1 rl /\
   (c!n1 = Some (T.Iop op rl rd nd)) /\
    reg_map_ok map rd dst /\
    ~In rd pr
     by plain { intros until dst; intros H; inv H; eauto }.

Closing Fact tr_expr_tr_econdition_inv : forall c map pr a ifso ifnot ns nd rd dst,
    tr_expr c map pr (So.Econdition a ifso ifnot) ns nd rd dst ->
    exists ntrue nfalse,
      tr_condition c map pr a ns ntrue nfalse /\
      tr_expr c map pr ifso ntrue nd rd dst /\
      tr_expr c map pr ifnot nfalse nd rd dst
      by plain { intros until dst; intros H; inv H; eauto }.      

Closing Fact tr_expr_tr_elet_inv : forall c map pr b1 b2 ns nd rd dst,
    tr_expr c map pr (So.Elet b1 b2) ns nd rd dst ->
    exists r n1,
      ~reg_in_map map r /\
      tr_expr c map pr b1 ns n1 r None /\
      tr_expr c (add_letvar map r) pr b2 n1 nd rd dst
      by plain { intros until dst; intros H; inv H; eauto }.

Closing Fact tr_expr_tr_eletvar_inv : forall c map pr n ns nd rd dst,
    tr_expr c map pr (So.Eletvar n) ns nd rd dst ->
    exists r, 
    List.nth_error map.(map_letvars) n = Some r /\
    (((rd = r /\ dst = None) \/ (reg_map_ok map rd dst /\ ~In rd pr))) /\
    tr_move c ns r nd rd
      by plain { intros until dst; intros H; inv H; eauto }.

Closing Fact tr_exprlist_tr_enil_inv : forall c map pr ns nd rl,
    tr_exprlist c map pr So.Enil ns nd rl ->
    ns = nd /\ rl = nil          
    by plain { intros until rl; intros H; inv H; eauto }.

Closing Fact tr_exprlist_tr_econs_inv : forall c map pr a1 al ns nd rl,
    tr_exprlist c map pr (So.Econs a1 al) ns nd rl ->
    exists r1 rl' n1,
      rl = r1 :: rl' /\
      tr_expr c map pr a1 ns n1 r1 None /\
      tr_exprlist c map (r1 :: pr) al n1 nd rl'
    by plain { intros until rl; intros H; inv H; eauto }.                 

Closing Fact tr_cond_tr_cecond_inv : forall c map pr cond bl ns ntrue nfalse,
    tr_condition c map pr (So.CEcond cond bl) ns ntrue nfalse ->
    exists n1 rl,
    tr_exprlist c map pr bl ns n1 rl /\
    c!n1 = Some (T.Icond cond rl ntrue nfalse)
    by plain { intros until nfalse; intros H; inv H; eauto }.                  

Closing Fact tr_cond_tr_cecondition_inv : forall c map pr a1 a2 a3 ns ntrue nfalse,
    tr_condition c map pr (So.CEcondition a1 a2 a3) ns ntrue nfalse ->
    exists n2 n3, 
      tr_condition c map pr a1 ns n2 n3 /\
      tr_condition c map pr a2 n2 ntrue nfalse /\
      tr_condition c map pr a3 n3 ntrue nfalse 
    by plain { intros until nfalse; intros H; inv H; eauto }.                   

Closing Fact tr_cond_tr_celet_inv : forall c map pr a b ns ntrue nfalse,
    tr_condition c map pr (So.CElet a b) ns ntrue nfalse ->
    exists r n1,
      ~reg_in_map map r /\
      tr_expr c map pr a ns n1 r None /\
      tr_condition c (add_letvar map r) pr b n1 ntrue nfalse
    by plain { intros until nfalse; intros H; inv H; eauto }.       

FLemma function_ptr_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (b: block) (f: So.fundef),
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
  forall (f: So.fundef) (tf: T.fundef),
  transl_fundef f = Errors.OK tf ->
  T.funsig tf = So.funsig f.
FProofLemma.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function.
  case (transl_fun f0 (init_state)); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed. CloseFLemma.

FInduction transl_expr_correct about So.eval_expr motive
   (fun ge sp e m le a v
     (_ : So.eval_expr ge sp e m le a v) =>
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
      /\ match_env map (So.set_optvar dst v e) le rs'
      /\ Val.lessdef v rs'#rd
      /\ (forall r, In r pr -> rs'#r = rs#r)
         /\ Mem.extends m tm')
   
with transl_exprlist_correct about So.eval_exprlist motive
  (fun ge sp e m le al vl
       (_ : So.eval_exprlist ge sp e m le al vl) =>
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

with transl_condexpr_correct about So.eval_condexpr motive
  (fun ge sp e m le a v
     (_ : So.eval_condexpr ge sp e m le a v) =>
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
+ intros; (* red; *) intros. apply tr_expr_tr_eop_inv in TE; unpack TE; subst.
(* normal case *)
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
  edestruct eval_operation_lessdef as [v' []]; eauto.
  exists (rs1#rd <- v'); exists tm1.
(* Exec *)
  split. eapply star_right. eexact EX1.
  eapply T.exec_Iop; eauto.
  rewrite (@eval_operation_preserved So.fundef _ _ _ (Genv.globalenv prog) (Genv.globalenv tprog)). eauto.
  exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) H0 eq_refl eq_refl). traceEq.
(* Match-env *)
  split. eauto using match_env_update_temp, match_env_update_dest.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.

(* Econdition *)  
+  intros; (*red;*) intros. apply tr_expr_tr_econdition_inv in TE; unpack TE. 
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 EXT1]]]]].
  assert (tr_expr (T.fn_code f) map pr (if va then b else c) (if va then ntrue else nfalse) nd rd dst).
    destruct va; auto.
  exploit H0; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply star_trans. apply plus_star. eexact EX1. eexact EX2. traceEq.
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r); auto.
(* Mem *)
  auto.

(* Elet *)  
+ intros; (*red;*) intros; apply tr_expr_tr_elet_inv in TE; unpack TE; subst.
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H0; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [EX2 [ME3 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r0); auto.
(* Mem *)
  auto.  

(* Eletvar *)  
+ intros; (*red;*) intros; apply tr_expr_tr_eletvar_inv in TE; unpack TE; subst. 
  exploit tr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1; exists tm.
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split.
  destruct TEMP as [[A B] | [A B]].
  subst r dst; simpl.
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto.
(* Other regs *)
  split. intros.
  destruct TEMP as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
(* Mem *)
  auto.  

(* Enil *)  
+ intros; (*red;*) intros; apply tr_exprlist_tr_enil_inv in TE; unpack TE; subst.
  exists rs; exists tm.
  split. apply star_refl.
  split. assumption.
  split. constructor.
  auto. 

(* Econs *)  
+ intros; (*red;*) intros; apply tr_exprlist_tr_econs_inv in TE; unpack TE; subst.
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
  exploit H0; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. constructor. rewrite OTHER2. auto.
  simpl; tauto.
  auto.
(* Other regs *)
  split. intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto.
  apply OTHER1; auto.
(* Mem *)
  auto.

(* CEcond *)  
+ intros; (*red;*) intros. apply tr_cond_tr_cecond_inv in TE; unpack TE; subst.
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
  exists rs1; exists tm1.
(* Exec *)
  split. eapply plus_right. eexact EX1. eapply T.exec_Icond. eauto.
  eapply eval_condition_lessdef; eauto. auto. traceEq.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. assumption.
(* Mem *)
  auto.

(* CEcondition *)  
+ intros; (*red;*) intros. apply tr_cond_tr_cecondition_inv in TE; unpack TE; subst. 
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 EXT1]]]]].
  assert (tr_condition (T.fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
    destruct va; auto.
  exploit H0; eauto. intros [rs2 [tm2 [EX2 [ME2 [OTHER2 EXT2]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply plus_trans. eexact EX1. eexact EX2. traceEq.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
(* Mem *)
  auto.

(* CElet *)  
+ intros; (*red;*) intros. apply tr_cond_tr_celet_inv in TE; unpack TE; subst.
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H0; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [EX2 [ME3 [OTHER2 EXT2]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply star_plus_trans. eexact EX1. eexact EX2. traceEq.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
(* Mem *)
  auto.
Qed. FEnd transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.

MetaData match_states.
Inductive match_states: So.state -> T.state -> Prop :=
  | match_state:
      forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret
        (MWF: map_wf map)
        (TS: tr_stmt tf.(T.fn_code) map s ns ncont nexits ngoto nret rret)
        (TF: tr_fun tf map f ngoto nret rret)
        (TK: tr_cont tf.(T.fn_code) map k ncont nexits ngoto nret rret cs)
        (ME: match_env map e nil rs)
        (MEXT: Mem.extends m tm),
      match_states (So.State f s k sp e m)
                   (T.State cs tf (Vptr sp Ptrofs.zero) ns rs tm)
  | match_callstate:
      forall f args targs k m tm cs tf
        (TF: transl_fundef f = Errors.OK tf)
        (MS: match_stacks k cs)
        (LD: Val.lessdef_list args targs)
        (MEXT: Mem.extends m tm),
      match_states (So.Callstate f args k m)
                   (T.Callstate cs tf targs tm)
  | match_returnstate:
      forall v tv k m tm cs
        (MS: match_stacks k cs)
        (LD: Val.lessdef v tv)
        (MEXT: Mem.extends m tm),
      match_states (So.Returnstate v k m)
        (T.Returnstate cs tv tm).
FEnd match_states.

FRecursion size_stmt about So.stmt motive (fun (_ : So.stmt) => nat) by _rect.
Local Open Scope nat_scope.
Case Sskip := 0.
Case Sseq s1 s2 := (size_stmt s1 + size_stmt s2 + 1).
Case Sifthenelse c s1 s2 := (size_stmt s1 + size_stmt s2 + 1).
Case Slabel lbl s1 := (size_stmt s1 + 1).
Case _ := 1.
FEnd size_stmt.

FRecursion size_cont about So.cont motive (fun (_ : So.cont) => nat) by _rect.
Case Kseq s k1 := (size_stmt s + size_cont k1 + 1).
Case _ := 0.
FEnd size_cont.

FDefinition measure_state := fun (s: So.state) =>
  match s with
  | self__RTLgen.So.State _ s k _ _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _ => (0, 0)
  end.

FDefinition lt_state := fun (S1 S2: So.state) =>
  lex_ord lt lt (measure_state S1) (measure_state S2).

FLemma lt_state_intro:
  forall f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (So.State f1 s1 k1 sp1 e1 m1)
           (So.State f2 s2 k2 sp2 e2 m2).
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
  tr_stmt c map So.Sskip ns ncont nexits ngoto nret rret -> 
  ncont = ns 
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_assign_inv :
  forall id a c map ns nd nexits ngoto nret rret,
  tr_stmt c map (So.Sassign id a) ns nd nexits ngoto nret rret ->
  exists r,
    map.(map_vars)!id = Some r /\
    tr_expr c map nil a ns nd r (Some id)
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sseq_inv : 
  forall c map s1 s2 ns nd nexits ngoto nret rret,
  tr_stmt c map (So.Sseq s1 s2) ns nd nexits ngoto nret rret ->
  exists n,  
  tr_stmt c map s2 n nd nexits ngoto nret rret /\
  tr_stmt c map s1 ns n nexits ngoto nret rret 
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sifthenelse_inv :
  forall c map a strue sfalse ns nd nexits ngoto nret rret,
  tr_stmt c map (So.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret ->
  exists ntrue nfalse,  
  tr_stmt c map strue ntrue nd nexits ngoto nret rret /\
  tr_stmt c map sfalse nfalse nd nexits ngoto nret rret /\
  tr_condition c map nil a ns ntrue nfalse
  by plain { intros until rret; intros H; inv H; eauto }.       

Closing Fact tr_stmt_sreturn_none_inv : 
  forall c map ns nd nexits ngoto nret rret,
  tr_stmt c map (So.Sreturn None) ns nd nexits ngoto nret rret ->
  ns = nret
  by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sreturn_some_inv :
  forall c map a ns nd nexits ngoto nret rret,
  tr_stmt c map (So.Sreturn (Some a)) ns nd nexits ngoto nret rret ->
  exists rret0, 
  tr_expr c map nil a ns nret rret0 None /\ rret = Some rret0
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_sgoto_inv :
  forall c map lbl ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sgoto lbl) ns nd nexits ngoto nret rret ->
    ngoto!lbl = Some ns
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_slabel_inv :
  forall c map lbl s ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Slabel lbl s) ns nd nexits ngoto nret rret  ->
    exists n,
      ngoto!lbl = Some n /\
      c!n = Some (T.Inop ns) /\
      tr_stmt c map s ns nd nexits ngoto nret rret  
    by plain { intros until rret; intros H; inv H; eauto }.             
          
Closing Fact Kseq_inv : forall s0 k0 s k,
    self__RTLgen.So.Kseq s0 k0 = self__RTLgen.So.Kseq s k -> 
    s0 = s /\ k0 = k
  by plain { intros until k; intros H; inversion H; eauto }.

Closing Fact stop_kseq_discriminate: forall s k, So.Kstop = So.Kseq s k -> False
    by plain { intros until k; intros H; discriminate }.

FInduction match_stacks_call_cont about tr_cont motive
  (fun c map k ncont nexits ngoto nret rret cs
       (_ : tr_cont c map k ncont nexits ngoto nret rret cs) =>
       match_stacks (So.call_cont k) cs /\ c!nret = Some(T.Ireturn rret)).
FProof.
all: intros; fsimpl; auto.
Qed. FEnd match_stacks_call_cont.

FInduction tr_cont_call_cont about tr_cont motive 
  (fun c map k ncont nexits ngoto nret rret cs
    (_ : tr_cont c map k ncont nexits ngoto nret rret cs) =>
    tr_cont c map (So.call_cont k) nret nil ngoto nret rret cs).
FProof.
all: intros; fsimpl; auto; fconstructor; eauto.
Qed. FEnd tr_cont_call_cont.

FInduction tr_find_label about So.stmt motive
  (fun (s : So.stmt) =>
    forall c map lbl n (ngoto: labelmap) nret rret s' k' cs,
    ngoto!lbl = Some n ->
    forall k ns1 nd1 nexits1,
    So.find_label s lbl k = Some (s', k') ->
    tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
    tr_cont c map k nd1 nexits1 ngoto nret rret cs ->
    exists ns2, exists nd2, exists nexits2,
       c!n = Some(T.Inop ns2)
    /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
    /\ tr_cont c map k' nd2 nexits2 ngoto nret rret cs).
FProof.
all: intros until nexits1; fsimpl; try congruence.
(* seq *)
+ caseEq (So.find_label __i lbl (So.Kseq __i0 k)); intros.
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
+ caseEq (So.find_label __i lbl k); intros.
  inv H3. apply tr_stmt_sifthenelse_inv in H4; unpack H4; subst.
  eapply H; eauto.
  apply tr_stmt_sifthenelse_inv in H4; unpack H4; subst. eapply H0; eauto.
Qed. FEnd tr_find_label.
                               
FInduction transl_step_correct about So.step
  motive (fun ge S1 t S2 (_ : So.step ge S1 t S2) =>
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
  assert (T.fn_stacksize tf = So.fn_stackspace f).
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
  pose (e0 := So.set_locals (So.fn_vars f) (So.set_params vargs (So.fn_params f))).
  pose (rs := T.init_regs targs rparams).
  assert (ME: match_env map2 e0 nil rs).
    unfold rs, e0. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (So.fn_params f)); eauto. intros [A B].
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

FLemma transl_initial_states: 
  forall prog tprog, match_prog prog tprog -> 
  forall S', So.initial_state prog S' ->
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
  constructor. auto. fconstructor.
  constructor. apply Mem.extends_refl.
Qed. CloseFLemma.

FLemma transl_final_states:
  forall S' R r,
  match_states S' R -> So.final_state S' r -> T.final_state R r.
FProofLemma. intros. inv H0. inv H.
apply match_stacks_stop_inv in MS; subst. inv LD. constructor. Qed. CloseFLemma.

FEnd RTLgen.

FEnd Base.

Trait Comp_Loops extends Base.

Family CminorSel.
FInductive stmt : Type :=
| Sblock: stmt -> stmt
| Sexit: nat -> stmt
| Sloop: stmt -> stmt.

FInductive cont: Type :=
| Kblock: cont -> cont.  

FRecursion call_cont.
Case Kblock k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case Kblock k := False.
FEnd is_call_cont.
  
FRecursion find_label.
Case Sloop s1 := (fun lbl k => find_label s1 lbl (Kseq (Sloop s1) k)).
Case Sblock s1 := (fun lbl k => find_label s1 lbl (Kblock k)).
Case Sexit n := (fun lbl k => None).
FEnd find_label.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_loop: forall ge f s k sp e m,
   step ge (State f (Sloop s) k sp e m)
     E0 (State f s (Kseq (Sloop s) k) sp e m)
| step_block: forall ge f s k sp e m,
    step ge (State f (Sblock s) k sp e m)
      E0 (State f s (Kblock k) sp e m)
| step_exit_seq: forall ge f n s k sp e m,
   step ge (State f (Sexit n) (Kseq s k) sp e m)
     E0 (State f (Sexit n) k sp e m)
| step_exit_block_0: forall ge f k sp e m,
   step ge (State f (Sexit O) (Kblock k) sp e m)
     E0 (State f Sskip k sp e m)
| step_exit_block_S: forall ge f n k sp e m,
   step ge (State f (Sexit (Datatypes.S n)) (Kblock k) sp e m)
     E0 (State f (Sexit n) k sp e m).
  
FEnd CminorSel.

Trait RTL_jumptable extends RTL.
FInductive instruction: Type :=
| Ijumptable: reg -> list node -> instruction.  

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ijumptable:
   forall ge s f sp pc rs m arg tbl n pc',
   (fn_code f)!pc = Some(Ijumptable arg tbl) ->
   rs#arg = Vint n ->
   list_nth_z tbl (Int.unsigned n) = Some pc' ->
   step ge (State s f sp pc rs m)
     E0 (State s f sp pc' rs m).

FEnd RTL_jumptable.

Family RTL extends RTL_jumptable.
FEnd RTL.

From Rocqet Require Import RTLmonad.

Family RTLgen.

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

FInductive tr_stmt : T.code -> mapping -> So.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=
| tr_Sloop: forall c map sbody ns nd nexits ngoto nret rret nloop nend,
     tr_stmt c map sbody nloop nend nexits ngoto nret rret ->
     c!ns = Some(T.Inop nloop) ->
     c!nend = Some(T.Inop nloop) ->
     tr_stmt c map (So.Sloop sbody) ns nd nexits ngoto nret rret
| tr_Sblock: forall c map sbody ns nd nexits ngoto nret rret,
     tr_stmt c map sbody ns nd (nd :: nexits) ngoto nret rret ->
     tr_stmt c map (So.Sblock sbody) ns nd nexits ngoto nret rret
  | tr_Sexit: forall c map n ns nd nexits ngoto nret rret,
     nth_error nexits n = Some ns ->
     tr_stmt c map (So.Sexit n) ns nd nexits ngoto nret rret.

FInductive tr_cont: T.code -> mapping ->
                   So.cont -> T.node -> list T.node -> labelmap -> T.node -> option reg ->
                   list T.stackframe -> Prop :=
| tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
      tr_cont c map k nd nexits ngoto nret rret cs ->
      tr_cont c map (So.Kblock k) nd (nd :: nexits) ngoto nret rret cs.
  
FRecursion size_stmt.
Local Open Scope nat_scope.
Case Sloop s1 := (size_stmt s1 + 1).
Case Sblock s1 := (size_stmt s1 + 1).
Case Sexit n := 0.
FEnd size_stmt.

FRecursion size_cont.
Case Kblock k1 := (size_cont k1 + 1).
FEnd size_cont.

Closing Fact tr_stmt_tr_sblock : forall c map sbody ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sblock sbody) ns nd nexits ngoto nret rret -> 
    tr_stmt c map sbody ns nd (nd :: nexits) ngoto nret rret
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_tr_sloop : forall c map sbody ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sloop sbody) ns nd nexits ngoto nret rret ->
    exists nloop nend, 
      tr_stmt c map sbody nloop nend nexits ngoto nret rret /\
      c!ns = Some(T.Inop nloop) /\
      c!nend = Some(T.Inop nloop) 
    by plain { intros until rret; intros H; inv H; eauto }.                   

Closing Fact tr_stmt_tr_sexit : forall c map n ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sexit n) ns nd nexits ngoto nret rret ->
    nth_error nexits n = Some ns
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_cont_tr_kblock : forall c map k nd nd' ngoto nret rret cs,
    tr_cont c map (So.Kblock k) nd nd' ngoto nret rret cs ->
    exists nexits,
      nd' = (nd :: nexits) /\
      tr_cont c map k nd nexits ngoto nret rret cs
    by plain { intros until cs; intros H; inv H; eauto }.             

FInduction match_stacks_call_cont.
FProof.
all: intros; fsimpl; auto.
Qed. FEnd match_stacks_call_cont.

FInduction tr_cont_call_cont.
FProof.
all: intros; fsimpl; auto; fconstructor; eauto.
Qed. FEnd tr_cont_call_cont.

FInduction tr_find_label.
FProof.
all: intros until nexits1; fsimpl; try congruence.
(* block *)
+ intros.  apply tr_stmt_tr_sblock in H2.
  eapply H; eauto. fconstructor.
(* loop *)  
+ intros. apply tr_stmt_tr_sloop in H2; unpack H2; subst.
  eapply H; eauto. fconstructor. fconstructor.
Qed. FEnd tr_find_label.

FInduction transl_step_correct.
FProof.
all: intros until tge; intros TRANSL A B; intros R1 MSTATE; inv MSTATE.

(* loop *)
+ apply tr_stmt_tr_sloop in TS; unpack TS; subst.
  econstructor; split.
  left. apply plus_one. eapply T.exec_Inop; eauto.
  econstructor; eauto.
  fconstructor.
  fconstructor.

(* block *)  
+ apply tr_stmt_tr_sblock in TS; unpack TS; subst. 
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. fconstructor. 

(* exit seq *)
+ apply tr_stmt_tr_sexit in TS; unpack TS; subst.
  apply tr_cont_tr_kseq_inv in TK; unpack TK; subst. 
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. fconstructor.

(* exit block 0 *)
+ apply tr_stmt_tr_sexit in TS; unpack TS; subst.
  apply tr_cont_tr_kblock in TK; unpack TK; subst.
  simpl in TS. inv TS.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. fconstructor. 

(* exit block n+1 *)  
+  apply tr_stmt_tr_sexit in TS; unpack TS; subst.
   apply tr_cont_tr_kblock in TK; unpack TK; subst.
   simpl in TS.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. fconstructor.
  
Qed. FEnd transl_step_correct.

FEnd RTLgen.

FEnd Comp_Loops.

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

Family RTL.
FInductive instruction: Type :=
| Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ibuiltin:
      forall ge s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args (Genv.to_senv ge) (fun r => rs#r) sp m args vargs ->
      external_call ef (Genv.to_senv ge) vargs m t vres m' ->
      step ge (State s f sp pc rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m').
  
FEnd RTL.

Family RTLgen.
Family So extends CminorSel. FEnd So.
Family T extends RTL. FEnd T.

FDefinition exprlist_of_expr_list : list So.expr -> So.exprlist := fun l =>
  List.fold_right So.Econs So.Enil l.

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
Fixpoint convert_builtin_arg {A: Type} (a: builtin_arg So.expr) (rl: list A) : builtin_arg A * list A :=
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
Fixpoint convert_builtin_args {A: Type} (al: list (builtin_arg So.expr)) (rl: list A) : list (builtin_arg A) :=
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
   let al := exprlist_of_expr_list (params_of_builtin_args So.expr args) in
   do rargs <- alloc_regs al map;
   let args' := convert_builtin_args args rargs in
   do res' <- convert_builtin_res map (sig_res (ef_sig ef)) r;
   do n1 <- add_instr (T.Ibuiltin ef args' res' nd);
   transl_exprlist al map rargs n1).
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FInductive tr_expr : T.code -> mapping -> list reg -> So.expr -> T.node -> T.node -> reg -> option AST.ident -> Prop :=
| tr_Ebuiltin: forall c map pr ef al ns nd rd dst n1 rl,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (T.Ibuiltin ef (List.map (@BA reg) rl) (BR rd) nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (So.Ebuiltin ef al) ns nd rd dst.

MetaData tr_builtin_res.
Inductive tr_builtin_res: mapping -> builtin_res ident -> builtin_res reg -> Prop :=
  | tr_builtin_res_var: forall map id r,
      map.(map_vars)!id = Some r ->
      tr_builtin_res map (BR id) (BR r)
  | tr_builtin_res_none: forall map,
      tr_builtin_res map BR_none BR_none
  | tr_builtin_res_fresh: forall map r,
      ~reg_in_map map r ->
      tr_builtin_res map BR_none (BR r).
FEnd tr_builtin_res.

FInductive tr_stmt : T.code -> mapping -> So.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=
| tr_Sbuiltin: forall c map res ef args ns nd nexits ngoto nret rret res' n1 rargs,
   tr_exprlist c map nil (exprlist_of_expr_list (params_of_builtin_args So.expr args)) ns n1 rargs ->
   c!n1 = Some (T.Ibuiltin ef (convert_builtin_args args rargs) res' nd) ->
   tr_builtin_res map res res' ->
   tr_stmt c map (So.Sbuiltin res ef args) ns nd nexits ngoto nret rret.

Closing Fact tr_ebuiltin_inv : forall c map pr ef al ns nd rd dst,
    tr_expr c map pr (So.Ebuiltin ef al) ns nd rd dst -> 
    exists n1 rl,
      tr_exprlist c map pr al ns n1 rl /\
      c!n1 = Some (T.Ibuiltin ef (List.map (@BA reg) rl) (BR rd) nd) /\
      reg_map_ok map rd dst /\ ~In rd pr 
    by plain { intros until dst; intros H; inv H; eauto }.                               

FLemma eval_builtin_args_trivial:
  forall (ge: T.genv) (rs: T.regset) sp m rl,
  eval_builtin_args ge (fun r => rs#r) sp m (List.map (@BA reg) rl) rs##rl.
FProofLemma.
  induction rl; simpl.
- constructor.
- constructor; auto. constructor.
Qed. CloseFLemma.

Inherit match_prog.

FLemma senv_preserved: forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.senv_transf_partial TRANSL).
Qed. CloseFLemma.
  
FInduction transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.
FProof.
+ intros; (*red;*) intros. apply tr_ebuiltin_inv in TE; unpack TE; subst.
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
  exploit external_call_mem_extends; eauto.
  intros [v' [tm2 [A [B [C D]]]]].
  exists (rs1#rd <- v'); exists tm2.
(* Exec *)
  split. eapply star_right. eexact EX1.
  change (rs1#rd <- v') with (regmap_setres (BR rd) v' rs1).
  eapply T.exec_Ibuiltin; eauto.
  eapply eval_builtin_args_trivial.
  eapply external_call_symbols_preserved; eauto. apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) H0 eq_refl eq_refl).
  reflexivity.
(* Match-env *)
  split. eauto using match_env_update_temp, match_env_update_dest. 
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed. FEnd transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.

FRecursion size_stmt.
Case _ := 1.
FEnd size_stmt.

FInduction tr_find_label.
FProof.
all: intros until nexits1; fsimpl; try congruence.
Qed. FEnd tr_find_label.

Closing Fact tr_sbuiltin_inv : forall c map res ef args ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sbuiltin res ef args) ns nd nexits ngoto nret rret -> 
    exists res' n1 rargs,
      tr_exprlist c map nil (exprlist_of_expr_list (params_of_builtin_args So.expr args)) ns n1 rargs /\
      c!n1 = Some (T.Ibuiltin ef (convert_builtin_args args rargs) res' nd) /\
      tr_builtin_res map res res'
    by plain { intros until rret; intros H; inv H; eauto }.       

Closing Fact tr_eval_enil : forall ge sp e m le vl,
    So.eval_exprlist ge sp e m le So.Enil vl ->
    vl = nil
    by plain { intros until vl; intros H; inv H; eauto }.

Closing Fact tr_eval_econs : forall ge sp e m le a1 al vl,
    So.eval_exprlist ge sp e m le (So.Econs a1 al) vl -> 
    exists v1 vl', 
      vl = (v1 :: vl') /\
      So.eval_expr ge sp e m le a1 v1 /\ So.eval_exprlist ge sp e m le al vl'
      by plain { intros until vl; intros H; inv H; eauto }.                                                    
                                                    
FLemma eval_exprlist_append:
  forall ge sp e m le al1 vl1 al2 vl2,
  So.eval_exprlist ge sp e m le (exprlist_of_expr_list al1) vl1 ->
  So.eval_exprlist ge sp e m le (exprlist_of_expr_list al2) vl2 ->
  So.eval_exprlist ge sp e m le (exprlist_of_expr_list (al1 ++ al2)) (vl1 ++ vl2).
FProofLemma.
  induction al1; simpl; intros vl1 al2 vl2 E1 E2.
- apply tr_eval_enil in E1; unpack E1; subst. auto.
- apply tr_eval_econs in E1; unpack E1; subst. simpl. fconstructor.
Qed. CloseFLemma.

FLemma invert_eval_builtin_arg:
  forall ge sp e m a v,
  So.eval_builtin_arg ge sp e m a v ->
  exists vl,
     So.eval_exprlist ge sp e m nil (exprlist_of_expr_list (AST.params_of_builtin_arg a)) vl
  /\ Events.eval_builtin_arg (Genv.to_senv ge) (fun v => v) (Vptr sp Ptrofs.zero) m (fst (convert_builtin_arg a vl)) v
  /\ (forall vl', convert_builtin_arg a (vl ++ vl') = (fst (convert_builtin_arg a vl), vl')).
FProofLemma.
  induction 1; simpl. (* 2-8: try (econstructor; do 4 fconstructor; intuition eauto with evalexpr barg; fail).*)
- econstructor; split. do 2 fconstructor. eauto. (*with evalexpr.*) split. constructor. auto.
- econstructor; split. do 2 fconstructor. eauto. (*with evalexpr.*) split. constructor. auto.
- econstructor; split. do 2 fconstructor. eauto. (*with evalexpr.*) split. repeat constructor. auto.
- econstructor; split. do 2 fconstructor. split. constructor. auto.
- econstructor; split. do 2 fconstructor. split. constructor. auto.
- econstructor; split. do 2 fconstructor. split. repeat constructor. auto. auto.
- econstructor; split. do 2 fconstructor. split. constructor. auto.
- econstructor; split. do 2 fconstructor. split. constructor. auto. auto.
- econstructor; split. do 2 fconstructor. split. constructor. auto.
- econstructor; split. do 3 fconstructor. split. repeat constructor. auto. 
- destruct IHeval_builtin_arg1 as (vl1 & A1 & B1 & C1).
  destruct IHeval_builtin_arg2 as (vl2 & A2 & B2 & C2).
  destruct (convert_builtin_arg a1 vl1) as [a1' rl1] eqn:E1; simpl in *.
  destruct (convert_builtin_arg a2 vl2) as [a2' rl2] eqn:E2; simpl in *.
  exists (vl1 ++ vl2); split.
  apply eval_exprlist_append; auto.
  split. rewrite C1, E2. constructor; auto.
  intros. rewrite app_ass, !C1, C2, E2. auto.
Qed. CloseFLemma.

FLemma invert_eval_builtin_args:
  forall ge sp e m al vl,
  list_forall2 (So.eval_builtin_arg ge sp e m) al vl ->
  exists vl',
     So.eval_exprlist ge sp e m nil (exprlist_of_expr_list (AST.params_of_builtin_args al)) vl'
  /\ Events.eval_builtin_args ge (fun v => v) (Vptr sp Ptrofs.zero) m (convert_builtin_args al vl') vl.
FProofLemma.
  induction 1; simpl.
- exists (@nil val); split. fconstructor. constructor.
- exploit invert_eval_builtin_arg; eauto. intros (vl1 & A & B & C).
  destruct IHlist_forall2 as (vl2 & D & E).
  exists (vl1 ++ vl2); split.
  apply eval_exprlist_append; auto.
  rewrite C; simpl. constructor; auto.
Qed. CloseFLemma.

FLemma transl_eval_builtin_arg:
  forall (ge: So.genv) sp m rs a vl rl v,
  Val.lessdef_list vl rs##rl ->
  Events.eval_builtin_arg ge (fun v => v) sp m (fst (convert_builtin_arg a vl)) v ->
  exists v',
     Events.eval_builtin_arg ge (fun r => rs#r) sp m (fst (convert_builtin_arg a rl)) v'
  /\ Val.lessdef v v'
  /\ Val.lessdef_list (snd (convert_builtin_arg a vl)) rs##(snd (convert_builtin_arg a rl)).
FProofLemma.
  induction a; simpl; intros until v; intros LD EV;
  try (now (inv EV; econstructor; eauto with barg)).
- destruct rl; simpl in LD; inv LD; inv EV; simpl.
  econstructor; eauto with barg.
  exists (rs#p); intuition auto. constructor.
- destruct (convert_builtin_arg a1 vl) as [a1' vl1] eqn:CV1; simpl in *.
  destruct (convert_builtin_arg a2 vl1) as [a2' vl2] eqn:CV2; simpl in *.
  destruct (convert_builtin_arg a1 rl) as [a1'' rl1] eqn:CV3; simpl in *.
  destruct (convert_builtin_arg a2 rl1) as [a2'' rl2] eqn:CV4; simpl in *.
  inv EV.
  exploit IHa1; eauto. rewrite CV1; simpl; eauto.
  rewrite CV1, CV3; simpl. intros (v1' & A1 & B1 & C1).
  exploit IHa2. eexact C1. rewrite CV2; simpl; eauto.
  rewrite CV2, CV4; simpl. intros (v2' & A2 & B2 & C2).
  exists (Val.longofwords v1' v2'); split. constructor; auto.
  split; auto. apply Val.longofwords_lessdef; auto.
- destruct (convert_builtin_arg a1 vl) as [a1' vl1] eqn:CV1; simpl in *.
  destruct (convert_builtin_arg a2 vl1) as [a2' vl2] eqn:CV2; simpl in *.
  destruct (convert_builtin_arg a1 rl) as [a1'' rl1] eqn:CV3; simpl in *.
  destruct (convert_builtin_arg a2 rl1) as [a2'' rl2] eqn:CV4; simpl in *.
  inv EV.
  exploit IHa1; eauto. rewrite CV1; simpl; eauto.
  rewrite CV1, CV3; simpl. intros (v1' & A1 & B1 & C1).
  exploit IHa2. eexact C1. rewrite CV2; simpl; eauto.
  rewrite CV2, CV4; simpl. intros (v2' & A2 & B2 & C2).
  econstructor; split. constructor; eauto.
  split; auto. destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef.
Qed. CloseFLemma.

FLemma transl_eval_builtin_args:
  forall (ge: So.genv) sp m rs al vl1 rl vl,
  Val.lessdef_list vl1 rs##rl ->
  Events.eval_builtin_args (Genv.to_senv ge) (fun v => v) sp m (convert_builtin_args al vl1) vl ->
  exists vl',
     Events.eval_builtin_args ge (fun r => rs#r) sp m (convert_builtin_args al rl) vl'
  /\ Val.lessdef_list vl vl'.
FProofLemma.
  induction al; simpl; intros until vl; intros LD EV.
- inv EV. exists (@nil val); split; constructor.
- destruct (convert_builtin_arg a vl1) as [a1' vl2] eqn:CV1; simpl in *.
  inv EV.
  exploit transl_eval_builtin_arg. eauto. instantiate (2 := a). rewrite CV1; simpl; eauto.
  rewrite CV1; simpl. intros (v1' & A1 & B1 & C1).
  exploit IHal. eexact C1. eauto. intros (vl' & A2 & B2).
  destruct (convert_builtin_arg a rl) as [a1'' rl2]; simpl in *.
  exists (v1' :: vl'); split; constructor; auto.
Qed. CloseFLemma.

FLemma match_env_update_res:
  forall map res v e le tres tv rs,
  Val.lessdef v tv ->
  map_wf map ->
  tr_builtin_res map res tres ->
  match_env map e le rs ->
  match_env map (So.set_builtin_res res v e) le (regmap_setres tres tv rs).
FProofLemma.
  intros. inv H1; simpl.
- eapply match_env_update_var; eauto.
- auto.
- eapply match_env_update_temp; eauto.
Qed. CloseFLemma.

FInduction transl_step_correct.
FProof.
all: intros until tge; intros TRANSL A B; intros R1 MSTATE; inv MSTATE.
+ apply tr_sbuiltin_inv in TS; unpack TS; subst. 
  exploit invert_eval_builtin_args; eauto. intros (vparams & P & Q).
  exploit transl_exprlist_correct; eauto.
  intros [rs' [tm' [E [F [G [J K]]]]]].
  exploit transl_eval_builtin_args; eauto.
  intros (vargs' & U & V).
  exploit (@eval_builtin_args_lessdef _ (Genv.to_senv (Genv.globalenv prog)) (fun r => rs'#r) (fun r => rs'#r)); eauto.
  intros (vargs'' & X & Y).
  assert (Z: Val.lessdef_list vl vargs'') by (eapply Val.lessdef_list_trans; eauto).
  edestruct external_call_mem_extends as [tv [tm'' [A [B [C D]]]]]; eauto.
  econstructor; split.
  left. eapply plus_right. eexact E.
  eapply T.exec_Ibuiltin. eauto.
  eapply eval_builtin_args_preserved with (ge1 := (Genv.globalenv prog)); eauto. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). 
  eapply external_call_symbols_preserved. apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). eauto.
  traceEq.
  econstructor; eauto. fconstructor.
  eapply match_env_update_res; eauto.
Qed. FEnd transl_step_correct.

FEnd RTLgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family CminorSel.
(*CminorSel *)
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

Family RTL.
FInductive instruction: Type :=
| Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
| Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Iload:
      forall ge s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step ge (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
| exec_Istore:
      forall ge s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step ge (State s f sp pc rs m)
        E0 (State s f sp pc' rs m').
  
FEnd RTL.

Family RTLgen.
Family So extends CminorSel. FEnd So.
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

FInductive tr_expr : T.code -> mapping -> list reg -> So.expr -> T.node -> T.node -> reg -> option AST.ident -> Prop :=
| tr_Eload: forall c map pr chunk addr al ns nd rd n1 rl dst,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (T.Iload chunk addr rl rd nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (So.Eload chunk addr al) ns nd rd dst.

FInductive tr_stmt : T.code -> mapping -> So.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=              
| tr_Sstore: forall c map chunk addr al b ns nd nexits ngoto nret rret rd n1 rl n2,
     tr_exprlist c map nil al ns n1 rl ->
     tr_expr c map rl b n1 n2 rd None ->
     c!n2 = Some (T.Istore chunk addr rl rd nd) ->
     tr_stmt c map (So.Sstore chunk addr al b) ns nd nexits ngoto nret rret.


Closing Fact tr_expr_tr_eload : forall c map pr chunk addr al ns nd rd dst,
  tr_expr c map pr (So.Eload chunk addr al) ns nd rd dst ->
    exists n1 rl,
      tr_exprlist c map pr al ns n1 rl /\
      c!n1 = Some (T.Iload chunk addr rl rd nd) /\
      reg_map_ok map rd dst /\ ~In rd pr
      by plain { intros until dst; intros H; inv H; eauto }.

FInduction transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.
FProof.
+ intros; (*red;*) intros. apply tr_expr_tr_eload in TE; unpack TE; subst. 
  exploit H; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
  edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
  edestruct Mem.loadv_extends as [v' []]; eauto.
  exists (rs1#rd <- v'); exists tm1.
(* Exec *)
  split. eapply star_right. eexact EX1. eapply T.exec_Iload. eauto.
  instantiate (1 := vaddr'). rewrite <- H1.
  apply eval_addressing_preserved. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) H0 eq_refl eq_refl).
  auto. traceEq.
(* Match-env *)
  split. eauto using match_env_update_temp, match_env_update_dest.
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto. 
Qed. FEnd transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.

FRecursion size_stmt.
Case _ := 1.
FEnd size_stmt.

FInduction tr_find_label.
FProof.
all: intros until nexits1; fsimpl; try congruence.
Qed. FEnd tr_find_label.

Closing Fact tr_expr_tr_sstore : forall c map chunk addr al b ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sstore chunk addr al b) ns nd nexits ngoto nret rret ->
    exists n1 rl n2 rd,
      tr_exprlist c map nil al ns n1 rl /\
      tr_expr c map rl b n1 n2 rd None /\
      c!n2 = Some (T.Istore chunk addr rl rd nd)
    by plain { intros until rret; intros H; inv H; eauto }.    

FInduction transl_step_correct.
FProof.
all: intros until tge; intros TRANSL A B; intros R1 MSTATE; inv MSTATE.
(* store *)
+  apply tr_expr_tr_sstore in TS; unpack TS; subst. 
  exploit transl_exprlist_correct; eauto.
  intros [rs' [tm' [A [B [C [D E]]]]]].
  exploit transl_expr_correct; eauto.
  intros [rs'' [tm'' [F [G [J [K L]]]]]].
  assert (Val.lessdef_list vl rs''##rl).
    replace (rs'' ## rl) with (rs' ## rl). auto.
    apply list_map_exten. intros. apply K. auto.
  edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
  edestruct Mem.storev_extends as [tm''' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eapply star_trans. eexact A. eexact F. reflexivity.
  eapply T.exec_Istore with (a := vaddr'). eauto.
  rewrite <- H0. apply eval_addressing_preserved. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). 
  eauto. traceEq.
  econstructor; eauto. fconstructor.
Qed. FEnd transl_step_correct.

FEnd RTLgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.
FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family CminorSel.
FInductive expr : Type :=
| Eexternal : ident -> signature -> exprlist -> expr.

FInductive stmt : Type :=
| Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
| Stailcall: signature -> expr + ident -> exprlist -> stmt.

FInductive cont: Type :=
| Kcall: option ident -> function -> val -> env -> cont -> cont.

FRecursion call_cont.
Case Kcall i f v e k := (Kcall i f v e k).
FEnd call_cont.

FRecursion is_call_cont.
Case Kcall i f v e k := True.
FEnd is_call_cont.

FRecursion find_label.
Case _ := (fun lbl k => None).
FEnd find_label.

FInductive eval_expr: genv -> fenv -> env -> mem -> letenv -> expr -> val -> Prop :=
| eval_Eexternal: forall ge sp e m le id sg al b ef vl v,
   Genv.find_symbol ge id = Some b ->
   Genv.find_funct_ptr ge b = Some (AST.External ef) ->
   ef_sig ef = sg ->
   eval_exprlist ge sp e m le al vl ->
   external_call ef ge vl m E0 v m ->
   eval_expr ge sp e m le (Eexternal id sg al) v.
  
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
     E0 (Callstate fd vargs (Kcall optid f (Vptr sp Ptrofs.zero) e k) m)    
| step_tailcall: forall ge f sig a bl k sp e m vf vargs fd m',
   eval_expr_or_symbol ge sp e m nil a vf ->
   eval_exprlist ge sp e m nil bl vargs ->
   Genv.find_funct ge vf = Some fd ->
   funsig fd = sig ->
   Mem.free m sp 0 (fn_stackspace f) = Some m' ->
   step ge (State f (Stailcall sig a bl) k sp e m)
     E0 (Callstate fd vargs (call_cont k) m')
| step_return: forall ge v optid f sp e k m,
      step ge (Returnstate v (Kcall optid f (Vptr sp Ptrofs.zero) e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m)
| step_external_function: forall ge ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step ge (Callstate (AST.External ef) vargs k m)
         t (Returnstate vres k m').
        
FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
| Itailcall: signature -> reg + ident -> list reg -> instruction.

Inherit genv.
Inherit regset.

FDefinition find_function :
       genv -> reg + ident -> regset -> option fundef := fun ge ros rs =>
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Icall:
   forall ge s f sp pc rs m sig ros args res pc' fd,
   (fn_code f)!pc = Some(Icall sig ros args res pc') ->
   find_function ge ros rs = Some fd ->
   funsig fd = sig ->
   step ge (State s f sp pc rs m)
     E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
| exec_Itailcall:
   forall ge s f stk pc rs m sig ros args fd m',
   (fn_code f)!pc = Some(Itailcall sig ros args) ->
   find_function ge ros rs = Some fd ->
   funsig fd = sig ->
   Mem.free m stk 0 (fn_stacksize f) = Some m' ->
   step ge (State s f (Vptr stk Ptrofs.zero) pc rs m)
     E0 (Callstate s fd rs##args m')
| exec_function_external:
      forall ge s ef args res t m m',
      external_call ef ge args m t res m' ->
      step ge (Callstate s (AST.External ef) args m)
         t (Returnstate s res m')
| exec_return:
      forall ge res f sp pc rs s vres m,
      step ge (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

FEnd RTL.

Family RTLgen.
Family So extends CminorSel. FEnd So.
Family T extends RTL. FEnd T.

Inherit alloc_regs.
From Rocqet Require Import RTLmonad.

FDefinition alloc_optreg : mapping -> option ident -> mon reg := fun map dest =>
  match dest with
  | Some id => find_var map id
  | None => new_reg
  end.

FRecursion transl_expr with transl_exprlist with transl_condexpr.
Case Eexternal id sg al :=
  (fun map rd nd =>
    do rl <- alloc_regs al map;
    do no <- add_instr (T.Icall sg (inr id) rl rd nd);
    transl_exprlist al map rl no).
FEnd transl_expr with transl_exprlist with transl_condexpr.

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

FInductive tr_expr : T.code -> mapping -> list reg -> So.expr -> T.node -> T.node -> reg -> option AST.ident -> Prop :=
| tr_Eexternal: forall c map pr id sg al ns nd rd dst n1 rl,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (T.Icall sg (inr _ id) rl rd nd) ->
      reg_map_ok map rd dst -> ~In rd pr ->
      tr_expr c map pr (Eexternal id sg al) ns nd rd dst.
  
FInductive tr_stmt : T.code -> mapping -> So.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=
| tr_Scall: forall c map optid sig b cl ns nd nexits ngoto nret rret rd n1 rf n2 rargs,
     tr_expr c map nil b ns n1 rf None ->
     tr_exprlist c map (rf :: nil) cl n1 n2 rargs ->
     c!n2 = Some (T.Icall sig (inl _ rf) rargs rd nd) ->
     reg_map_ok map rd optid ->
     tr_stmt c map (So.Scall optid sig (inl _ b) cl) ns nd nexits ngoto nret rret
| tr_Scall_imm: forall c map optid sig id cl ns nd nexits ngoto nret rret rd n2 rargs,
     tr_exprlist c map nil cl ns n2 rargs ->
     c!n2 = Some (T.Icall sig (inr _ id) rargs rd nd) ->
     reg_map_ok map rd optid ->
     tr_stmt c map (So.Scall optid sig (inr _ id) cl) ns nd nexits ngoto nret rret
| tr_Stailcall: forall c map sig b cl ns nd nexits ngoto nret rret n1 rf n2 rargs,
     tr_expr c map nil b ns n1 rf None ->
     tr_exprlist c map (rf :: nil) cl n1 n2 rargs ->
     c!n2 = Some (T.Itailcall sig (inl _ rf) rargs) ->
     tr_stmt c map (So.Stailcall sig (inl _ b) cl) ns nd nexits ngoto nret rret
| tr_Stailcall_imm: forall c map sig id cl ns nd nexits ngoto nret rret n2 rargs,
     tr_exprlist c map nil cl ns n2 rargs ->
     c!n2 = Some (T.Itailcall sig (inr _ id) rargs) ->
     tr_stmt c map (So.Stailcall sig (inr _ id) cl) ns nd nexits ngoto nret rret.

Inherit map_wf.

FInductive tr_cont: T.code -> mapping ->
                   So.cont -> T.node -> list T.node -> labelmap -> T.node -> option reg ->
                   list T.stackframe -> Prop :=
| tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
      c!nret = Some(T.Ireturn rret) ->
      match_stacks (So.Kcall optid f sp e k) cs ->
      tr_cont c map (So.Kcall optid f sp e k) nret nil ngoto nret rret cs
with match_stacks: So.cont -> list T.stackframe -> Prop :=
| match_stacks_call: forall optid f sp e k r tf n rs cs map nexits ngoto nret rret,
      map_wf map ->
      tr_fun tf map f ngoto nret rret ->
      match_env map e nil rs ->
      reg_map_ok map r optid ->
      tr_cont (T.fn_code tf) map k n nexits ngoto nret rret cs ->
      match_stacks (So.Kcall optid f sp e k) (T.Stackframe r tf sp n rs :: cs).


FInduction transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_expr_correct with transl_exprlist_correct with transl_condexpr_correct.

FRecursion size_stmt.
Case _ := 1.
FEnd size_stmt.

FRecursion size_cont.
Case _ := 0.
FEnd size_cont.

FInduction match_stacks_call_cont.
FProof.
all: intros; fsimpl; auto.
Qed. FEnd match_stacks_call_cont.

FInduction tr_cont_call_cont.
FProof.
all: intros; fsimpl; auto; fconstructor; eauto.
Qed. FEnd tr_cont_call_cont.

FInduction tr_find_label.
FProof.
all: intros until nexits1; fsimpl; try congruence.
Qed. FEnd tr_find_label.

Closing Fact tr_stmt_tr_scall : forall c map optid sig b cl ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Scall optid sig (inl _ b) cl) ns nd nexits ngoto nret rret -> 
    exists rd n1 rf n2 rargs,
      tr_expr c map nil b ns n1 rf None /\
      tr_exprlist c map (rf :: nil) cl n1 n2 rargs /\
      c!n2 = Some (T.Icall sig (inl _ rf) rargs rd nd) /\
      reg_map_ok map rd optid
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_tr_scall_imm : forall c map optid sig id cl ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Scall optid sig (inr _ id) cl) ns nd nexits ngoto nret rret ->
    exists rd n2 rargs,
      tr_exprlist c map nil cl ns n2 rargs /\
      c!n2 = Some (T.Icall sig (inr _ id) rargs rd nd) /\
      reg_map_ok map rd optid
    by plain { intros until rret; intros H; inv H; eauto }.

Closing Fact tr_stmt_tr_stailcall : forall c map sig b cl ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Stailcall sig (inl _ b) cl) ns nd nexits ngoto nret rret -> 
    exists n1 rf n2 rargs,
     tr_expr c map nil b ns n1 rf None /\
     tr_exprlist c map (rf :: nil) cl n1 n2 rargs /\
     c!n2 = Some (T.Itailcall sig (inl _ rf) rargs) 
    by plain { intros until rret; intros H; inv H; eauto }.


Closing Fact tr_stmt_tr_stailcall_imm : forall c map sig id cl ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Stailcall sig (inr _ id) cl) ns nd nexits ngoto nret rret ->
    exists n2 rargs,
      tr_exprlist c map nil cl ns n2 rargs /\
      c!n2 = Some (T.Itailcall sig (inr _ id) rargs) 
    by plain { intros until rret; intros H; inv H; eauto }.                

FLemma functions_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (v: val) (f: So.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_funct_transf_partial TRANSL).
Qed. CloseFLemma.

Closing Fact match_stacks_call_inv : forall optid f sp e cs k,
    match_stacks (So.Kcall optid f sp e k) cs ->
    exists r tf n rs cs' map nexits ngoto nret rret,
      cs = (T.Stackframe r tf sp n rs :: cs') /\
      map_wf map /\
      tr_fun tf map f ngoto nret rret /\
      match_env map e nil rs /\
      reg_map_ok map r optid /\
      tr_cont (T.fn_code tf) map k n nexits ngoto nret rret cs' 
    by plain { intros until k; intros H; inv H; eauto }.             

FInduction transl_step_correct.
FProof.
all: intros until tge; intros TRANSL A B; intros R1 MSTATE; inv MSTATE.

(* call *)
+ destruct a. apply tr_stmt_tr_scall in TS; unpack TS; subst; inv e0.   
  (* indirect *)
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D X]]]]]].
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J Y]]]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  econstructor; split.
  left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
  eapply T.exec_Icall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
  apply sig_transl_function; auto.
  traceEq.
  constructor; auto. fconstructor. 
  (* direct *)
  apply tr_stmt_tr_scall_imm in TS; unpack TS; subst; inv e0.   
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J Y]]]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  econstructor; split.
  left; eapply plus_right. eexact E.
  eapply T.exec_Icall; eauto. simpl.
  rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). rewrite H5.
    rewrite Genv.find_funct_find_funct_ptr in P. eauto.
  apply sig_transl_function; auto.
  traceEq.
  constructor; auto. fconstructor. 

(* tailcall *)
+  destruct a. apply tr_stmt_tr_stailcall in TS; unpack TS; subst; inv e0.   
  (* indirect *)
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D X]]]]]].
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J Y]]]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont. instantiate (1 := TK). intros [U V].
  assert (T.fn_stacksize tf = So.fn_stackspace f). inv TF; auto.
  edestruct Mem.free_parallel_extends as [tm''' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
  eapply T.exec_Itailcall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
  apply sig_transl_function; auto.
  rewrite H; eauto.
  traceEq.
  constructor; auto. 
  (* direct *)
  apply tr_stmt_tr_stailcall_imm in TS; unpack TS; subst; inv e0.   
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J Y]]]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont. instantiate (1 := TK). intros [U V].
  assert (T.fn_stacksize tf = So.fn_stackspace f). inv TF; auto.
  edestruct Mem.free_parallel_extends as [tm''' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eexact E.
  eapply T.exec_Itailcall; eauto. simpl.
  rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl).
  rewrite H5.
  rewrite Genv.find_funct_find_funct_ptr in P. eauto.
  apply sig_transl_function; auto.
  rewrite H; eauto.
  traceEq.
  constructor; auto.

+ (* return *)
  apply match_stacks_call_inv in MS; unpack MS; subst. 
  econstructor; split.
  left; apply plus_one; fconstructor.
  econstructor; eauto. fconstructor.
  eapply match_env_update_dest; eauto.

(* external call *)
+ apply cheat.  
Qed. FEnd transl_step_correct.

FEnd RTLgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait CminorSel_Switch extends CminorSel.

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
Fixpoint transl_exitexpr (map: mapping) (a: So.exitexpr) (nexits: list T.node)
                         {struct a} : mon T.node :=
  match a with
  | So.XEexit n =>
      transl_exit nexits n
  | So.XEjumptable a tbl =>
      do r <- alloc_reg a map;
      do tbl' <- transl_jumptable nexits tbl;
      do n1 <- add_instr (T.Ijumptable r tbl');
         transl_expr a map r n1
  | So.XEcondition a b c =>
      do nc <- transl_exitexpr map c nexits;
      do nb <- transl_exitexpr map b nexits;
         transl_condexpr a map nb nc
  | So.XElet a b =>
      do r <- new_reg;
      do n1 <- transl_exitexpr (add_letvar map r) b nexits;
         transl_expr a map r n1
  end.
FEnd transl_exitexpr.

FRecursion transl_stmt.
Case Sswitch a := (fun map nd nexits ngoto nret rret => transl_exitexpr map a nexits).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sswitch a := (fun lm => ret lm).
FEnd reserve_labels.

Inherit tr_expr.

FDefinition tr_jumptable := fun (nexits: list T.node) (tbl: list nat) (ttbl: list T.node) =>
  forall v act,
  list_nth_z tbl v = Some act ->
  exists n, list_nth_z ttbl v = Some n /\ nth_error nexits act = Some n.

MetaData tr_exitexpr.
Inductive tr_exitexpr (c: T.code):
       mapping -> So.exitexpr -> T.node -> list T.node -> Prop :=
  | tr_XEcond: forall map x n nexits,
      nth_error nexits x = Some n ->
      tr_exitexpr c map (So.XEexit x) n nexits
  | tr_XEjumptable: forall map a tbl ns nexits n1 r tbl',
      tr_jumptable nexits tbl tbl' ->
      tr_expr c map nil a ns n1 r None ->
      c!n1 = Some (T.Ijumptable r tbl') ->
      tr_exitexpr c map (So.XEjumptable a tbl) ns nexits
  | tr_XEcondition: forall map a1 a2 a3 ns nexits n2 n3,
      tr_condition c map nil a1 ns n2 n3 ->
      tr_exitexpr c map a2 n2 nexits ->
      tr_exitexpr c map a3 n3 nexits ->
      tr_exitexpr c map (So.XEcondition a1 a2 a3) ns nexits
  | tr_XElet: forall map a b ns nexits r n1,
      ~reg_in_map map r ->
      tr_expr c map nil a ns n1 r None ->
      tr_exitexpr c (add_letvar map r) b n1 nexits ->
      tr_exitexpr c map (So.XElet a b) ns nexits.
FEnd tr_exitexpr.
       
FInductive tr_stmt : T.code -> mapping -> So.stmt -> T.node -> T.node -> list T.node -> labelmap -> T.node -> option reg -> Prop :=
| tr_Sswitch: forall c map a ns nd nexits ngoto nret rret,
     tr_exitexpr c map a ns nexits ->
     tr_stmt c map (So.Sswitch a) ns nd nexits ngoto nret rret.

FRecursion size_stmt.
Case _ := 1.
FEnd size_stmt.

MetaData transl_exitexpr_prop.
Definition transl_exitexpr_prop
     ge sp e m (le: So.letenv) (a: So.exitexpr) (x: nat) : Prop :=
  forall tm cs f map ns nexits rs prog tprog tge
    (MWF: map_wf map)
    (_ : ge = Genv.globalenv prog)
    (_ : tge = Genv.globalenv tprog)     
    (_ : match_prog prog tprog)
    (TE: tr_exitexpr (T.fn_code f) map a ns nexits)
    (ME: match_env map e le rs)
    (EXT: Mem.extends m tm),
  exists nd, exists rs', exists tm',
     star T.step tge (T.State cs f (Vptr sp Ptrofs.zero) ns rs tm) E0 (T.State cs f (Vptr sp Ptrofs.zero) nd rs' tm')
  /\ nth_error nexits x = Some nd
  /\ match_env map e le rs'
  /\ Mem.extends m tm'.

Theorem transl_exitexpr_correct:
  forall ge sp e m le a x,
  So.eval_exitexpr ge sp e m le a x ->
  transl_exitexpr_prop ge sp e m le a x.
Proof.
  induction 1; red; intros; inv TE.
- (* XEexit *)
  exists ns, rs, tm.
  split. apply star_refl.
  auto.
- (* XEjumptable *)
  exploit H6; eauto. intros (nd & A & B).
  exploit transl_expr_correct; eauto. intros (rs1 & tm1 & EXEC1 & ME1 & RES1 & PRES1 & EXT1).
  exists nd, rs1, tm1.
  split. eapply star_right. eexact EXEC1. eapply T.exec_Ijumptable; eauto. inv RES1; auto. traceEq.
  auto.
- (* XEcondition *)
  exploit transl_condexpr_correct; eauto. intros (rs1 & tm1 & EXEC1 & ME1 & RES1 & EXT1).
  exploit IHeval_exitexpr; eauto.
  instantiate (2 := if va then n2 else n3). destruct va; eauto.
  intros (nd & rs2 & tm2 & EXEC2 & EXIT2 & ME2 & EXT2).
  exists nd, rs2, tm2.
  split. eapply star_trans. apply plus_star. eexact EXEC1. eexact EXEC2. traceEq.
  auto.
- (* XElet *)
  exploit transl_expr_correct; eauto. intros (rs1 & tm1 & EXEC1 & ME1 & RES1 & PRES1 & EXT1).
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit IHeval_exitexpr; eauto. eapply match_env_bind_letvar; eauto.
  intros (nd & rs2 & tm2 & EXEC2 & EXIT2 & ME2 & EXT2).
  exists nd, rs2, tm2.
  split. eapply star_trans. eexact EXEC1. eexact EXEC2. traceEq.
  split. auto.
  split. eapply match_env_unbind_letvar; eauto.
  auto.
Qed.
FEnd transl_exitexpr_prop.

Closing Fact tr_expr_tr_sswitch : forall c map a ns nd nexits ngoto nret rret,
    tr_stmt c map (So.Sswitch a) ns nd nexits ngoto nret rret -> 
    tr_exitexpr c map a ns nexits
    by plain { intros until rret; intros H; inv H; eauto }.                

FInduction tr_find_label.
FProof.
all: intros until nexits1; fsimpl; try congruence.
Qed. FEnd tr_find_label.

FInduction transl_step_correct.
FProof.
all: intros until tge; intros TRANSL A B; intros R1 MSTATE; inv MSTATE.
+ apply tr_expr_tr_sswitch in TS; unpack TS; subst. 
  exploit transl_exitexpr_correct; eauto.
  intros (nd & rs' & tm' & A & B & C & D).
  econstructor; split.
  right; split. eexact A. Lt_state.
  econstructor; eauto. fconstructor.
Qed. FEnd transl_step_correct.

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
