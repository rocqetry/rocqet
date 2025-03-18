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

From Rocqet Require Import Machregs.
From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

(*Require Import LfamBase.
Require Import Linear.
Require Import Mach.*)

Trait Base.

Family Lfam.
FDefinition label := positive.

FInductive instruction: Type :=
| Lop : Op.operation -> list mreg -> mreg -> instruction
| Lcond : Op.condition -> list mreg -> label -> instruction
| Llabel: label -> instruction
| Lgoto: label -> instruction
| Lreturn : instruction.

FDefinition code: Type := list instruction.

FOpaque Definition function : Type := cheat.
FOpaque Definition function_sig: function -> signature := cheat.

FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) =>
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

FEnd Lfam.

Family Linear extends Lfam.
FInductive instruction: Type :=
| Lgetstack: slot -> Z -> typ -> mreg -> instruction
| Lsetstack: mreg -> slot -> Z -> typ -> instruction.

Inherit code.

MetaData fn binds fn_sig, fn_code, fn_stacksize.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_sig := fn_sig.

FEnd Linear.

Family Mach extends Lfam.

FInductive instruction: Type :=
| Lgetstack: ptrofs -> typ -> mreg -> instruction
| Lgetparam: ptrofs -> typ -> mreg -> instruction
| Lsetstack: mreg -> ptrofs -> typ -> instruction.

Inherit code.

MetaData fn binds fn_sig, fn_code, fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
Record fn: Type := mkfunction {
  fn_sig: signature;
  fn_code: code;
  fn_stacksize: Z;
  fn_link_ofs: ptrofs;
  fn_retaddr_ofs: ptrofs
}.
FEnd fn.

FOverride Definition function := fn.

FEnd Mach.

(* Linear -> Mach *)
Family Stacking.
Family S extends Linear. FEnd S.
Family T extends Mach. FEnd T.

(* Lineartyping *)
From Rocqet Require Import Conventions.

FDefinition slot_valid := fun funct (sl: slot) (ofs: Z) (ty: typ) =>
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (Locations.S Incoming ofs ty) (regs_of_rpairs (loc_parameters (S.fn_sig funct)))
  end
  && Zdivide_dec (typealign ty) ofs.

FDefinition slot_writable := fun (sl: slot) =>
  match sl with
  | Local => true
  | Outgoing => true
  | Incoming => false
  end.

FDefinition loc_valid := fun funct l =>
  match l with
  | R r => true
  | S Local ofs ty => slot_valid funct Local ofs ty
  | S _ _ _ => false
  end.

MetaData  wt_builtin_res.
Fixpoint wt_builtin_res (ty: typ) (res: builtin_res mreg) : bool :=
  match res with
  | BR r => subtype ty (mreg_type r)
  | BR_none => true
  | BR_splitlong hi lo => wt_builtin_res AST.Tint hi && wt_builtin_res AST.Tint lo
  end.
FEnd wt_builtin_res.

FRecursion wt_instr about S.instruction motive (fun (_ : S.instruction) => S.function -> bool) by _rect.
Case Lgetstack sl ofs ty r := (fun funct => subtype ty (mreg_type r) && slot_valid funct sl ofs ty).
Case Lsetstack r sl ofs ty := (fun funct => slot_valid funct sl ofs ty && slot_writable sl).
Case Lop op args res :=
  (fun funct =>
     match is_move_operation op args with
      | Some arg =>
          subtype (mreg_type arg) (mreg_type res)
      | None =>
          let (targs, tres) := type_of_operation op in
          subtype tres (mreg_type res)
     end).
Case _ := (fun _ => true).
FEnd wt_instr.

FDefinition wt_code := fun (f: S.function) (c: S.code) =>
   forallb (fun i => wt_instr i f) c.
FDefinition wt_function := fun (f: S.function) =>
  wt_code f (S.fn_code f).

FDefinition wt_locset : S.locset -> Prop := fun ls =>
  forall l, Val.has_type (ls l) (Loc.type l).

FLemma wt_setreg:
  forall ls r v,
  Val.has_type v (mreg_type r) -> wt_locset ls -> wt_locset (Locmap.set (R r) v ls).
FProofLemma.
  intros; red; intros.
  unfold Locmap.set.
  destruct (Loc.eq (R r) l).
  subst l; auto.
  destruct (Loc.diff_dec (R r) l). auto. red. auto.
Qed. CloseFLemma.

FLemma wt_setstack:
  forall ls sl ofs ty v,
  wt_locset ls -> wt_locset (Locmap.set (Locations.S sl ofs ty) v ls).
FProofLemma.
  intros; red; intros.
  unfold Locmap.set.
  destruct (Loc.eq (S sl ofs ty) l).
  subst l. simpl.
  generalize (Val.load_result_type (chunk_of_type ty) v).
  replace (type_of_chunk (chunk_of_type ty)) with ty. auto.
  destruct ty; reflexivity.
  destruct (Loc.diff_dec (S sl ofs ty) l). auto. red. auto.
Qed. CloseFLemma.

FLemma wt_undef_regs:
  forall rs ls, wt_locset ls -> wt_locset (S.undef_regs rs ls).
FProofLemma.
  induction rs; simpl; intros. auto. apply wt_setreg; auto. red; auto.
Qed. CloseFLemma.

FLemma wt_call_regs:
  forall ls, wt_locset ls -> wt_locset (S.call_regs ls).
FProofLemma.
  intros; red; intros. unfold S.call_regs. destruct l. auto.
  destruct sl.
  red; auto.
  change (Loc.type (Locations.S Incoming pos ty)) with (Loc.type (Locations.S Outgoing pos ty)). auto.
  red; auto.
Qed. CloseFLemma.

FLemma wt_return_regs:
  forall caller callee,
  wt_locset caller -> wt_locset callee -> wt_locset (S.return_regs caller callee).
FProofLemma.
  intros; red; intros.
  unfold S.return_regs. destruct l.
- destruct (is_callee_save r); auto.
- destruct sl; auto; red; auto.
Qed. CloseFLemma.

FLemma wt_undef_caller_save_regs:
  forall ls, wt_locset ls -> wt_locset (S.undef_caller_save_regs ls).
FProofLemma.
  intros; red; intros. unfold S.undef_caller_save_regs.
  destruct l.
  destruct (is_callee_save r); auto; simpl; auto.
  destruct sl; auto; red; auto.
Qed. CloseFLemma.

FLemma wt_init:
  wt_locset (Locmap.init Vundef).
FProofLemma.
  red; intros. unfold Locmap.init. red; auto.
Qed. CloseFLemma.

FLemma wt_setpair:
  forall sg v rs,
  Val.has_type v (proj_sig_res sg) ->
  wt_locset rs ->
  wt_locset (Locmap.setpair (loc_result sg) v rs).
FProofLemma.
  intros. generalize (loc_result_pair sg) (loc_result_type sg).
  destruct (loc_result sg); simpl Locmap.setpair.
- intros. apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- intros A B. decompose [and] A.
  apply wt_setreg. eapply Val.has_subtype; eauto. destruct v; exact I.
  apply wt_setreg. eapply Val.has_subtype; eauto. destruct v; exact I.
  auto.
Qed. CloseFLemma.

FLemma wt_setres:
  forall res ty v rs,
  wt_builtin_res ty res = true ->
  Val.has_type v ty ->
  wt_locset rs ->
  wt_locset (Locmap.setres res v rs).
FProofLemma.
  induction res; simpl; intros.
- apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- auto.
- InvBooleans. eapply IHres2; eauto. destruct v; exact I.
  eapply IHres1; eauto. destruct v; exact I.
Qed. CloseFLemma.

FLemma wt_find_label:
  forall f lbl c,
  wt_function f = true ->
  S.find_label lbl (S.fn_code f) = Some c ->
  wt_code f c = true.
FProofLemma.
  unfold wt_function; intros until c. generalize (S.fn_code f). induction c0; simpl; intros.
  discriminate.
  InvBooleans. destruct (S.is_label a lbl).
  congruence.
  auto.
Qed. CloseFLemma.

FDefinition agree_outgoing_arguments := fun (sg: signature) (ls pls: S.locset) =>
  forall ty ofs,
  In (Locations.S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
  ls (Locations.S Outgoing ofs ty) = pls (Locations.S Outgoing ofs ty).

FDefinition outgoing_undef : S.locset -> Prop := fun ls =>
  forall ty ofs, ls (Locations.S Outgoing ofs ty) = Vundef.

FDefinition wt_fundef := fun (fd: S.fundef) =>
  match fd with
  | AST.Internal f => wt_function f = true
  | AST.External ef => True
  end.

MetaData wt_callstack binds wt_callstack_nil, wt_callstack_cons.
Inductive wt_callstack: list S.stackframe -> Prop :=
  | wt_callstack_nil:
      wt_callstack nil
  | wt_callstack_cons: forall f sp rs c s
        (WTSTK: wt_callstack s)
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs),
      wt_callstack (S.Stackframe f sp rs c :: s).
FEnd wt_callstack.

FLemma wt_parent_locset:
  forall s, wt_callstack s -> wt_locset (S.parent_locset s).
FProofLemma.
  induction 1; simpl.
- apply wt_init.
- auto.
Qed. CloseFLemma.

MetaData wt_state.
Inductive wt_state: S.state -> Prop :=
  | wt_regular_state: forall s f sp c rs m
        (WTSTK: wt_callstack s )
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs),
      wt_state (S.State s f sp c rs m)
  | wt_call_state: forall s fd rs m
        (WTSTK: wt_callstack s)
        (WTFD: wt_fundef fd)
        (WTRS: wt_locset rs)
        (AGCS: agree_callee_save rs (S.parent_locset s))
        (AGARGS: agree_outgoing_arguments (S.funsig fd) rs (S.parent_locset s)),
      wt_state (S.Callstate s fd rs m)
  | wt_return_state: forall s rs m
        (WTSTK: wt_callstack s)
        (WTRS: wt_locset rs)
        (AGCS: agree_callee_save rs (S.parent_locset s))
        (UOUT: outgoing_undef rs),
      wt_state (S.Returnstate s rs m).
FEnd wt_state.

FLemma wt_state_getstack:
  forall s f sp sl ofs ty rd c rs m,
  wt_state (S.State s f sp (S.Lgetstack sl ofs ty rd :: c) rs m) ->
  slot_valid f sl ofs ty = true.
FProofLemma.
  intros. inv H. simpl in WTC; fsimpl in WTC; InvBooleans. auto.
Qed. CloseFLemma.

FLemma wt_state_setstack:
  forall s f sp sl ofs ty r c rs m,
  wt_state (S.State s f sp (S.Lsetstack r sl ofs ty :: c) rs m) ->
  slot_valid f sl ofs ty = true /\ slot_writable sl = true.
FProofLemma.
  intros. inv H. simpl in WTC; fsimpl in WTC; InvBooleans. intuition.
Qed. CloseFLemma.

FLemma wt_callstate_wt_regs:
  forall s f rs m,
  wt_state (S.Callstate s f rs m) ->
  forall r, Val.has_type (rs (R r)) (mreg_type r).
FProofLemma.
  intros. inv H. apply WTRS.
Qed. CloseFLemma.

FLemma wt_callstate_agree:
  forall s f rs m,
  wt_state (S.Callstate s f rs m) ->
  agree_callee_save rs (S.parent_locset s) /\ agree_outgoing_arguments (S.funsig f) rs (S.parent_locset s).
FProofLemma.
  intros. inv H; auto.
Qed. CloseFLemma.

FLemma wt_returnstate_agree:
  forall s rs m,
  wt_state (S.Returnstate s rs m) ->
  agree_callee_save rs (S.parent_locset s) /\ outgoing_undef rs.
FProofLemma.
  intros. inv H; auto.
Qed. CloseFLemma.

From Rocqet Require Import Bounds.
(* Fields in bounds that depend on late bound names *)

FRecursion record_regs_of_instr about S.instruction motive
  (fun (_ : S.instruction) => Bounds.RegSet.t -> Bounds.RegSet.t) by _rect.
Case Lreturn := (fun u => u).
Case Lgetstack sl ofs ty r := (fun u => record_reg u r).
Case Lsetstack r sl ofs ty := (fun u => record_reg u r).
Case Lop op args res := (fun u => record_reg u res).
Case Llabel lbl := (fun u => u).
Case Lgoto lbl := (fun u => u).
Case Lcond cond args lbl := (fun u => u).
FEnd record_regs_of_instr.

FDefinition record_regs_of_function : S.function -> Bounds.RegSet.t := fun f =>
  fold_left (fun u i => record_regs_of_instr i u) (S.fn_code f) Bounds.RegSet.empty.

FRecursion slots_of_instr about S.instruction motive
  (fun (_ : S.instruction) => list (slot * Z * typ)) by _rect.
Case Lreturn := nil.
Case Lgetstack sl ofs ty r := ((sl, ofs, ty) :: nil).
Case Lsetstack r sl ofs ty := ((sl, ofs, ty) :: nil).
Case Lop op args res := nil.
Case Llabel lbl := nil.
Case Lgoto lbl := nil.
Case Lcond cond args lbl := nil.
FEnd slots_of_instr.

FRecursion outgoing_space about S.instruction motive
  (fun (_ : S.instruction) => Z) by _rect.
Case Lreturn := 0.
Case Lgetstack sl ofs ty r := 0.
Case Lsetstack r sl ofs ty := 0.
Case Lop op args res := 0.
Case Llabel lbl := 0.
Case Lgoto lbl := 0.
Case Lcond cond args lbl := 0.
FEnd outgoing_space.

FDefinition max_over_instrs : (S.instruction -> Z) -> S.function -> Z := fun valu f =>
  max_over_list valu (S.fn_code f).

FDefinition max_over_slots_of_instr : (slot * Z * typ -> Z) -> S.instruction -> Z := fun valu i =>
  max_over_list valu (slots_of_instr i).

FDefinition max_over_slots_of_funct : (slot * Z * typ -> Z) -> S.function -> Z := fun valu f =>
  max_over_instrs (max_over_slots_of_instr valu) f.

FLemma max_over_list_pos:
  forall (A: Type) (valu: A -> Z) (l: list A),
  max_over_list valu l >= 0.
FProofLemma.
  intros until valu. unfold max_over_list.
  assert (forall l z, fold_left (fun x y => Z.max x (valu y)) l z >= z).
  induction l; simpl; intros.
  lia. apply Zge_trans with (Z.max z (valu a)).
  auto. apply Z.le_ge. apply Z.le_max_l. auto.
Qed. CloseFLemma.

FLemma max_over_slots_of_funct_pos:
  forall (valu: slot * Z * typ -> Z) f, max_over_slots_of_funct valu f >= 0.
FProofLemma.
  intros. unfold max_over_slots_of_funct.
  unfold max_over_instrs. apply max_over_list_pos.
Qed. CloseFLemma.

FLemma fold_left_preserves:
  forall (A B: Type) (f: A -> B -> A) (P: A -> Prop),
  (forall a b, P a -> P (f a b)) ->
  forall l a, P a -> P (fold_left f l a).
FProofLemma.
  induction l; simpl; auto.
Qed. CloseFLemma.

FLemma fold_left_ensures:
  forall (A B: Type) (f: A -> B -> A) (P: A -> Prop) b0,
  (forall a b, P a -> P (f a b)) ->
  (forall a, P (f a b0)) ->
  forall l a, In b0 l -> P (fold_left f l a).
FProofLemma.
  induction l; simpl; intros. contradiction.
  destruct H1. subst a. apply fold_left_preserves; auto. apply IHl; auto.
Qed. CloseFLemma.

FDefinition only_callee_saves : RegSet.t -> Prop :=
  fun u => forall r, RegSet.In r u -> is_callee_save r = true.

FLemma record_reg_only: forall u r, only_callee_saves u -> only_callee_saves (record_reg u r).
FProofLemma.
  unfold only_callee_saves, record_reg; intros.
  destruct (is_callee_save r) eqn:CS; auto.
  destruct (mreg_eq r r0). congruence. apply H; eapply RegSet.add_3; eauto.
Qed. CloseFLemma.

FLemma record_regs_only: forall rl u, only_callee_saves u -> only_callee_saves (record_regs u rl).
FProofLemma.
  intros. unfold record_regs. apply fold_left_preserves; auto using record_reg_only.
Qed. CloseFLemma.

FInduction record_regs_of_instr_only
  about S.instruction
  motive (fun (i : S.instruction) =>
    forall u, only_callee_saves u -> only_callee_saves (record_regs_of_instr i u)).
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FLemma record_regs_of_function_only:
  forall f, only_callee_saves (record_regs_of_function f).
FProofLemma.
  intros. unfold record_regs_of_function.
  apply fold_left_preserves. intros. apply record_regs_of_instr_only. auto.
  red; intros. eelim RegSet.empty_1; eauto.
Qed. CloseFLemma.

MetaData function_bounds.
Program Definition function_bounds (f: S.function) := {|
  used_callee_save := RegSet.elements (record_regs_of_function f);
  bound_local := max_over_slots_of_funct local_slot f;
  bound_outgoing := Z.max (max_over_instrs outgoing_space f) (max_over_slots_of_funct outgoing_slot f);
  bound_stack_data := Z.max (S.fn_stacksize f) 0
|}.
Next Obligation.
  apply max_over_slots_of_funct_pos.
Qed.
Next Obligation.
  apply Z.le_ge. eapply Z.le_trans. 2: apply Z.le_max_r.
  apply Z.ge_le. apply max_over_slots_of_funct_pos.
Qed.
Next Obligation.
  apply Z.le_ge. apply Z.le_max_r.
Qed.
Next Obligation.
  generalize (RegSet.elements_3w (record_regs_of_function f)).
  generalize (RegSet.elements (record_regs_of_function f)).
  induction 1. constructor. constructor; auto.
  red; intros; elim H. apply InA_alt. exists x; auto.
Qed.
Next Obligation.
  apply (record_regs_of_function_only f). apply RegSet.elements_2.
  apply InA_alt. exists r; auto.
Qed.
FEnd function_bounds.

From Rocqet Require Import Stacklayout.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

FDefinition offset_arg := fun (x: Z) => fe_ofs_arg + 4 * x.

FDefinition transl_op := fun (fe: frame_env) (op: Op.operation) =>
    Op.shift_stack_operation fe.(fe_stack_data) op.

MetaData save_callee_save_rec.
Fixpoint save_callee_save_rec (rl: list mreg) (ofs: Z) (k: T.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      T.Lsetstack r (Ptrofs.repr ofs1) ty :: save_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd save_callee_save_rec.

FDefinition save_callee_save := fun (fe: frame_env) (k: T.code) =>
  save_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

MetaData restore_callee_save_rec.
Fixpoint restore_callee_save_rec (rl: list mreg) (ofs: Z) (k: T.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      T.Lgetstack (Ptrofs.repr ofs1) ty r :: restore_callee_save_rec rl (ofs1 + sz) k
  end.
FEnd restore_callee_save_rec.

FDefinition restore_callee_save := fun (fe: frame_env) (k: T.code) =>
  restore_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

FRecursion transl_instr about S.instruction motive (fun (_ : S.instruction) => frame_env -> T.code -> T.code) by _rect.
Case Lgetstack sl ofs ty r :=
(fun fe k =>
match sl with
| Local =>
    T.Lgetstack (Ptrofs.repr (offset_local fe ofs)) ty r :: k
| Incoming =>
    T.Lgetparam (Ptrofs.repr (offset_arg ofs)) ty r :: k
| Outgoing =>
    T.Lgetstack (Ptrofs.repr (offset_arg ofs)) ty r :: k
end).
Case Lsetstack r sl ofs ty :=
(fun fe k =>
  match sl with
  | Local =>
      T.Lsetstack r (Ptrofs.repr (offset_local fe ofs)) ty :: k
  | Incoming =>
      k
  | Outgoing =>
      T.Lsetstack r (Ptrofs.repr (offset_arg ofs)) ty :: k
  end).
Case Lop op args res := (fun fe k =>  T.Lop (transl_op fe op) args res :: k).
Case Llabel lbl := (fun fe k => T.Llabel lbl :: k).
Case Lgoto lbl := (fun fe k => T.Lgoto lbl :: k).
Case Lcond cond args lbl := (fun fe k => T.Lcond cond args lbl :: k).
Case Lreturn := (fun fe k =>  restore_callee_save fe (T.Lreturn :: k)).
FEnd transl_instr.

FDefinition transl_code : frame_env -> list S.instruction -> T.code := fun fe il =>
  list_fold_right (fun i k => transl_instr i fe k) il nil.

FDefinition transl_body := fun (f: S.function) (fe: frame_env) =>
  save_callee_save fe (transl_code fe (S.fn_code f)).

Local Open Scope string_scope.

FDefinition transf_function : S.function -> res T.function := fun f =>
  let fe := make_env (function_bounds f) in
  if negb (wt_function f) then
    Error (msg "Ill-formed Linear code")
  else if zlt Ptrofs.max_unsigned fe.(fe_size) then
    Error (msg "Too many spilled variables, stack size exceeded")
  else
    OK (T.mkfunction
         (S.fn_sig f)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr))).

FDefinition transf_fundef : S.fundef -> res T.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res T.program := fun p =>
  transform_partial_program transf_fundef p.

FEnd Stacking.

FEnd Base.

Trait Comp_Loops extends Base.

Family Lfam.
FInductive instruction: Type :=
| Ljumptable : mreg -> list label -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

Family Linear extends Lfam.
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ljumptable:
      forall ge s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl (fn_code f) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step ge (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' rs' m).
FEnd Linear.

Family Mach extends Lfam.
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Ljumptable:
      forall ge s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      find_label lbl (fn_code f) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step ge (State s fb sp (Ljumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m).
FEnd Mach.

Trait Stacking_jumptable extends Stacking.

FRecursion wt_instr.
Case Ljumptable arg tbl := (fun funct => true).
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case Ljumptable arg tbl := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case Ljumptable arg tbl := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FRecursion transl_instr.
Case Ljumptable arg tbl := (fun fe k => T.Ljumptable arg tbl :: k).
FEnd transl_instr.
FEnd Stacking_jumptable.

Family Stacking extends Stacking_jumptable.

FRecursion instr_within_bounds.
Case _ := (fun b => True).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case _ := (fun r' => False).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
Qed. FEnd record_regs_of_instr_ok.


FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
simpl; do 4 fsimpl; simpl; intros; auto.
Qed. FEnd instr_is_within_bounds.

Inherit no_callee_saves.

FLemma destroyed_by_jumptable_caller_save:
  no_callee_saves destroyed_by_jumptable.
FProofLemma.
  red; reflexivity.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros; try inv MS; try rewrite transl_code_eq; try (generalize (function_is_within_bounds f _ (is_tail_in TAIL)); intro BOUND; simpl in BOUND); fsimpl in *.
(* Ljumptable *)
+  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite e. intro IJ; inv IJ; auto. }
  econstructor; split.
  apply plus_one; eapply T.exec_Ljumptable; eauto.
  apply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_jumptable_caller_save.
  auto. eapply find_label_tail; eauto.
  apply frame_undef_regs; auto.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Linear.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin:
      forall ge s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (State s f sp (Lbuiltin ef args res :: b) rs m)
        t (State s f sp b rs' m').
FEnd Linear.

Family Mach.
FInductive instruction : Type :=
| Lbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

MetaData set_res.
Fixpoint set_res (res: builtin_res mreg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => Regmap.set r v rs
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.
FEnd set_res.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lbuiltin:
      forall ge s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args (Genv.to_senv ge) rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step ge (State s f sp (Lbuiltin ef args res :: b) rs m)
        t (State s f sp b rs' m').

FEnd Mach.

Family Stacking.

FRecursion wt_instr.
Case Lbuiltin ef args res := (fun funct =>
      wt_builtin_res (proj_sig_res (ef_sig ef)) res
      && forallb (loc_valid funct) (params_of_builtin_args args)).
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case _ := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FDefinition offset_local := fun (fe: frame_env) (x: Z) => fe.(fe_ofs_local) + 4 * x.

MetaData transl_builtin_arg.
Fixpoint transl_builtin_arg (fe: frame_env) (a: builtin_arg loc) : builtin_arg mreg :=
  match a with
  | BA (R r) => BA r
  | BA (S Local ofs ty) =>
      BA_loadstack (chunk_of_type ty) (Ptrofs.repr (offset_local fe ofs))
  | BA (S _ _ _) => BA_int Int.zero(* never happens *)
  | BA_int n => BA_int n
  | BA_long n => BA_long n
  | BA_float n => BA_float n
  | BA_single n => BA_single n
  | BA_loadstack chunk ofs =>
      BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr fe.(fe_stack_data)))
  | BA_addrstack ofs =>
      BA_addrstack (Ptrofs.add ofs (Ptrofs.repr fe.(fe_stack_data)))
  | BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
  | BA_addrglobal id ofs => BA_addrglobal id ofs
  | BA_splitlong hi lo =>
      BA_splitlong (transl_builtin_arg fe hi) (transl_builtin_arg fe lo)
  | BA_addptr a1 a2 =>
      BA_addptr (transl_builtin_arg fe a1) (transl_builtin_arg fe a2)
  end.
FEnd transl_builtin_arg.

FRecursion transl_instr.
Case Lbuiltin ef args dst := (fun fe k => T.Lbuiltin ef (map (transl_builtin_arg fe) args) dst :: k).
FEnd transl_instr.

FRecursion instr_within_bounds.
Case Lbuiltin ef args res := (fun b =>
       (forall r, In r (params_of_builtin_res res) \/ In r (destroyed_by_builtin ef) -> mreg_within_bounds b r)
       /\ (forall sl ofs ty, In (Locations.S sl ofs ty) (params_of_builtin_args args) -> slot_within_bounds b sl ofs ty)).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case Lbuiltin ef args res := (fun r' => In r' (params_of_builtin_res res) \/ In r' (destroyed_by_builtin ef)).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

Inherit record_reg_ok.

FLemma record_regs_ok: forall r rl u, In r rl -> is_callee_save r = true -> RegSet.In r (record_regs u rl).
FProofLemma.
  intros. unfold record_regs. eapply fold_left_ensures; eauto using record_reg_incr, record_reg_ok.
Qed. CloseFLemma.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
(* TODO: I think this is easy *)
apply cheat.
(* + destruct H; auto using record_regs_incr, record_regs_ok.*)
(*+ destruct H. eapply record_regs_ok in H0.
  assert (A : RegSet.In r' u).
  apply record_regs_incr. auto using record_regs_incr, record_regs_ok.   *)
Qed. FEnd record_regs_of_instr_ok.

MetaData slots_of_locs.
Fixpoint slots_of_locs (l: list loc) : list (slot * Z * typ) :=
  match l with
  | nil => nil
  | S sl ofs ty :: l' => (sl, ofs, ty) :: slots_of_locs l'
  | R r :: l' => slots_of_locs l'
  end.
FEnd slots_of_locs.

FLemma slots_of_locs_charact:
  forall sl ofs ty l, In (sl, ofs, ty) (slots_of_locs l) <-> In (Locations.S sl ofs ty) l.
FProofLemma.
  induction l; simpl; intros.
  tauto.
  destruct a; simpl; intuition congruence.
Qed. CloseFLemma.

FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
  simpl; do 4 fsimpl; simpl; intros; auto.
 split; intros.
  apply H1; auto.
  (* apply H0. rewrite slots_of_locs_charact; auto.*)
  (* TODO: this shouldn't be too hard *)
  apply cheat.
Qed. FEnd instr_is_within_bounds.

Inherit frame_get_local.

FLemma transl_builtin_arg_correct:
  forall (ge: S.genv) (f: S.function)
         (tf: T.function),
  let b := function_bounds f in
  let fe := make_env b in
  forall (TRANSF_F: transf_function f = OK tf)
  (j: meminj)
  (m m': mem)
  (ls ls0: S.locset)
  (rs: regset)
  (sp sp': block)
  (parent retaddr: val)
  (INJ: j sp = Some(sp', fe.(fe_stack_data)))
  (AGR: agree_regs j ls rs)
  (SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject ge j) a v,
  eval_builtin_arg ge ls (Vptr sp Ptrofs.zero) m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (Locations.S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg ge rs (Vptr sp' Ptrofs.zero) m' (transl_builtin_arg fe a) v'
  /\ Val.inject j v v'.
FProofLemma.
  intros until retaddr. intros INJ AGR SEP. assert (SYMB: forall id ofs, Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address ge id ofs)).
  { assert (G: meminj_preserves_globals ge j).
    { eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eexact SEP. }
    intros; unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) eqn:FS; auto.
    destruct G. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
(* Local Opaque fe.*)
  induction 1; (*simpl;*) intros VALID BOUNDS.
- simpl in VALID. assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + simpl. exists (rs r); auto with barg.
  + simpl in BOUNDS. exploit frame_get_local; eauto. intros (v & A & B).
    exists v; split; auto. constructor; auto.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; eauto with barg.
- simpl in BOUNDS. simpl in VALID. set (ofs' := Ptrofs.add ofs (Ptrofs.repr (fe_stack_data (make_env (function_bounds f))))).
  apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  instantiate (1 := Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs').
  simpl. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; split; eauto with barg.
  unfold Val.offset_ptr. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
- simpl in BOUNDS. simpl in VALID. simpl. apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. econstructor; split; eauto with barg.
- simpl in BOUNDS. simpl in VALID. simpl. destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_inject; auto.
- simpl in BOUNDS. simpl in VALID. simpl. destruct IHeval_builtin_arg1 as (v1' & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); auto using in_or_app.
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed. CloseFLemma.

FLemma transl_builtin_args_correct:
  forall (ge: S.genv) (f: S.function)
         (tf: T.function),
  let b := function_bounds f in
  let fe := make_env b in
  forall (TRANSF_F: transf_function f = OK tf)
  (j: meminj)
  (m m': mem)
  (ls ls0: S.locset)
  (rs: regset)
  (sp sp': block)
  (parent retaddr: val)
  (INJ: j sp = Some(sp', fe.(fe_stack_data)))
  (AGR: agree_regs j ls rs)
  (SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject ge j) al vl,
  eval_builtin_args ge ls (Vptr sp Ptrofs.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (Locations.S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args ge rs (Vptr sp' Ptrofs.zero) m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.inject_list j vl vl'.
FProofLemma.
  intros until retaddr. intros INJ AGR SEP. induction 1; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed. CloseFLemma.

FLemma wt_state_builtin:
  forall s f sp ef args res c rs m,
  wt_state (S.State s f sp (S.Lbuiltin ef args res :: c) rs m) ->
  forallb (loc_valid f) (params_of_builtin_args args) = true.
FProofLemma.
  intros. inv H. simpl in WTC. fsimpl in WTC; InvBooleans. auto.
Qed. CloseFLemma.

FLemma senv_preserved: forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.senv_match TRANSL).
Qed. CloseFLemma.

FLemma agree_regs_set_res:
  forall j res v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setres res v ls) (T.set_res res v' rs).
FProofLemma.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed. CloseFLemma.

FLemma agree_locs_set_res:
  forall f ls0 res v ls,
  let b := function_bounds f in
  let fe := make_env b in
  agree_locs f ls ls0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_locs f (Locmap.setres res v ls) ls0.
FProofLemma.
  induction res; simpl; intros.
- eapply agree_locs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed. CloseFLemma.

FLemma frame_set_res:
  forall f j sp ls0 parent retaddr m P res v ls,
  m |= frame_contents f j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents f j sp (Locmap.setres res v ls) ls0 parent retaddr ** P.
FProofLemma.
  induction res; (*simpl;*) intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros;
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND); fsimpl in *.
(* Lbuiltin *)
+ fsimpl in BOUND. destruct BOUND as [BND1 BND2].
  exploit transl_builtin_args_correct.
    eauto. eauto. exact AGREGS. rewrite sep_swap in SEP; apply sep_proj2 in SEP; eexact SEP.
    eauto. rewrite <- forallb_forall. eapply wt_state_builtin; eauto.
    exact BND2.
  intros [vargs' [P Q]].
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  exploit external_call_parallel_rule; eauto.
  clear SEP; intros (j' & res' & m1' & EC & RES & SEP & INCR & ISEP).
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  econstructor; split.
  apply plus_one. fconstructor; eauto.
  eapply eval_builtin_args_preserved with (ge1 := (Genv.globalenv prog)); eauto. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  eapply external_call_symbols_preserved; eauto. apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  eapply match_states_intro with (j := j'); eauto with coqlib.
  eapply match_stacks_change_meminj; eauto.
  apply agree_regs_set_res; auto. apply agree_regs_undef_regs; auto. eapply agree_regs_inject_incr; eauto.
  apply agree_locs_set_res; auto. apply agree_locs_undef_regs; auto.
  apply frame_set_res. apply frame_undef_regs. apply frame_contents_incr with j; auto.
  rewrite sep_swap2. apply stack_contents_change_meminj with j; auto. rewrite sep_swap2.
  exact SEP.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
| Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

Family Linear extends Lfam.
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lload:
      forall ge s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step ge (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b rs' m)
| exec_Lstore:
      forall ge s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step ge (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs' m').

FEnd Linear.

Family Mach extends Lfam.
FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lload:
      forall ge s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step ge (State s f sp (Lload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
| exec_Lstore:
      forall ge s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step ge (State s f sp (Lstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m').
FEnd Mach.

Family Stacking.

FRecursion wt_instr.
Case Lload chunk addr args dst :=
  (fun funct => subtype (type_of_chunk chunk) (mreg_type dst)).
Case Lstore chunk addr args src := (fun funct => true).
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case Lload chunk addr args dst := (fun u => record_reg u dst).
Case Lstore chunk addr args src := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FDefinition transl_addr := fun (fe: frame_env) (addr: addressing) =>
  shift_stack_addressing fe.(fe_stack_data) addr.

FDefinition simplify_load := fun chunk =>
  match chunk with
  | Mbool => Mint8unsigned
  | _ => chunk
  end.

FDefinition simplify_store := fun chunk =>
  match chunk with
  | Mbool => Mint8unsigned
  | Mint8signed => Mint8unsigned
  | Mint16signed => Mint16unsigned
  | _ => chunk
  end.

FRecursion transl_instr.
Case Lload chunk addr args dst :=
 (fun fe k => T.Lload (simplify_load chunk) (transl_addr fe addr) args dst :: k).
Case Lstore chunk addr args src :=
 (fun fe k => T.Lstore (simplify_store chunk) (transl_addr fe addr) args src :: k).
FEnd transl_instr.

FRecursion instr_within_bounds.
Case Lload chunk addr args dst := (fun b => mreg_within_bounds b dst).
Case _ := (fun b => True).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case Lload chunk addr args dst := (fun r' => r' = dst).
Case _ := (fun r' => False).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
Qed. FEnd record_regs_of_instr_ok.

FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
simpl; do 4 fsimpl; simpl; intros; auto.
Qed. FEnd instr_is_within_bounds.

FLemma simplify_load_correct: forall chunk m a v,
  Mem.loadv chunk m a = Some v ->
  exists v', Mem.loadv (simplify_load chunk) m a = Some v' /\ Val.lessdef v v'.
FProofLemma.
  intros. destruct a; simpl in *; try discriminate.
  destruct chunk; simpl; try (exists v; auto; fail).
  rewrite Mem.load_bool_int8_unsigned in H.
  destruct (Mem.load Mint8unsigned m b (Ptrofs.unsigned i)) as [v'|]; simpl in H; inv H.
  exists v'; auto using Val.norm_bool_is_lessdef.
Qed. CloseFLemma.

FLemma simplify_store_correct: forall chunk m a v m',
  Mem.storev chunk m a v = Some m' ->
  Mem.storev (simplify_store chunk) m a v = Some m'.
FProofLemma.
  intros. destruct a; simpl in *; try discriminate. rewrite <- H. symmetry.
  destruct chunk; simpl; auto.
- apply Mem.store_bool_unsigned_8.
- apply Mem.store_signed_unsigned_8.
- apply Mem.store_signed_unsigned_16.
Qed. CloseFLemma.

FLemma simplify_load_destroyed: forall chunk addr,
  destroyed_by_load (simplify_load chunk) addr = destroyed_by_load chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

FLemma simplify_store_destroyed: forall chunk addr,
  destroyed_by_store (simplify_store chunk) addr = destroyed_by_store chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

Inherit no_callee_saves.
Inherit ByCases.

FLemma destroyed_by_load_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_load chunk addr).
FProofLemma.
Local Transparent destroyed_by_load.
  intros; unfold destroyed_by_load; ByCases.
Qed. CloseFLemma.

FLemma transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

FLemma transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
FProofLemma.
  intros; destruct chunk; reflexivity.
Qed. CloseFLemma.

FLemma destroyed_by_store_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_store chunk addr).
FProofLemma.
Local Transparent destroyed_by_store.
  intros; unfold destroyed_by_store; ByCases.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros; try inv MS; try rewrite transl_code_eq; try (generalize (function_is_within_bounds f _ (is_tail_in TAIL)); intro BOUND; simpl in BOUND); fsimpl in *.
(* Lload *)
+ assert (exists a',
          eval_addressing (Genv.globalenv prog) (Vptr sp' Ptrofs.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ Val.inject j a a').
  eapply eval_addressing_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  eapply agree_reglist; eauto.
  destruct H as [a' [A B]].
  exploit loadv_parallel_rule.
  apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. eexact SEP.
  eauto. eauto.
  intros [v' [C D]].
  exploit simplify_load_correct; eauto.
  intros [v'' [E F]].
  assert (G: Val.inject j v v'').
  { inv F; auto. inv D; auto. }
  econstructor; split.
  apply plus_one. eapply T.exec_Lload. (* fconstructor. *)
  instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  eexact E. eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg. rewrite transl_destroyed_by_load, simplify_load_destroyed. apply agree_regs_undef_regs; auto. auto.
  apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_load_caller_save. fsimpl in BOUND. auto.

(* Lstore *)
+ assert (exists a',
          eval_addressing (Genv.globalenv prog) (Vptr sp' Ptrofs.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ Val.inject j a a').
  eapply eval_addressing_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  eapply agree_reglist; eauto.
  destruct H as [a' [A B]].
  rewrite sep_swap3 in SEP.
  exploit storev_parallel_rule. eexact SEP. eauto. eauto. apply AGREGS.
  clear SEP; intros (m1' & C & SEP).
  rewrite sep_swap3 in SEP.
  econstructor; split.
  apply plus_one. eapply T.exec_Lstore.
  instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  apply simplify_store_correct. eexact C. eauto.
  econstructor. eauto. eauto. eauto.
  rewrite transl_destroyed_by_store, simplify_store_destroyed. apply agree_regs_undef_regs; auto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
  auto. eauto with coqlib.
  eapply frame_undef_regs; eauto.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap. FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Lfam.
FInductive instruction: Type :=
| Lcall: signature -> mreg + ident -> instruction
| Ltailcall: signature -> mreg + ident -> instruction.

FRecursion is_label.
Case _ := (fun lbl => false).
FEnd is_label.

FEnd Lfam.

Family Linear extends Lfam.
Inherit locset.

FDefinition find_function := fun (ge: genv) (ros: mreg + ident) (rs: locset) =>
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lcall:
      forall ge s f sp sig ros b rs m f',
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      step ge (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) f' rs m)
| exec_Ltailcall:
      forall ge s f stk sig ros b rs m rs' f' m',
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 (fn_stacksize f) = Some m' ->
      step ge (State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s f' rs' m').
FEnd Linear.

Family Mach extends Lfam.

Inherit genv.

FDefinition find_function_ptr
        := fun (ge: genv) (ros: mreg + ident) (rs: regset) =>
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

(* To be provided by Asmgen *)
(* In CompCert, `return_address_offset` is a parameter to step *)
(* Here we (ab)use(?) the implicit self parameterization of family polymorphism to make it a parameter *)
FOpaque Definition return_address_offset: function -> code -> ptrofs -> Prop := cheat.

FInductive step: genv -> state -> trace -> state -> Prop :=
| exec_Lcall:
      forall ge s fb sp sig ros c rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      return_address_offset f c ra ->
      step ge (State s fb sp (Lcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs m)
| exec_Ltailcall:
      forall ge s fb stk soff sig ros c rs m f f' m',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (AST.Internal f) ->
      load_stack m (Vptr stk soff) Tptr (fn_link_ofs f) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr (fn_retaddr_ofs f) = Some (parent_ra s) ->
      Mem.free m stk 0 (fn_stacksize f) = Some m' ->
      step ge (State s fb (Vptr stk soff) (Ltailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m').
FEnd Mach.

Family Stacking.

FRecursion wt_instr.
Case _ := (fun funct => true).
(*Case Lcall sig ros := (fun funct => ).
Case Ltailcall sig ros := (fun funct => ).*)
FEnd wt_instr.

FRecursion record_regs_of_instr.
Case _ := (fun u => u).
FEnd record_regs_of_instr.

FRecursion slots_of_instr.
Case _ := nil.
FEnd slots_of_instr.

FRecursion outgoing_space.
Case _ := 0.
FEnd outgoing_space.

FInduction record_regs_of_instr_only.
FProof.
all: intros; fsimpl; auto using record_reg_only, record_regs_only.
Qed. FEnd record_regs_of_instr_only.

FRecursion transl_instr.
Case Lcall sig ros :=
 (fun fe k => T.Lcall sig ros :: k).
Case Ltailcall sig ros :=
  (fun fe k => restore_callee_save fe (T.Ltailcall sig ros :: k)).
FEnd transl_instr.

FRecursion instr_within_bounds.
Case Lcall sig ros := (fun b => size_arguments sig <= bound_outgoing b).
Case _ := (fun b => True).
FEnd instr_within_bounds.

FRecursion defined_by_instr.
Case _ := (fun r' => False).
FEnd defined_by_instr.

FInduction record_regs_of_instr_incr.
FProof.
all: intros; fsimpl; auto using record_reg_incr, record_regs_incr.
Qed. FEnd record_regs_of_instr_incr.

FInduction record_regs_of_instr_ok.
FProof.
all: intros; fsimpl in *; fsimpl in *; try contradiction; subst; auto using record_reg_ok.
Qed. FEnd record_regs_of_instr_ok.

FLemma size_arguments_bound:
  forall f sig ros,
  In (S.Lcall sig ros) (S.fn_code f) ->
  size_arguments sig <= bound_outgoing (function_bounds f).
FProofLemma.
(* TODO *)
apply cheat.
(* intros. change (size_arguments sig) with (outgoing_space (S.Lcall sig ros)).
  unfold function_bounds, bound_outgoing.
  apply Zmax_bound_l. apply max_over_instrs_bound; auto.*)
Qed. CloseFLemma.

FInduction instr_is_within_bounds.
FProof.
all: intros; generalize (mreg_is_within_bounds _ _ H); generalize (slot_is_within_bounds _ _ H);
  simpl; do 4 fsimpl; simpl; intros; auto.
eapply size_arguments_bound; eauto.
Qed. FEnd instr_is_within_bounds.

Inherit function_ptr_translated.

FLemma find_function_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall j ls rs m ros f,
  agree_regs j ls rs ->
  m |= globalenv_inject ge j ->
  S.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     T.find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
FProofLemma.
  intros until f; intros AG [bound [_ [?????]]] FF.
  destruct ros; simpl in FF.
- exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF.
  rewrite Genv.find_funct_find_funct_ptr in FF.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  rewrite DOMAIN in H5. inv H5. simpl. auto. eapply FUNCTIONS; eauto.
- destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl. subst. (* rewrite H1.*)
  rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) H eq_refl eq_refl).  auto.
Qed. CloseFLemma.

FOpaque Definition return_address_offset_exists:
  forall f sg ros c,
    is_tail (T.Lcall sg ros :: c) (T.fn_code f) ->
  exists ofs, T.return_address_offset f c ofs := cheat.

FLemma is_tail_save_callee_save:
  forall l ofs k,
  is_tail k (save_callee_save_rec l ofs k).
FProofLemma.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto.
Qed. CloseFLemma.

FLemma is_tail_restore_callee_save:
  forall l ofs k,
  is_tail k (restore_callee_save_rec l ofs k).
FProofLemma.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto.
Qed. CloseFLemma.

FInduction is_tail_transl_instr about S.instruction motive
  (fun (i : S.instruction) =>
     forall fe k, is_tail k (transl_instr i fe k)).
FProof.
all: intros; fsimpl; auto with coqlib.
+ unfold restore_callee_save. eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
+ unfold restore_callee_save. eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
+ destruct s; auto with coqlib.
+ destruct s; auto with coqlib.
Qed. FEnd is_tail_transl_instr.

FLemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
FProofLemma.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq.
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed. CloseFLemma.

FLemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (S.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (T.fn_code tf).
FProofLemma.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body, save_callee_save.
  eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed. CloseFLemma.

FLemma match_stacks_change_sig:
  forall ge tge sg1 j cs cs' sg,
  match_stacks ge tge j cs cs' sg ->
  tailcall_possible sg1 ->
  match_stacks ge tge j cs cs' sg1.
FProofLemma.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto. intros. elim (H0 _ H1).
Qed. CloseFLemma.

(* This should be in Conventions? *)
FLemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 -> tailcall_possible sg.
FProofLemma.
  intros; red; intros. exploit loc_arguments_acceptable_2; eauto.
  unfold loc_argument_acceptable.
  destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
  generalize (loc_arguments_bounded _ _ _ H0).
  generalize (typesize_pos ty). lia.
Qed. CloseFLemma.

FLemma wt_state_tailcall:
  forall s f sp sg ros c rs m,
  wt_state (S.State s f sp (S.Ltailcall sg ros :: c) rs m) ->
  size_arguments sg = 0.
FProofLemma.
  intros. inv H. simpl in WTC. fsimpl in WTC. apply cheat. (* why? InvBooleans. auto.*)
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
all: intros; try inv MS; try rewrite transl_code_eq; try (generalize (function_is_within_bounds f _ (is_tail_in TAIL)); intro BOUND; simpl in BOUND); fsimpl in *.
(* Lcall *)
+ exploit find_function_translated; eauto.
    eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. fsimpl in IST. eexact IST. intros [ra D].
  econstructor; split.
  apply plus_one. fconstructor; eauto.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  apply Val.Vptr_has_type.
  do 2 fsimpl in IST. fsimpl in BOUND.
  intros; red.
    apply Z.le_trans with (size_arguments (S.funsig f')). auto.
    apply loc_arguments_bounded; auto. auto.
    unfold stack_contents. fold stack_contents.
  rewrite sep_assoc. exact SEP.

(* Ltailcall*)
+ rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  clear SEP. intros (rs1 & m1' & P & Q & R & S & T & U & SEP).
  rewrite sep_swap in SEP.
  exploit find_function_translated; eauto.
    eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  econstructor; split.
  eapply plus_right. eexact S. fconstructor; eauto. traceEq.
  econstructor; eauto.
  apply match_stacks_change_sig with (S.fn_sig f); auto.
  apply zero_size_arguments_tailcall_possible. eapply wt_state_tailcall; eauto.
Qed. FEnd transf_step_correct.

FEnd Stacking.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops. FEnd Comp_Switch.

Family Comp extends
  Comp_Heap,
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Field,
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin.

Family Stacking.
Final Family S := Linear.
Final Family T := Mach.
FEnd Stacking.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction Comp.Stacking.
Extraction Library X.

