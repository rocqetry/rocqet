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

Require Import LTL.
Require Import LfamBase.
Require Import Linear.

From Rocqet Require Import Registers.     

From Rocqet Require Import Machregs.

From Rocqet Require Import Conventions1.
From Rocqet Require Import Locations.

Trait Base.

(* LTL -> Linear *)
Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

From Rocqet Require Import Lattice.
From Rocqet Require Import Kildall.

(* Determination of the order of basic blocks *)

Module DS := Dataflow_Solver(LBoolean)(NodeSetForward).

FDefinition reachable_aux : S.function -> option (PMap.t bool) :=
  fun (f: S.function) =>
  DS.fixpoint
    (S.fn_code f) S.successors_block
    (fun pc r => r)
    (S.fn_entrypoint f) true.

FDefinition reachable : S.function -> PMap.t bool := fun f =>
  match reachable_aux f with
  | None => PMap.init true
  | Some rs => rs
  end.

MetaData enumerate_aux.
Parameter enumerate_aux: self__Linearize.S.function -> PMap.t bool -> list self__Linearize.S.node.
FEnd enumerate_aux.

Module Nodeset := FSetAVL.Make(OrderedPositive).

From Rocqet Require Import Errors.
Open Scope error_monad_scope.

MetaData nodeset_of_list.
Fixpoint nodeset_of_list (l: list self__Linearize.S.node) (s: Nodeset.t)
                         {struct l}: res Nodeset.t :=
  match l with
  | nil => OK s
  | hd :: tl =>
      if Nodeset.mem hd s
      then Error (msg "Linearize: duplicates in enumeration")
      else nodeset_of_list tl (Nodeset.add hd s)
  end.
FEnd nodeset_of_list.

FDefinition check_reachable_aux := 
     fun (reach: PMap.t bool) (s: Nodeset.t)
     (ok: bool) (pc: S.node) (bb: S.bblock) =>
  if reach!!pc then ok && Nodeset.mem pc s else ok.

FDefinition check_reachable := 
     fun (f: S.function) (reach: PMap.t bool) (s: Nodeset.t) =>
  PTree.fold (check_reachable_aux reach s) (S.fn_code f) true.

FDefinition enumerate : S.function -> res (list S.node) := fun f => 
  let reach := reachable f in
  let enum := enumerate_aux f reach in
  do s <- nodeset_of_list enum Nodeset.empty;
  if check_reachable f reach s
  then OK enum
  else Error (msg "Linearize: wrong enumeration").

FRecursion starts_with_label about T.instruction motive (fun (_ : T.instruction) => T.label -> bool) by _rect.
Case Llabel lbl' := (fun lbl => peq lbl lbl').
Case Lop op args res := (fun lbl => false).
Case Lgetstack sl ofs ty r := (fun lbl => false).
Case Lsetstack r sl ofs ty := (fun lbl => false).
Case Lcond cond args lbl' := (fun lbl => false).
Case Lreturn := (fun lbl => false).
Case Lgoto lbl' := (fun lbl => false).
FEnd starts_with_label.

MetaData starts_with.
Fixpoint starts_with (lbl: self__Linearize.T.label) (k: self__Linearize.T.code) {struct k} : bool :=
     match k with
     | i :: k' => if self__Linearize.starts_with_label i lbl then true else starts_with lbl k'
     | _ => false
     end.
FEnd starts_with.
              
FDefinition add_branch : T.label -> T.code -> T.code := fun (s: T.label) (k: T.code) =>
   if starts_with s k then k else T.Lgoto s :: k.

FRecursion translate_instr about S.instruction motive (fun (_ : S.instruction) => (T.code -> T.code) -> T.code -> T.code) by _rect.
Case Lop op args res := (fun f k => T.Lop op args res :: f k).
Case Lgetstack sl ofs ty r := (fun f k => T.Lgetstack sl ofs ty r :: f k).
Case Lsetstack r sl ofs ty := (fun f k => T.Lsetstack r sl ofs ty :: f k).
Case Lbranch s := (fun f k => add_branch s k).
Case Lcond cond args s1 s2 :=
(fun f k => if starts_with s1 k then T.Lcond (Op.negate_condition cond) args s2 :: add_branch s1 k else T.Lcond cond args s1 :: add_branch s2 k).
Case Lreturn := (fun f k => T.Lreturn :: f k).
FEnd translate_instr.
       
MetaData linearize_block.
Fixpoint linearize_block (b: self__Linearize.S.bblock) (k: self__Linearize.T.code) : self__Linearize.T.code :=
   match b with
   | nil => k
   | i :: b' => self__Linearize.translate_instr i (linearize_block b') k
   end.
FEnd linearize_block.

FDefinition linearize_node : S.function -> S.node -> T.code -> T.code :=
  fun (f: S.function) (pc: S.node) (k: T.code) =>
  match (S.fn_code f)!pc with
  | None => k
  | Some b => T.Llabel pc :: linearize_block b k
  end.

FDefinition linearize_body : S.function -> list S.node -> T.code :=
  fun (f: S.function) (enum: list S.node) =>
  list_fold_right (linearize_node f) enum nil.

FDefinition transf_function : S.function -> res T.function := fun f =>
  do enum <- enumerate f;
  OK (T.mkfunction
       (S.fn_sig f)
       (S.fn_stacksize f)
       (add_branch (S.fn_entrypoint f) (linearize_body f enum))).

FDefinition transf_fundef : S.fundef -> res T.fundef := fun f =>
  AST.transf_partial_fundef transf_function f.

FDefinition transf_program : S.program -> res T.program := fun p =>
  transform_partial_program transf_fundef p.

(* correctness *)

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

(*
Variable prog: LTL.program.
Variable tprog: Linear.program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
*)

MetaData match_stackframes.
Inductive match_stackframes: S.stackframe -> T.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp bb ls tf c,
      transf_function f = OK tf ->
      (forall pc, In pc (S.successors_block bb) -> (reachable f)!!pc = true) ->
      is_tail c tf.(T.fn_code) ->
      match_stackframes
        (S.Stackframe f sp ls bb)
        (T.Stackframe tf sp ls (linearize_block bb c)).
FEnd match_stackframes.

(*MetaData _blah.*)
FInductive match_states: S.state -> T.state -> Prop :=
  | match_states_add_branch:
      forall s f sp pc ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (TAIL: is_tail c (T.fn_code tf)),
      match_states (S.State s f sp pc ls m)
                   (T.State ts tf sp (add_branch pc c) ls m)
  | match_states_cond_taken:
      forall s f sp pc ls m tf ts cond args c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (JUMP: eval_condition cond (S.reglist ls args) m = Some true),
      match_states (S.State s f sp pc (S.undef_regs (destroyed_by_cond cond) ls) m)
                   (T.State ts tf sp (T.Lcond cond args pc :: c) ls m)
  | match_states_block:
      forall s f sp bb ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: forall pc, In pc (S.successors_block bb) -> (reachable f)!!pc = true)
        (TAIL: is_tail c (T.fn_code tf)),
      match_states (S.Block s f sp bb ls m)
                   (T.State ts tf sp (linearize_block bb c) ls m)
  | match_states_call:
      forall s f ls m tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (S.Callstate s f ls m)
                   (T.Callstate ts tf ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (S.Returnstate s ls m)
                   (T.Returnstate ts ls m).

(*Theorem MS_add_branch_inv : forall s f sp pc ls m s2,
  match_states (S.State s f sp pc ls m) s2 -> 
  exists ts tf c, 
  list_forall2 match_stackframes s ts /\
  transf_function f = OK tf /\
  (reachable f)!!pc = true /\
  is_tail c (T.fn_code tf) /\
  s2 = (T.State ts tf sp (add_branch pc c) ls m).
Proof.
intros until s2. intros H. inv H. 
do 3 econstructor. eauto.
do 3 econstructor. eauto.
split. apply STACKS. 
split. apply TRF.
split. apply REACH.
split. apply *)
 
Closing Fact MS_add_branch_inv : forall s f sp pc ls m s2,
  match_states (S.State s f sp pc ls m) s2 -> 
  exists ts tf c, 
  list_forall2 match_stackframes s ts /\
  transf_function f = OK tf /\
  (reachable f)!!pc = true /\
  is_tail c (T.fn_code tf) /\
  s2 = (T.State ts tf sp (add_branch pc c) ls m)
by plain { intros until s2; intros H; inv H; eauto }.

Closing Fact MS_block_inv : forall s f sp bb ls m s2, 
    match_states (S.Block s f sp bb ls m) s2 -> 
    exists ts tf c, 
    list_forall2 match_stackframes s ts /\
    transf_function f = OK tf /\
    (forall pc, In pc (S.successors_block bb) -> (reachable f)!!pc = true) /\
    is_tail c (T.fn_code tf) /\
    s2 = (T.State ts tf sp (linearize_block bb c) ls m)
by plain { intros until s2; intros H; inv H; eauto }.

Closing Fact MS_return_inv : forall s ls m s2,
  match_states (S.Returnstate s ls m) s2 ->             
  exists ts, 
  list_forall2 match_stackframes s ts /\
  s2 = (T.Returnstate ts ls m)
by plain { intros until s2; intros H; inv H; eauto }.          

Closing Fact MS_call_inv : forall s f ls m s2, 
  match_states (S.Callstate s f ls m) s2 -> 
  exists ts tf, 
  list_forall2 match_stackframes s ts /\
  transf_fundef f = OK tf /\
  s2 = (T.Callstate ts tf ls m)
by plain { intros until s2; intros H; inv H; eauto }.

FDefinition measure := fun (S0: S.state) =>
  match S0 with
  | self__Linearize.S.State s f sp pc ls m => 0%nat
  | self__Linearize.S.Block s f sp bb ls m => 1%nat
  | _ => 0%nat
  end.

(* Correctness of reachability analysis *)

FLemma reachable_successors:
  forall f pc pc' b,
  (S.fn_code f)!pc = Some b -> In pc' (S.successors_block b) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
FProofLemma.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution; eauto. intros; apply DS.L.eq_refl.
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed. CloseFLemma.

(* Properties of node enumeration *)

Module NodesetFacts := FSetFacts.Facts(Nodeset).

FLemma nodeset_of_list_correct:
  forall l s s',
  nodeset_of_list l s = OK s' ->
  list_norepet l
  /\ (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ In pc l)
  /\ (forall pc, In pc l -> ~Nodeset.In pc s).
FProofLemma.
  induction l; simpl; intros.
  inv H. split. constructor. split. intro; tauto. intros; tauto.
  generalize H; clear H; caseEq (Nodeset.mem a s); intros.
  inv H0.
  exploit IHl; eauto. intros [A [B C]].
  split. constructor; auto. red; intro. elim (C a H1). apply Nodeset.add_1. hnf. auto.
  split. intros. rewrite B. rewrite NodesetFacts.add_iff.
  unfold Nodeset.E.eq. unfold OrderedPositive.eq. tauto.
  intros. destruct H1. subst pc. rewrite NodesetFacts.not_mem_iff. auto.
  generalize (C pc H1). rewrite NodesetFacts.add_iff. tauto.
Qed. CloseFLemma.

FLemma check_reachable_correct:
  forall f reach s pc i,
  check_reachable f reach s = true ->
  (S.fn_code f)!pc = Some i ->
  reach!!pc = true ->
  Nodeset.In pc s.
FProofLemma.
  intros f reach s.
  assert (forall l ok,
    List.fold_left (fun a p => check_reachable_aux reach s a (fst p) (snd p)) l ok = true ->
    ok = true /\
    (forall pc i,
     In (pc, i) l ->
     reach!!pc = true ->
     Nodeset.In pc s)).
  induction l; simpl; intros.
  split. auto. intros. destruct H0.
  destruct a as [pc1 i1]. simpl in H.
  exploit IHl; eauto. intros [A B].
  unfold check_reachable_aux in A.
  split. destruct (reach!!pc1). elim (andb_prop _ _ A). auto. auto.
  intros. destruct H0. inv H0. rewrite H1 in A. destruct (andb_prop _ _ A).
  apply Nodeset.mem_2; auto.
  eauto.

  intros pc i. unfold check_reachable. rewrite PTree.fold_spec. intros.
  exploit H; eauto. intros [A B]. eapply B; eauto.
  apply PTree.elements_correct. eauto.
Qed. CloseFLemma.

FLemma enumerate_complete:
  forall f enum pc i,
  enumerate f = OK enum ->
  (S.fn_code f)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc enum.
FProofLemma.
  intros until i. unfold enumerate.
  set (reach := reachable f).
  intros. monadInv H.
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit check_reachable_correct; eauto. intro.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]].
  rewrite B in H2. destruct H2. elim (Nodeset.empty_1 H2). auto.
Qed. CloseFLemma.

FLemma find_label_add_branch:
  forall lbl k s,
  T.find_label lbl (add_branch s k) = T.find_label lbl k.
FProofLemma.
  intros. unfold add_branch. destruct (starts_with s k).
  - auto.
  - simpl. fsimpl. reflexivity.
Qed. CloseFLemma.

Create HintDb fsimpl.
Hint Extern 1 => fsimpl : fsimpl.
Hint Extern 1 => simpl : fsimpl.

FInduction find_label_lin_block_helper about S.instruction motive (fun (a : S.instruction) => 
  forall lbl b k (IH: T.find_label lbl (linearize_block b k) = T.find_label lbl k), 
    T.find_label lbl (translate_instr a (linearize_block b) k) = T.find_label lbl k).
FProof.
all: intros; generalize (find_label_add_branch lbl k); intro; info_auto with fsimpl. 
+ fsimpl. case (starts_with n k); auto with fsimpl. 
Qed. FEnd find_label_lin_block_helper.

FLemma find_label_lin_block:
  forall lbl k b,
  T.find_label lbl (linearize_block b k) = T.find_label lbl k.
FProofLemma.
  intros lbl k. generalize (find_label_add_branch lbl k); intro.
  induction b; simpl; auto. 
  (*fdestruct a: *) eapply find_label_lin_block_helper; eauto.  
Qed. CloseFLemma.

FLemma linearize_body_cons:
  forall f pc enum,
  linearize_body f (pc :: enum) =
  match (S.fn_code f)!pc with
  | None => linearize_body f enum
  | Some b => T.Llabel pc :: linearize_block b (linearize_body f enum)
  end.
FProofLemma.
  intros. unfold linearize_body. rewrite list_fold_right_eq.
  unfold linearize_node. destruct (S.fn_code f)!pc; auto.
Qed. CloseFLemma.

FLemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  (S.fn_code f)!pc = Some b ->
  exists k, T.find_label pc (linearize_body f enum) = Some (linearize_block b k).
FProofLemma.
  induction enum; intros.
  elim H.
  rewrite linearize_body_cons.
  destruct (peq a pc).
  subst a. exists (linearize_body f enum).
  rewrite H0. simpl. fsimpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  destruct (IHenum pc b H1 H0) as [k FIND].
  exists k. destruct (S.fn_code f)!a.
  simpl. fsimpl. rewrite peq_false. rewrite find_label_lin_block. auto. auto.
  auto.
Qed. CloseFLemma.

FLemma find_label_lin:
  forall f tf pc b,
  transf_function f = OK tf ->
  (S.fn_code f)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  T.find_label pc (T.fn_code tf) = Some (linearize_block b k).
FProofLemma.
  intros. monadInv H. simpl.
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed. CloseFLemma.

FLemma is_tail_find_label:
  forall lbl c2 c1,
  T.find_label lbl c1 = Some c2 -> is_tail c2 c1.
FProofLemma.
  induction c1; simpl.
  intros; discriminate.
  case (T.is_label a lbl). intro. injection H; intro. subst c2.
  constructor. constructor.
  intro. constructor. auto.
Qed. CloseFLemma.

FLemma is_tail_add_branch:
  forall lbl c1 c2, is_tail (add_branch lbl c1) c2 -> is_tail c1 c2.
FProofLemma.
  intros until c2. unfold add_branch. destruct (starts_with lbl c1).
  auto. eauto with coqlib.
Qed. CloseFLemma.

FInduction is_tail_lin_block_help about S.instruction motive
  (fun (a : S.instruction) =>
     forall b c1 c2 (H : is_tail (translate_instr a (linearize_block b) c1) c2),
       (forall (c1 : T.code) (c2 : list T.instruction), is_tail (linearize_block b c1) c2 -> is_tail c1 c2) ->
       is_tail c1 c2).
FProof.
all: intros; fsimpl in H; eauto with coqlib.
+ eapply is_tail_add_branch; eauto.
+ destruct (starts_with n c1); eapply is_tail_add_branch; eauto with coqlib.
Qed. FEnd is_tail_lin_block_help.

FRecursion unique_labels_helper about T.instruction motive
   (fun (_ : T.instruction) => T.code -> Prop -> Prop) by _rect. 
Case Llabel lbl := (fun c rest => ~(In (T.Llabel lbl) c) /\ rest).
Case _ := (fun c rest => rest).
FEnd unique_labels_helper.

MetaData unique_labels.
Fixpoint unique_labels (c: T.code) : Prop :=
  match c with
  | nil => True
  | i :: c => unique_labels_helper i c (unique_labels c)  
  end.
FEnd unique_labels.

FInduction find_label_unique_helper about T.instruction 
  motive (fun (a : T.instruction) => forall c2 (UNIQ : unique_labels (a :: c2)), unique_labels c2).
FProof.
all: intros; unfold unique_labels in UNIQ; fsimpl in UNIQ; fold unique_labels in UNIQ; tauto.
Qed. FEnd find_label_unique_helper.

FLemma find_label_unique:
  forall lbl c1 c2 c3,
  is_tail (T.Llabel lbl :: c1) c2 ->
  unique_labels c2 ->
  T.find_label lbl c2 = Some c3 ->
  c1 = c3.
FProofLemma.
  induction c2.
  simpl; intros; discriminate.
  intros c3 TAIL UNIQ. simpl.
  generalize (T.is_label_correct a lbl). case (T.is_label a lbl); intro ISLBL.
  subst a. intro. inversion TAIL. congruence. subst.  unfold unique_labels in UNIQ. fsimpl in UNIQ. fold unique_labels in UNIQ.
  elim UNIQ; intros. elim H0. apply is_tail_in with c1; auto.
  inversion TAIL. congruence. apply IHc2. auto.
  eapply find_label_unique_helper; eauto.
Qed. CloseFLemma.
                
FLemma is_tail_lin_block:
  forall b c1 c2,
  is_tail (linearize_block b c1) c2 -> is_tail c1 c2.
FProofLemma.
  induction b; simpl; intros.
  auto. eapply is_tail_lin_block_help; eauto.
Qed. CloseFLemma.

FLemma unique_labels_add_branch:
  forall lbl k,
  unique_labels k -> unique_labels (add_branch lbl k).
FProofLemma.
  intros; unfold add_branch.
  destruct (starts_with lbl k); simpl; intuition.
Qed. CloseFLemma.

(* proved in CompCert, but doesn't require rocqet features *)
MetaData unique_labels_lin_rec.
Axiom unique_labels_lin_rec:
  forall f enum,
  list_norepet enum ->
  unique_labels (linearize_body f enum).
FEnd unique_labels_lin_rec.

FLemma enumerate_norepet:
  forall f enum,
  enumerate f = OK enum ->
  list_norepet enum.
FProofLemma.
  intros until enum. unfold enumerate.
  set (reach := reachable f).
  intros. monadInv H.
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]]. auto.
Qed. CloseFLemma.

FLemma unique_labels_transf_function:
  forall f tf,
  transf_function f = OK tf ->
  unique_labels (T.fn_code tf).
FProofLemma.
  intros. monadInv H. simpl.
  apply unique_labels_add_branch.
  apply unique_labels_lin_rec. eapply enumerate_norepet; eauto.
Qed. CloseFLemma.

(* Starts with is correct, requires nested induction *)
MetaData starts_with_correct.
Axiom starts_with_correct:
  forall tge lbl c1 c2 c3 s f sp ls m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  T.find_label lbl c2 = Some c3 ->
  plus T.step tge (T.State s f sp c1 ls m)
             E0 (T.State s f sp c3 ls m).
FEnd starts_with_correct.

FLemma add_branch_correct:
  forall tge lbl c k s f tf sp ls m,
  transf_function f = OK tf ->
  is_tail k (T.fn_code tf) ->
  T.find_label lbl (T.fn_code tf) = Some c ->
  plus T.step tge (T.State s tf sp (add_branch lbl k) ls m)
             E0 (T.State s tf sp c ls m).
FProofLemma.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.    
  eapply starts_with_correct; eauto.
  eapply unique_labels_transf_function; eauto.
  apply plus_one. apply T.exec_Lgoto. auto.
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

FLemma stacksize_preserved:
  forall f tf,
  transf_function f = OK tf ->
  T.fn_stacksize tf = S.fn_stacksize f.
FProofLemma.
  intros. monadInv H. auto.
Qed. CloseFLemma.

FLemma match_parent_locset:
  forall s ts, list_forall2 match_stackframes s ts -> T.parent_locset ts = S.parent_locset s.
FProofLemma.
  induction 1; simpl. auto. inv H; auto.
Qed. CloseFLemma.

FLemma reachable_entrypoint:
  forall f, (reachable f)!!((S.fn_entrypoint f)) = true.
FProofLemma.
  intros. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux; intros reach A.
  assert (LBoolean.ge reach!!((S.fn_entrypoint f)) true).
  eapply DS.fixpoint_entry. eexact A. auto.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed. CloseFLemma.

FInduction transf_step_correct about S.step
  motive (fun ge s1 t s2 (_ : S.step ge s1 t s2) =>    
    forall prog tprog tge (TRANSF: match_prog prog tprog) s1' (MS: match_states s1 s1'),
    ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
    (exists s2', plus T.step tge s1' t s2' /\ match_states s2 s2')
    \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat).
FProof.
(* start of block, at an [add_branch] *)
+ intros. apply MS_add_branch_inv in MS; unpack MS; subst.
  exploit find_label_lin; eauto. intros [k F].
  left; econstructor; split.
  eapply add_branch_correct; eauto.
  fconstructor; eauto.
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.
  
 (* Lop *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  left; econstructor; split. simpl. fsimpl.
  apply plus_one. fconstructor; eauto.
  instantiate (1 := v); rewrite <- e; apply eval_operation_preserved.
  exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  simpl in TEMP1. fsimpl in TEMP1.
  fconstructor; eauto. 

(* Lgetstack *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst.
  left; econstructor; split. simpl. fsimpl.
  apply plus_one. fconstructor; eauto.
  simpl in TEMP1. fsimpl in TEMP1.
  fconstructor; eauto.

(* Lsetstack *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  left; econstructor; split. simpl. fsimpl.
  apply plus_one. fconstructor; eauto.
  simpl in TEMP1. fsimpl in TEMP1.
  fconstructor; eauto.

(* Lbranch *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst.
 simpl in TEMP1. fsimpl in TEMP1.
 assert ((reachable f)!!pc = true). apply TEMP1; simpl; auto.
 right; split. simpl; lia. split. auto. simpl. fsimpl. fconstructor; eauto.

(* Lcond *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst.
 simpl in TEMP1. fsimpl in TEMP1.
 assert (REACH1: (reachable f)!!pc1 = true) by (apply TEMP1; simpl; auto).
 assert (REACH2: (reachable f)!!pc2 = true) by (apply TEMP1; simpl; auto).
 simpl linearize_block. fsimpl.
destruct (starts_with pc1 c).
  (* TODO: I think we can prove this by hand *)
  assert (S.reglist = T.reglist) by (unfold S.reglist; unfold T.reglist; reflexivity).
  (* branch if cond is false *)
  assert (DC: destroyed_by_cond (negate_condition cond) = destroyed_by_cond cond).
    destruct cond; reflexivity.
  destruct b.
  (* cond is true: no branch *)
  left; econstructor; split.
  apply plus_one. eapply T.exec_Lcond_false.
  rewrite eval_negate_condition. 
  (* TODO *)
  rewrite <- H.
  rewrite e. auto. eauto.
  rewrite DC. fconstructor; eauto.
  (* cond is false: branch is taken *)
  right; split. simpl; lia. split. auto. rewrite <- DC. fconstructor; eauto.
  rewrite eval_negate_condition. rewrite e. auto.
  (* branch if cond is true *)
  destruct b.
  (* cond is true: branch is taken *)
  right; split. simpl; lia. split. auto. fconstructor; eauto.
  (* cond is false: no branch *)
  left; econstructor; split.
  apply plus_one. eapply T.exec_Lcond_false. eauto. eauto.
  fconstructor; eauto.

(* Lreturn *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst.
  simpl in TEMP1. fsimpl in TEMP1.
  left; econstructor; split.

  simpl. apply plus_one. simpl. fsimpl. fconstructor; eauto.
  rewrite (stacksize_preserved _ _ TEMP). eauto.
  rewrite (match_parent_locset _ _ TEMP0). fconstructor; eauto.

(* return *)  
+ intros. apply MS_return_inv in MS; unpack MS; subst.
  inv TEMP0. inv H1.
  left; econstructor; split.
  apply plus_one. fconstructor.
  fconstructor; eauto.

(* internal functions *)  
+ intros. apply MS_call_inv in MS; unpack MS; subst. 
assert (REACH: (reachable f)!!(S.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  monadInv TEMP0.
  left; econstructor; split.
  apply plus_one. eapply T.exec_function_internal; eauto.
  rewrite (stacksize_preserved _ _ EQ). eauto.
  generalize EQ; intro EQ'; monadInv EQ'. simpl.
  fconstructor; eauto. simpl. eapply is_tail_add_branch. constructor.
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Base.

Trait Comp_Loops extends Base.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Family Linearize.

FRecursion starts_with_label.
Case Ljumptable a b  := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Ljumptable args tbl := (fun f k => T.Ljumptable args tbl :: k).
FEnd translate_instr.

FInductive match_states: S.state -> T.state -> Prop :=
| match_states_jumptable:
      forall s f sp pc ls m tf ts arg tbl c n
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (ARG: ls (R arg) = Vint n)
        (JUMP: list_nth_z tbl (Int.unsigned n) = Some pc),
      match_states (S.State s f sp pc (S.undef_regs destroyed_by_jumptable ls) m)
                   (T.State ts tf sp (T.Ljumptable arg tbl :: c) ls m).

FInduction find_label_lin_block_helper.
FProof.
all: intros; generalize (find_label_add_branch lbl k); intro; info_auto with fsimpl. 
Qed. FEnd find_label_lin_block_helper.

FInduction is_tail_lin_block_help.
FProof.
all: intros; fsimpl in H; eauto with coqlib.
Qed. FEnd is_tail_lin_block_help.

FRecursion unique_labels_helper.
Case _ := (fun c rest => rest).
FEnd unique_labels_helper.

FInduction find_label_unique_helper.
FProof.
all: intros; unfold unique_labels in UNIQ; fsimpl in UNIQ; fold unique_labels in UNIQ; tauto.
Qed. FEnd find_label_unique_helper.

FInduction transf_step_correct.
FProof.
(* Ljumptable *)
+ intros. apply MS_block_inv in MS; unpack MS; subst.
  simpl in TEMP1. fsimpl in TEMP1.  
  assert (REACH': (reachable f)!!pc = true).  
    apply TEMP1. simpl. eapply list_nth_z_in; eauto.
    right; split. simpl; lia. split. auto. simpl. fsimpl. fconstructor; eauto.
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family Linearize.

FRecursion starts_with_label.
Case _ := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lbuiltin ef args res := (fun f k => T.Lbuiltin ef args res ::f k).
FEnd translate_instr.

FInduction find_label_lin_block_helper.
FProof.
all: intros; generalize (find_label_add_branch lbl k); intro; info_auto with fsimpl. 
Qed. FEnd find_label_lin_block_helper.

FInduction is_tail_lin_block_help.
FProof.
all: intros; fsimpl in H; eauto with coqlib.
Qed. FEnd is_tail_lin_block_help.

FRecursion unique_labels_helper.
Case _ := (fun c rest => rest).
FEnd unique_labels_helper.

FInduction find_label_unique_helper.
FProof.
all: intros; unfold unique_labels in UNIQ; fsimpl in UNIQ; fold unique_labels in UNIQ; tauto.
Qed. FEnd find_label_unique_helper.

FLemma senv_preserved: forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.senv_transf_partial TRANSL).
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
(* Lbuiltin *)
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  simpl in TEMP1. fsimpl in TEMP1.
  left; econstructor; split. simpl.
  apply plus_one. fsimpl. eapply T.exec_Lbuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := (Genv.globalenv prog)); eauto. 
  exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).  
  eapply external_call_symbols_preserved; eauto. 
  apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).
  fconstructor.
(* external function *)
+ intros. apply MS_call_inv in MS; unpack MS; subst.
  monadInv TEMP0. left; econstructor; split.
  apply plus_one. eapply T.exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. 
  apply (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl).  
  fconstructor.  
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

FRecursion starts_with_label.
Case Lstore a b c d := (fun lbl => false).
Case Lload a b c d := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lstore chunk addr args src := (fun f k => T.Lstore chunk addr args src :: f k).
Case Lload chunk addr args dst := (fun f k => T.Lload chunk addr args dst :: f k).
FEnd translate_instr.

FInduction find_label_lin_block_helper.
FProof.
all: intros; generalize (find_label_add_branch lbl k); intro; info_auto with fsimpl. 
Qed. FEnd find_label_lin_block_helper.

FInduction is_tail_lin_block_help.
FProof.
all: intros; fsimpl in H; eauto with coqlib.
Qed. FEnd is_tail_lin_block_help.

FRecursion unique_labels_helper.
Case _ := (fun c rest => rest).
FEnd unique_labels_helper.

FInduction find_label_unique_helper.
FProof.
all: intros; unfold unique_labels in UNIQ; fsimpl in UNIQ; fold unique_labels in UNIQ; tauto.
Qed. FEnd find_label_unique_helper.

FInduction transf_step_correct.
FProof.
(* Lload *)
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  simpl in TEMP1. fsimpl in TEMP1.
  left; econstructor; split. simpl.
  apply plus_one. fsimpl. fconstructor.
  (*instantiate (1 := a). *) rewrite <- e; apply eval_addressing_preserved.
  exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl). 
  fconstructor.
(* Lstore *)  
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  simpl in TEMP1. fsimpl in TEMP1. 
  left; econstructor; split. simpl.
  apply plus_one. fsimpl. fconstructor.
  (*instantiate (1 := a).*) rewrite <- e; apply eval_addressing_preserved.
  exact (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl). 
  fconstructor.  
Qed. FEnd transf_step_correct.

FEnd Linearize.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Linearize.
FEnd Linearize.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Linearize.
Family S extends LTL. FEnd S.
Family T extends Linear. FEnd T.

FRecursion starts_with_label.
Case Lcall a b := (fun lbl => false).
Case Ltailcall a b := (fun lbl => false).
FEnd starts_with_label.

FRecursion translate_instr.
Case Lcall sig ros := 
  (fun f k => T.Lcall sig ros :: f k).
Case Ltailcall sig ros := 
 (fun f k => T.Ltailcall sig ros :: k).
FEnd translate_instr.

FInduction find_label_lin_block_helper.
FProof.
all: intros; generalize (find_label_add_branch lbl k); intro; info_auto with fsimpl. 
Qed. FEnd find_label_lin_block_helper.

FInduction is_tail_lin_block_help.
FProof.
all: intros; fsimpl in H; eauto with coqlib.
Qed. FEnd is_tail_lin_block_help.

FRecursion unique_labels_helper.
Case _ := (fun c rest => rest).
FEnd unique_labels_helper.

FInduction find_label_unique_helper.
FProof.
all: intros; unfold unique_labels in UNIQ; fsimpl in UNIQ; fold unique_labels in UNIQ; tauto.
Qed. FEnd find_label_unique_helper.

FLemma functions_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (v: val) (f: S.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = Errors.OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply (Genv.find_funct_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma function_ptr_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall (b: block) (f: S.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. rewrite A. rewrite B.
apply Genv.find_funct_ptr_transf_partial; eauto.
Qed. CloseFLemma.

Inherit symbols_preserved.

FLemma find_function_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  ge = Genv.globalenv prog ->
  tge = Genv.globalenv tprog ->
  forall ros ls f,
  S.find_function ge ros ls = Some f ->
  exists tf,
  T.find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
FProofLemma.
  unfold S.find_function; intros; destruct ros; simpl.
  eapply functions_translated; eauto.
  rewrite (symbols_preserved prog tprog ge tge H H0 H1).  
  destruct (Genv.find_symbol ge i).
  apply (function_ptr_translated prog tprog ge tge H H0 H1); auto.   
  congruence.
Qed. CloseFLemma.

FLemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  T.funsig tf = S.funsig f.
FProofLemma.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. monadInv EQ. apply cheat. (* reflexivity.*)
  inv H. reflexivity.
Qed. CloseFLemma.

FInduction transf_step_correct.
FProof.
(* Lcall *)
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  simpl in TEMP1. fsimpl in TEMP1. 
  exploit find_function_translated; eauto. intros [tfd [A B]].
  left; econstructor; split. simpl. fsimpl.
  apply plus_one. fconstructor; eauto.
  symmetry; eapply sig_preserved; eauto.
  fconstructor; eauto. constructor; auto. econstructor; eauto.
(* Ltailcall *)
+ intros. apply MS_block_inv in MS; unpack MS; subst. 
  simpl in TEMP1. fsimpl in TEMP1. 
  exploit find_function_translated; eauto. intros [tfd [A B]].
  left; econstructor; split. simpl. fsimpl.
  apply plus_one. fconstructor; eauto.
  rewrite (match_parent_locset _ _ TEMP0). eauto.
  symmetry; eapply sig_preserved; eauto.
  rewrite (stacksize_preserved _ _ TEMP); eauto.
  rewrite (match_parent_locset _ _ TEMP0).
  fconstructor; eauto.
Qed. FEnd transf_step_correct.
  
FEnd Linearize.

FEnd Comp_Call.

Trait Comp_Switch extends Comp_Loops. FEnd Comp_Switch.

Family Comp extends
  Base,
  Comp_Builtin,
  Comp_Loops,
  Comp_Field,
  Comp_Heap,
  Comp_Switch,
  Comp_Call. 

Family Linearize.
Final Family S := LTL.
Final Family T := Linear.
FEnd Linearize.

FEnd Comp.


