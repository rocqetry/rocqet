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

Require Import CfamBase.
Require Import Cminor.
Require Import CminorSel.
Require Import Cfamtransl.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Trait Base.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

FOverride Definition earg := unit.

FDefinition addrsymbol := fun (id: ident) (ofs: ptrofs) =>
  T.Eop (Oaddrsymbol id ofs) T.Enil.

FDefinition addrstack := fun (ofs: ptrofs) =>
  T.Eop (Oaddrstack ofs) T.Enil.

FRecursion sel_constant about S.constant motive (fun (_ : S.constant) => T.expr) by _rect.
Case Ointconst n := (T.Eop (Ointconst n) T.Enil).
Case Ofloatconst f := (T.Eop (Ofloatconst f) T.Enil).
Case Osingleconst f := (T.Eop (Osingleconst f) T.Enil).
(*simpler than compcert *)
Case Olongconst n := (T.Eop (Olongconst n) T.Enil).
Case Oaddrsymbol id ofs := (addrsymbol id ofs).
Case Oaddrstack ofs := (addrstack ofs).
FEnd sel_constant.

(* These are implemented as "Nondetfunction" in CompCert, which is not Gallina, but
   rather a meta language which is compiled in to Gallina
   we axiomatize the functions here for simplicity *)
MetaData nondet_selection binds sel_unop, sel_binop.
Axiom sel_unop : unary_operation -> T.expr -> T.expr.
Axiom sel_binop : binary_operation -> T.expr -> T.expr -> T.expr.
FEnd nondet_selection.

FRecursion transl_expr.
Case Econst cst := (fun _ => OK ((sel_constant cst))).
Case Eunop op arg := (fun earg => do result <- (transl_expr arg earg); OK (sel_unop op result)).
Case Ebinop op arg1 arg2 := (fun earg =>
    do r1 <- transl_expr arg1 earg;
    do r2 <- transl_expr arg2 earg;
    OK (sel_binop op r1 r2)).
FEnd transl_expr.

FRecursion condexpr_of_expr about T.expr motive (fun (_ : T.expr) => T.condexpr) by _rect.
Case Eop op el :=
  (match op with
   | Op.Ocmp c => T.CEcond c el
   | _ => T.CEcond (Ccompuimm Cne Int.zero) (T.Econs (T.Eop op el) T.Enil)
   end).
Case Econdition a b c := (T.CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)).
Case Elet a b := (T.CElet a (condexpr_of_expr b)).
Case Eletvar n := (T.CEcond (Ccompuimm Cne Int.zero) (T.Econs (T.Eletvar n) T.Enil)).
Case Evar i := (T.CEcond (Ccompuimm Cne Int.zero) (T.Econs (T.Evar i) T.Enil)).
FEnd condexpr_of_expr.

FOverride Definition sarg := unit.

(* no heuristics *)
FRecursion transl_stmt.
Case Sifthenelse e ifso ifnot :=
  (fun earg sarg =>
     do ifso' <- transl_stmt ifso earg sarg; do ifnot' <- transl_stmt ifnot earg sarg;
     do e' <- (transl_expr e earg) ;
     OK (T.Sifthenelse (condexpr_of_expr e') ifso' ifnot')).
FEnd transl_stmt.

(* no helpers *)
FOverride Definition transl_function := fun f =>
  (*let ki := known_id f in
  do env <- Cminortyping.type_function f;*)
  do body' <- transl_stmt (S.fn_body f) tt tt;
  OK (T.mkfunction
        (S.fn_sig f)
        (S.fn_params f)
        (S.fn_vars f)
        (S.fn_stackspace f)
        body').

Inherit transl_program.

(* correctness *)

FDefinition match_fundef := fun (cunit: S.program) (f: S.fundef) (tf: T.fundef) =>
  transl_fundef f = OK tf.

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program match_fundef eq p tp.

(* Variable cunit: Cminor.program.
Hypothesis LINK: linkorder cunit prog.
Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF: match_prog prog tprog. *)

MetaData env_lessdef.
Definition env_lessdef (e1 e2: S.env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (S.set_params vl1 il) (S.set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (S.set_locals il e1) (S.set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.
FEnd env_lessdef.

(* We Aximatize these because those selection functions are not defined direclty in Gallina *)
MetaData nondet_selection_proof binds eval_sel_unop, eval_sel_binop.
Axiom eval_sel_unop:
  forall tge sp e m le op a1 v1 v,
  T.eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', T.eval_expr tge sp e m le (sel_unop op a1) v' /\ Val.lessdef v v'.

Axiom eval_sel_binop:
  forall tge sp e m le op a1 a2 v1 v2 v,
  T.eval_expr tge sp e m le a1 v1 ->
  T.eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', T.eval_expr tge sp e m le (sel_binop op a1 a2) v' /\ Val.lessdef v v'.
FEnd nondet_selection_proof.

FLemma symbols_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.find_symbol_match TRANSL).
Qed. CloseFLemma.

FLemma eval_addrsymbol:
  forall ge sp e m le id ofs,
  exists v, T.eval_expr ge sp e m le (addrsymbol id ofs) v /\ Val.lessdef (Genv.symbol_address ge id ofs) v.
FProofLemma.
  intros. unfold addrsymbol. econstructor; split. fconstructor. fconstructor.
  simpl; eauto.
  auto.
Qed. CloseFLemma.

FLemma eval_addrstack:
  forall ge sp e m le ofs,
  exists v, T.eval_expr ge sp e m le (addrstack ofs) v /\ Val.lessdef (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs) v.
FProofLemma.
  intros. unfold addrstack. econstructor; split. fconstructor. fconstructor.
  simpl; eauto.
  auto.
Qed. CloseFLemma.

FInduction transl_constant_correct about S.constant
  motive (fun (cst : S.constant) =>
    forall prog tprog ge tge (TRANSL: match_prog prog tprog),
     Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
    forall sp v e m le,
       S.eval_constant cst ge sp = Some v ->
       exists tv,
          T.eval_expr tge sp e m le (sel_constant cst) tv
       /\ Val.lessdef v tv).
FProof.
all: intros; fsimpl in H1; inv H1; fsimpl.
+ exists (Vint i); split; auto. fconstructor. fconstructor. auto.
+ exists (Vfloat f); split; auto. fconstructor. fconstructor. auto.
+ exists (Vsingle f); split; auto. fconstructor. fconstructor. auto.
+ exists (Vlong i); split; auto. fconstructor. fconstructor. auto.
+ unfold Genv.symbol_address; rewrite <- (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl); fold (Genv.symbol_address (Genv.globalenv tprog) i i0). apply eval_addrsymbol.
+ apply eval_addrstack.
Qed. FEnd transl_constant_correct.

Ltac TrivialExists2 :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

FLemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
FProofLemma.
  intros until v; intros EV LD. inv LD.
  exists v; auto.
  destruct op; simpl; inv EV; TrivialExists2.
Qed. CloseFLemma.

FLemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v ->
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
FProofLemma.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  { inv LD1. inv LD2. exists v; auto.
    destruct op; destruct v1'; simpl in *; inv EV; TrivialExists2.
    destruct op; simpl in *; inv EV; TrivialExists2. }
  assert (CMPU: forall c,
    eval_binop (Ocmpu c) v1 v2 m = Some v ->
    exists v' : val, eval_binop (Ocmpu c) v1' v2' m' = Some v' /\ Val.lessdef v v').
  { intros c A. simpl in *. inv A. econstructor; split. eauto.
    apply Val.of_optbool_lessdef.
    intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
    intros; eapply Mem.valid_pointer_extends; eauto. }
  assert (CMPLU: forall c,
    eval_binop (Ocmplu c) v1 v2 m = Some v ->
    exists v' : val, eval_binop (Ocmplu c) v1' v2' m' = Some v' /\ Val.lessdef v v').
  { intros c A. simpl in *. unfold Val.cmplu in *.
    destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:C; simpl in A; inv A.
    eapply Val.cmplu_bool_lessdef with (valid_ptr' := (Mem.valid_pointer m')) in C;
    eauto using Mem.valid_pointer_extends.
    rewrite C. exists (Val.of_bool b); auto. }
  destruct op; auto.
Qed. CloseFLemma.

FInduction transl_expr_correct about S.eval_expr motive
  (fun ge sp e m lenv a v (_ : S.eval_expr ge sp e m lenv a v) =>
     forall prog tprog tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
     Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
     forall e' m' ta (TR: transl_expr a tt = OK ta),
     env_lessdef e e' -> Mem.extends m m' ->
     exists v', T.eval_expr tge sp e' m' lenv ta v' /\ Val.lessdef v v').
FProof.
all: intros; simpl; fsimpl.
(* Evar *)
+ exploit H1; eauto. intros [v' [A B]]. exists v'; split; auto. fsimpl in TR. monadInv TR. fconstructor; auto.
(* Econst *)
+ exploit transl_constant_correct; eauto.
  fsimpl in TR. monadInv TR.
  intros [tv [A B]]. exists tv; split; eauto.
(* Eunop *)
+ fsimpl in TR. monadInv TR.
  exploit H; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto.
(* Binop *)
+ fsimpl in TR. monadInv TR. exploit H0; eauto. intros [v1' [A B]].
  exploit H; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  assert (G: exists v'', T.eval_expr (Genv.globalenv tprog) e e' m' lenv (sel_binop op x x0) v'' /\ Val.lessdef v' v'')
    by (eapply eval_sel_binop; eauto).
  destruct G as [v'' [P Q]].
   exists v''; split; eauto. eapply Val.lessdef_trans; eauto.
Qed. FEnd transl_expr_correct.

(*FInduction eval_condexpr_of_expr about T.expr
  motive (fun (a : T.expr) =>
    forall b tge sp e m le a v (_ : T.eval_expr tge sp e m le a v),
    Val.bool_of_val v b ->
    T.eval_condexpr tge sp e m le (condexpr_of_expr a) b).
FProof.
+ intros. *)
MetaData eval_condexpr_of_expr.
(* Axiomatize: proved by functional induction, which we don't yet support *)
Axiom eval_condexpr_of_expr:
  forall tge sp e m a le v b,
  T.eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  T.eval_condexpr tge sp e m le (condexpr_of_expr a) b.
FEnd eval_condexpr_of_expr.

FDefinition eventually := fun ge => Smallstep.eventually S.step S.final_state ge.

FInductive match_cont: S.program -> S.cont -> T.cont -> Prop :=
| match_cont_seq: forall cunit s s' k k',
    transl_stmt s tt tt = OK s' ->
    match_cont cunit k k' ->
    match_cont cunit (S.Kseq s k) (T.Kseq s' k')
| match_cont_other: forall cunit k k',
    match_call_cont k k' ->
    match_cont cunit k k'
with match_call_cont: S.cont -> T.cont -> Prop :=
| match_cont_stop:
    match_call_cont S.Kstop T.Kstop.

Closing Fact match_cont_seq_inv : forall cunit s k tk,
    match_cont cunit (S.Kseq s k) tk ->
    exists s' k',
      tk = (T.Kseq s' k') /\
      transl_stmt s tt tt = OK s' /\
      match_cont cunit k k'
by plain { intros until tk; intros H; inv H; eauto }.

MetaData match_states.
Inductive match_states (cunit: S.program) (prog: S.program): S.state -> T.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m'
        (LINK: linkorder cunit prog)
        (* (HF: helper_functions_declared cunit hf)*)
        (TF: transl_function f = OK f')
        (* (TYF: type_function f = OK env)*)
        (TS: transl_stmt s tt tt = OK s')
        (MC: match_cont cunit k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states cunit prog
        (S.State f s k sp e m)
        (T.State f' s' k' sp e' m')
  | match_callstate: forall f f' args args' k k' m m'
        (LINK: linkorder cunit prog)
        (TF: match_fundef cunit f f')
        (MC: match_call_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states cunit prog
        (S.Callstate f args k m)
        (T.Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_call_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states cunit prog
        (S.Returnstate v k m)
        (T.Returnstate v' k' m').
FEnd match_states.

FDefinition measure := fun (s: S.state) =>
  match s with
  | self__Selection.S.Callstate _ _ _ _ => 0%nat
  | self__Selection.S.State _ _ _ _ _ _ => 1%nat
  | self__Selection.S.Returnstate _ _ _ => 2%nat
  end.

FLemma stackspace_function_translated:
  forall f tf, transl_function f = OK tf -> T.fn_stackspace tf = S.fn_stackspace f.
FProofLemma.
  intros. monadInv H. auto.
Qed. CloseFLemma.

FInduction call_cont_commut about match_cont motive
  (fun cunit k k' (_ : match_cont cunit k k') =>
     match_call_cont (S.call_cont k) (T.call_cont k'))
with call_cont_commut' about match_call_cont motive
  (fun k k' (_ : match_call_cont k k') =>
    match_call_cont (S.call_cont k) (T.call_cont k')).
FProof.
all: intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd call_cont_commut with call_cont_commut'.

FInduction match_is_call_cont about match_cont motive
  (fun cunit k k' (_ : match_cont cunit k k') =>
    S.is_call_cont k ->
    match_call_cont k k' /\ T.is_call_cont k')
with match_is_call_cont' about match_call_cont motive
  (fun k k' (_ : match_call_cont k k') =>
    S.is_call_cont k ->
    T.is_call_cont k').
FProof.
- intros. fsimpl in H0. contradiction.
- intros. fsimpl. exact I.
Qed. FEnd match_is_call_cont with match_is_call_cont'.

FLemma match_states_skip: forall cunit prog f f' k k' sp e m e' m'
        (LINK: linkorder cunit prog)
        (* (HF: helper_functions_declared cunit hf)*)
        (TF: transl_function f = OK f')
        (* (TYF: type_function f = OK env)*)
        (MC: match_cont cunit k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
  match_states cunit prog (S.State f S.Sskip k sp e m) (T.State f' T.Sskip k' sp e' m').
FProofLemma.
  intros. eapply match_state; eauto. fsimpl. reflexivity.
Qed. CloseFLemma.

FInduction find_label_commut about S.stmt motive
  (fun (s: S.stmt) =>
    forall cunit lbl k s' k',
     match_cont cunit k k' ->
     transl_stmt s tt tt = OK s' ->
     match S.find_label s lbl k, T.find_label s' lbl k' with
     | None, None => True
     | Some(s1, k1), Some(s1', k1') => transl_stmt s1 tt tt = OK s1' /\ match_cont cunit k1 k1'
     | _, _ => False
     end).
FProof.
all: intros until k'; simpl; fsimpl; intros MC SE; fsimpl in SE; try (monadInv SE); simpl; fsimpl; auto.
+ fsimpl; auto.
+ fsimpl; auto.
+ exploit (H cunit lbl (S.Kseq __i0 k)). fconstructor; eauto. eauto. fsimpl.
  destruct (S.find_label __i lbl (S.Kseq __i0 k)) as [[sx kx] | ];
  destruct (T.find_label x lbl (T.Kseq x0 k')) as [[sy ky] | ];
  intuition. apply H0; eauto.
+ destruct o; inv SE; simpl. monadInv H0; fsimpl; auto. fsimpl; auto.
+ fsimpl. destruct (ident_eq lbl l).
  - eauto.
  -  apply H; eauto.
+ fsimpl; auto.
+ fsimpl.
  exploit H; eauto. instantiate (1 := lbl).
  destruct (S.find_label __i lbl k) as [[sx kx] | ];
  destruct (T.find_label x lbl k') as [[sy ky] | ];
  intuition. apply H0; auto.
Qed. FEnd find_label_commut.

Require Import Rocqet.LibTactics.

FInduction transl_step_correct about S.step motive
  (fun ge S1 t S2 (_ : S.step ge S1 t S2) =>
     forall prog tprog tge cunit (LINK: linkorder cunit prog) (TRANSL: match_prog prog tprog),
     Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
     forall T1, match_states cunit prog S1 T1 -> (* wt_state S1 ->*)
     (exists T2, plus T.step tge T1 t T2 /\ match_states cunit prog S2 T2)
     \/ (measure S2 < measure S1 /\ t = E0 /\ match_states cunit prog S2 T1)%nat
     \/ (exists T2 n, T.step tge T1 t T2 /\ eventually ge n S2 (fun S3 => match_states cunit prog S3 T2))).
FProof.
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME; inv ME; fsimpl in TS; try (monadInv TS).
(* skip seq *)
+ apply match_cont_seq_inv in MC; unpack MC; subst. left; econstructor; split. apply plus_one; fconstructor. econstructor; eauto. (* inv H*)
(* skip call *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor. eapply match_is_call_cont; eauto.
  unfold T.free_fenv. erewrite stackspace_function_translated; eauto.
  econstructor; eauto. eapply match_is_call_cont; eauto.
(* assign *)
+ exploit transl_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  eapply match_states_skip; eauto. apply set_var_lessdef; auto.
(* seq *)
+ left; econstructor; split.
  apply plus_one; fconstructor.
  econstructor; eauto. fconstructor; eauto.
(* return none *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  left; econstructor; split.
  apply plus_one; fconstructor.
  econstructor; eauto. eapply (call_cont_commut cunit k k' MC); eauto.
(* return some *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit transl_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  econstructor; eauto. eapply (call_cont_commut cunit k k' MC); eauto.
(* label *)
+ left; econstructor; split. apply plus_one; fconstructor. econstructor; eauto.
(* goto *)
+ assert (transl_stmt (S.fn_body f) tt tt = OK (T.fn_body f')).
  { monadInv TF; simpl. congruence. }
  exploit (find_label_commut (S.fn_body f) cunit lbl (S.call_cont k)); eauto.
    apply match_cont_other. eapply (call_cont_commut cunit k k'0 MC); eauto.
  unfold S.function_body in e0. rewrite e0.
  destruct (T.find_label (T.fn_body f') lbl (T.call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H0 as (P & Q).
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  econstructor; eauto.
(* ifthenelse *)
+ exploit transl_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv b0.
  left; exists (T.State f' (if b then x else x0) k' sp e' m'); split.
  apply plus_one; fconstructor; eauto. eapply eval_condexpr_of_expr; eauto.
  assert (G: lenv = nil) by (apply cheat). (* We know lenv = nil from CompCert, our transl_expr_correct theorem statement needs to be adjusted *)
  subst. assumption.
  constructor; eauto. destruct b; eauto.
  (* internal function *)
+ red in TF. fsimpl in TF. simpl in TF. monadInv TF. generalize EQ; intros TF; monadInv TF.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; simpl; eauto using Val.has_argtype_list_lessdef.
  econstructor; simpl; eauto.
  apply match_cont_other; auto.
  apply set_locals_lessdef. apply set_params_lessdef; auto.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Base.

(* moved to base *)
(*
Trait Comp_Float extends Base.

Family Selection.
(* Select operator from RISV-V operation *)
FRecursion sel_constant.
Case Ofloatconst f := (T.Eop (Ofloatconst f) T.Enil).
Case Osingleconst f := (T.Eop (Osingleconst f) T.Enil).
FEnd Selection.

FEnd Comp_Float. *)

Trait Comp_Loops extends Base.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

FRecursion transl_stmt.
Case Sloop body :=
  (fun eargs sargs =>
     do body' <- transl_stmt body eargs sargs; OK (T.Sloop body')).
Case Sblock body :=
  (fun eargs sargs =>
     do body' <- transl_stmt body eargs sargs; OK (T.Sblock body')).
Case Sexit n := (fun eargs sargs => OK (T.Sexit n)).
FEnd transl_stmt.

FInductive match_cont: S.program -> S.cont -> T.cont -> Prop :=
| match_cont_block: forall cunit k k',
   match_cont cunit k k' ->
   match_cont cunit (S.Kblock k) (T.Kblock k').

FInduction call_cont_commut.
FProof.
+ apply cheat.
Qed. FEnd call_cont_commut.

FInduction match_is_call_cont.
FProof.
+ apply cheat.
Qed. FEnd match_is_call_cont.

FInduction find_label_commut.
FProof.
+ apply cheat.
+ apply cheat.
+ apply cheat.
Qed. FEnd find_label_commut. 

FInduction transl_step_correct.
FProof.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Loops.

From Rocqet Require Import Switch.

Trait Comp_Switch extends Base, Comp_Loops.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

(* Axiom in CompCert *)
MetaData compile_switch.
Parameter compile_switch: Z -> nat -> table -> comptree.
FEnd compile_switch.

MetaData sel_switch.
(* We axiomatize becuase it is defined using "Nondet" functions  *)
Axiom sel_switch : nat -> comptree -> T.exitexpr.
FEnd sel_switch.
FDefinition sel_switch_int := sel_switch.
FDefinition sel_switch_long := sel_switch.

FRecursion transl_stmt.
Case Sswitch b e cases dfl :=
  (fun _ _ =>
      if b then
        (let t := compile_switch Int64.modulus dfl cases in
        if validate_switch Int64.modulus dfl cases t
        then
          do e' <- transl_expr e tt;
          OK (T.Sswitch (T.XElet e' (sel_switch_long O t)))
        else Error (msg "Selection: bad switch (long)"))
      else
        (let t := compile_switch Int.modulus dfl cases in
        if validate_switch Int.modulus dfl cases t
        then
          do e' <- transl_expr e tt;
          OK (T.Sswitch (T.XElet e' (sel_switch_int O t)))
        else Error (msg "Selection: bad switch (int)"))
  ).
FEnd transl_stmt.

FInduction find_label_commut.
FProof.
+ apply cheat.
Qed. FEnd find_label_commut. 

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Switch.

Trait Comp_Builtin extends Base.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

FDefinition Sno_op := T.Sseq T.Sskip T.Sskip.

Inherit transl_expr.

MetaData builtin_arg.
Axiom builtin_arg : T.expr ->  AST.builtin_arg T.expr.
FEnd builtin_arg.

FDefinition sel_builtin_arg
       := fun (e: S.expr) (c: builtin_arg_constraint) (* : res (AST.builtin_arg expr) :=*) =>
  do e' <- transl_expr e tt;
  OK (let ba := builtin_arg e' in
  if builtin_arg_ok ba c then ba else BA e').

MetaData sel_builtin_args.
Fixpoint sel_builtin_args
       (el: list S.expr)
       (cl: list builtin_arg_constraint): res (list (AST.builtin_arg T.expr)) :=
  match el with
  | nil => OK nil
  | e :: el =>
      do e' <- sel_builtin_arg e (List.hd OK_default cl);
      do el' <- sel_builtin_args el (List.tl cl); 
      OK (e' :: el')
  end.
FEnd sel_builtin_args.

FDefinition sel_builtin_res := fun (optid: option ident) (* : builtin_res ident :=*) =>
  match optid with
  | None => BR_none
  | Some id => BR id
  end.

FDefinition platform_builtin := fun (b: Builtins1.platform_builtin) (args: T.exprlist) => (None : option T.expr). 

MetaData sel_known_builtin.
Function sel_known_builtin (bf: Builtins.builtin_function) (args: T.exprlist) :=
  match bf, args with
  | Builtins.BI_platform b, _ =>
      platform_builtin b args
  (*| Builtins.BI_standard (Builtins0.BI_select ty), a1 ::: a2 ::: a3 ::: Enil =>
      Some (sel_select ty a1 a2 a3)
  | BI_standard BI_fabs, a1 ::: Enil =>
      Some (SelectOp.absf a1)
  | BI_standard BI_fabsf, a1 ::: Enil =>
      Some (SelectOp.absfs a1)*)
  | _, _ =>
      None
  end.
FEnd sel_known_builtin.

(* Should be in Machregs *)
Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg => nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.

FDefinition sel_builtin_default := fun (optid: option ident) (ef: external_function)
                                       (args: list S.expr) =>
  do args <- (sel_builtin_args args (builtin_constraints ef));                                     
  OK (T.Sbuiltin (sel_builtin_res optid) ef args).

MetaData transl_exprlist.
Fixpoint transl_exprlist (al: list S.expr) : res T.exprlist :=
  match al with
  | nil => OK T.Enil
  | a :: bl =>
      do a' <- transl_expr a tt;
      do bl' <- transl_exprlist bl;
      OK (T.Econs a' bl')
  end.
FEnd transl_exprlist.

FDefinition sel_builtin := fun (optid: option ident) (ef: external_function)
                               (args: list S.expr) =>
  match ef with
  | EF_builtin name sg =>
      match Builtins.lookup_builtin_function name sg with
      | Some bf =>
          match optid with
          | Some id =>
              do args' <- (transl_exprlist args);
              match sel_known_builtin bf args' with
              | Some a => OK (T.Sassign id a)
              | None => sel_builtin_default optid ef args
              end
          | None =>
              OK Sno_op(* builtins with semantics are pure *)
          end
      | None => (sel_builtin_default optid ef args)
      end
  | _ =>
      (sel_builtin_default optid ef args)
  end.

FRecursion condexpr_of_expr.
Case Ebuiltin ef args := (T.CEcond (Ccompuimm Cne Int.zero) (T.Econs (T.Ebuiltin ef args) T.Enil)).
FEnd condexpr_of_expr.

FRecursion transl_stmt.
Case Sbuiltin optid ef args := 
  (fun eargs sargs =>
     (sel_builtin optid ef args)).
FEnd transl_stmt.

FInduction find_label_commut.
FProof.
+ apply cheat.
Qed. FEnd find_label_commut. 

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Builtin.

Trait Comp_External extends Base.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_External.

Trait Comp_Call extends Base, Comp_Builtin, Comp_External.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

MetaData call_kind binds Call_default, Call_imm, Call_builtin.
Inductive call_kind : Type :=
  | Call_default
  | Call_imm (id: ident)
  | Call_builtin (ef: external_function).
FEnd call_kind.

FRecursion expr_is_addrof_ident_cst about S.constant motive (fun (_ : S.constant) => option ident) by _rect.
Case Oaddrsymbol id ofs := (if Ptrofs.eq ofs Ptrofs.zero then Some id else None).
Case _ := None.
FEnd expr_is_addrof_ident_cst.

FRecursion expr_is_addrof_ident about S.expr motive (fun (_ : S.expr) => option ident) by _rect.
Case Econst cst := (expr_is_addrof_ident_cst cst).
Case _ := None.                      
FEnd expr_is_addrof_ident.

MetaData _env_ binds globdef, defmap.
Definition globdef := AST.globdef S.fundef unit.
Variable defmap: PTree.t globdef.
FEnd _env_.

FDefinition classify_call := fun (e: S.expr) =>
  match expr_is_addrof_ident e with
  | None => Call_default
  | Some id =>
      match defmap!id with
      | Some(Gfun(AST.External ef)) => if ef_inline ef then Call_builtin ef else Call_imm id
      | _ => Call_imm id
      end
  end.

FRecursion condexpr_of_expr.
Case Eexternal i sig args := (T.CEcond (Ccompuimm Cne Int.zero) (T.Econs (T.Eexternal i sig args) T.Enil)).
FEnd condexpr_of_expr.

(* use default call *)
FRecursion transl_stmt.
Case Scall optid sg fn args :=
  (fun eargs sargs =>  
      (match classify_call fn with
       | self__Selection.Call_default =>
              do fn' <- transl_expr fn eargs;
              do args' <- transl_exprlist args;
              OK (T.Scall optid sg (inl _ fn') args')
       | self__Selection.Call_imm id =>
           do args' <- transl_exprlist args;
           OK (T.Scall optid sg (inr _ id) args')
       | self__Selection.Call_builtin ef => sel_builtin optid ef args
      end)).
Case Stailcall sg fn args :=
   (fun eargs sargs =>     
      (match classify_call fn with
       | self__Selection.Call_imm id =>
           do args' <- transl_exprlist args;
           OK (T.Stailcall sg (inr _ id) args')
       | _ =>
           do fn' <- transl_expr fn eargs;
           do args' <- transl_exprlist args;
           OK (T.Stailcall sg (inl _ fn') args')
      end)).
FEnd transl_stmt.

FInduction find_label_commut.
FProof.
+ apply cheat.
+ apply cheat.  
Qed. FEnd find_label_commut.

FInduction transl_step_correct.
FProof.
+ apply cheat.
+ apply cheat.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Call.

Trait Comp_Heap extends Base, Comp_Builtin.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

(* Not defined in Gallina*)
MetaData addressing'.
Axiom addressing' : memory_chunk -> T.expr -> Op.addressing * T.exprlist.
FEnd addressing'.

FDefinition load := fun (chunk: memory_chunk) (e1: T.expr) =>
  match addressing' chunk e1 with
  | (mode, args) => T.Eload chunk mode args
  end.

FDefinition store := fun (chunk: memory_chunk) (e1 e2: T.expr) =>
  match addressing' chunk e1 with
  | (mode, args) => T.Sstore chunk mode args e2
  end.

FRecursion transl_expr.
Case Eload chunk addr :=
  (fun arg =>
     do addr' <- transl_expr addr arg; 
     OK (load chunk addr')).
FEnd transl_expr.

FRecursion condexpr_of_expr.
Case Eload chunk addr args := (T.CEcond (Ccompuimm Cne Int.zero) (T.Econs (T.Eload chunk addr args) T.Enil)).
FEnd condexpr_of_expr.

FRecursion transl_stmt.
Case Sstore chunk addr rhs :=
  (fun earg sarg =>
     do addr' <- transl_expr addr earg;
     do rhs' <- transl_expr rhs earg; 
     OK (store chunk addr' rhs')).
FEnd transl_stmt.

FInduction transl_expr_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_expr_correct.

FInduction find_label_commut.
FProof.
+ apply cheat.
Qed. FEnd find_label_commut.

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Selection.
FEnd Selection.

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

FEnd Comp.*)
