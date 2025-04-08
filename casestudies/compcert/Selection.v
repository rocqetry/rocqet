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


Closing Fact match_call_cont_stop_inv : forall tk,
    match_call_cont S.Kstop tk ->
    tk = T.Kstop
by plain { intros until tk; intros H; inv H; eauto }.


FInductive match_states : S.program -> S.program -> S.state -> T.state -> Prop :=
  | match_state: forall cunit prog f f' s k s' k' sp e m e' m'
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
  | match_callstate: forall cunit prog f f' args args' k k' m m'
        (LINK: linkorder cunit prog)
        (TF: match_fundef cunit f f')
        (MC: match_call_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states cunit prog
        (S.Callstate f args k m)
        (T.Callstate f' args' k' m')
  | match_returnstate: forall cunit prog v v' k k' m m'
        (MC: match_call_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states cunit prog
        (S.Returnstate v k m)
        (T.Returnstate v' k' m').

Closing Fact MS_state_inv :
  forall cunit prog f s k sp e m TS,
  match_states cunit prog (S.State f s k sp e m) TS ->
  exists f' s' k' e' m',
    TS = T.State f' s' k' sp e' m'
    /\ linkorder cunit prog /\ transl_function f = OK f' /\ transl_stmt s tt tt = OK s'
    /\ match_cont cunit k k' /\ env_lessdef e e' /\ Mem.extends m m'
  by plain { intros * H; inv H; repeat eexists; eauto }.

Closing Fact MS_callstate_internal_inv :
  forall cunit prog f args k m TS,
  match_states cunit prog (S.Callstate (AST.Internal f) args k m) TS ->
  exists f' args' k' m',
    TS = T.Callstate f' args' k' m'
    /\ linkorder cunit prog /\ match_fundef cunit (AST.Internal f) f'
    /\ match_call_cont k k' /\ Val.lessdef_list args args' /\ Mem.extends m m'
  by plain { intros * H; inv H; repeat eexists; eauto }.

Closing Fact MS_returnstate_stop_inv :
  forall cunit prog v m TS,
  match_states cunit prog (S.Returnstate v S.Kstop m) TS ->
  exists v' k' m',
    TS = T.Returnstate v' k' m'
    /\ match_call_cont S.Kstop k' /\ Val.lessdef v v' /\ Mem.extends m m'
  by plain { intros * H; inv H; repeat eexists; eauto }.

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


FLemma function_ptr_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall (b: block) (f: S.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf, Genv.find_funct_ptr tge b = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.find_funct_ptr_match TRANSL).
Qed. CloseFLemma.

FLemma sig_function_translated:
  forall cu f tf, match_fundef cu f tf -> T.funsig tf = S.funsig f.
FProofLemma.
intros. unfold match_fundef in H.
(*destruct H as (hf & P & Q).*) destruct f; monadInv H; auto. monadInv EQ; auto.
Qed. CloseFLemma.

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
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME;
  (apply MS_state_inv in ME as (?f'&?s'&?k'&?e'&?m'&->&_&TF&TS&MC&LD&ME)
  || apply MS_callstate_internal_inv in ME as (?f'&?args'&?k'&?m'&->&_&TF&MC&LD&ME));
  try (fsimpl in TS; monadInv TS).
(* skip seq *)
+ apply match_cont_seq_inv in MC; unpack MC; subst. left; econstructor; split. apply plus_one; fconstructor. fconstructor.
(* skip call *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor. eapply match_is_call_cont; eauto.
  unfold T.free_fenv. erewrite stackspace_function_translated; eauto.
  fconstructor. eapply match_is_call_cont; eauto.
(* assign *)
+ exploit transl_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  eapply match_states_skip; eauto. apply set_var_lessdef; auto.
(* seq *)
+ left; econstructor; split.
  apply plus_one; fconstructor.
  fconstructor. fconstructor; eauto.
(* return none *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  left; econstructor; split.
  apply plus_one; fconstructor.
  fconstructor. eapply (call_cont_commut cunit k k' MC); eauto.
(* return some *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit transl_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  fconstructor. eapply (call_cont_commut cunit k k' MC); eauto.
(* label *)
+ left; econstructor; split. apply plus_one; fconstructor. fconstructor.
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
  fconstructor.
(* ifthenelse *)
+ exploit transl_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv b0.
  left; exists (T.State f' (if b then x else x0) k' sp e' m'); split.
  apply plus_one; fconstructor; eauto. eapply eval_condexpr_of_expr; eauto.
  (* We know lenv = nil from CompCert, our transl_expr_correct theorem statement needs to be adjusted *)
  assert (G: lenv = nil) by (apply cheat).
  subst. assumption.
  fconstructor. destruct b; eauto.
  (* internal function *)
+ red in TF. fsimpl in TF. simpl in TF. monadInv TF. generalize EQ; intros TF; monadInv TF.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; simpl; eauto using Val.has_argtype_list_lessdef.
  fconstructor.
  apply match_cont_other; auto.
  apply set_locals_lessdef. apply set_params_lessdef; auto.
Qed. FEnd transl_step_correct.

FLemma sel_initial_states:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSL: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall S', S.initial_state prog S' ->
  exists R, T.initial_state tprog R /\ match_states cunit prog S' R.
FProofLemma.
destruct 5. subst ge0. rewrite -> H in H3.
  exploit function_ptr_translated; eauto. intros (cu & f' & A & B & C).
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_match TRANSL); eauto.
  rewrite (match_program_main TRANSL). (*fold tge.*) rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl).
  eauto. rewrite <- H0 in A.
  eexact A.
  rewrite <- H4. eapply sig_function_translated; eauto.
  fconstructor. fconstructor. apply Mem.extends_refl.
Qed. CloseFLemma.

FLemma sel_final_states:
  forall cunit prog S' R r,
  match_states cunit prog S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma.
  intros. inv H0. apply MS_returnstate_stop_inv in H as (v'&k'&m'&->&MC&LD&ME).
  apply match_call_cont_stop_inv in MC; subst. (*inv MC.*) inv LD. constructor.
Qed. CloseFLemma.

FEnd Selection.

FEnd Base.

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

Closing Fact match_cont_block_inv :
  forall cunit k k', match_cont cunit (S.Kblock k) k' ->
   exists k'',
     (k' = T.Kblock k'') /\ match_cont cunit k k''
by plain { intros until k'; intros H; inv H; eauto }.

FInduction call_cont_commut with call_cont_commut'.
FProof.
+ intros. do 2 fsimpl; auto; fconstructor.
Qed. FEnd call_cont_commut with call_cont_commut'.

FInduction match_is_call_cont with match_is_call_cont'.
FProof.
+ intros. fsimpl in H0. contradiction.
Qed. FEnd match_is_call_cont with match_is_call_cont'.

FInduction find_label_commut.
FProof.
all: intros until k'; simpl; fsimpl; intros MC SE; fsimpl in SE; try (monadInv SE); simpl; fsimpl; auto.
(* loop *)
+ do 4 fsimpl. eapply H. apply match_cont_seq; auto.
  fsimpl; rewrite EQ; auto. auto.

(* block *)
+ do 4 fsimpl. apply H. eapply match_cont_block; auto.
  rewrite EQ. auto.
(* exit *)
+ fsimpl. exact I.
Qed. FEnd find_label_commut.

FInduction transl_step_correct.
FProof.
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME;
  apply MS_state_inv in ME as (?f'&?s'&?k'&?e'&?m'&->&_&TF&TS&MC&LD&ME); fsimpl in TS; try (monadInv TS).
(* skip block *)
+ apply match_cont_block_inv in MC; unpack MC; subst.
  left; econstructor; split. apply plus_one; apply T.step_skip_block.
  eauto using match_states_skip.

(* Sloop *)
+ left; econstructor; split. apply plus_one; fconstructor. fconstructor.
  apply match_cont_seq; auto. fsimpl; rewrite EQ; auto.

(* Sblock *)
+ left; econstructor; split. apply plus_one; apply T.step_block. fconstructor. eapply match_cont_block; auto.

(* Sexit seq *)
+ apply match_cont_seq_inv in MC; unpack MC; subst. left; econstructor; split. apply plus_one; fconstructor.
  eapply match_state; eauto. fsimpl; reflexivity.

(** Sexit0 block *)
+ apply match_cont_block_inv in MC; unpack MC; subst. left; econstructor; split. apply plus_one; fconstructor. eauto using match_states_skip.

+ (* SexitS block *)
  apply match_cont_block_inv in MC; unpack MC; subst. left; econstructor; split. apply plus_one; fconstructor.
  eapply match_state; eauto. fsimpl; reflexivity.
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
all: intros until k'; simpl; fsimpl; intros MC SE; fsimpl in SE; try (monadInv SE); simpl; fsimpl; auto.
(* switch *)
+ destruct b.
  destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE. monadInv H0.
  fsimpl; auto.
  destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE. monadInv H0.
  fsimpl; auto.
Qed. FEnd find_label_commut.

MetaData sel_switch_int_correct.
Axiom sel_switch_int_correct:
  forall tge dfl cases arg sp e m i t le,
  validate_switch Int.modulus dfl cases t = true ->
  T.eval_expr tge sp e m le arg (Vint i) ->
  T.eval_exitexpr tge sp e m le (T.XElet arg (sel_switch_int O t)) (switch_target (Int.unsigned i) dfl cases).
FEnd sel_switch_int_correct.

MetaData sel_switch_long_correct.
Axiom sel_switch_long_correct:
  forall tge dfl cases arg sp e m i t le,
  validate_switch Int64.modulus dfl cases t = true ->
  T.eval_expr tge sp e m le arg (Vlong i) ->
  T.eval_exitexpr tge sp e m le (T.XElet arg (sel_switch_long O t)) (switch_target (Int64.unsigned i) dfl cases).
FEnd sel_switch_long_correct.

FInduction transl_step_correct.
FProof.
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME;
  apply MS_state_inv in ME as (?f'&?s'&?k'&?e'&?m'&->&_&TF&TS&MC&LD&ME); fsimpl in TS; try (monadInv TS).
(* Sswitch *)
+ inv s. simpl in TS. fsimpl in TS.
  set (ct := compile_switch Int.modulus default cases) in *.
  destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS. monadInv H0.
  exploit transl_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  apply plus_one; fconstructor. assert (lenv = nil) by (apply cheat). subst. (* we know lenv = nil, our theorem statement is buggy *)
  eapply sel_switch_int_correct; eauto.
  eapply match_state; eauto.  fsimpl. reflexivity.
  set (ct := compile_switch Int64.modulus default cases) in *.
  destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS. monadInv H0.
  exploit transl_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  apply plus_one; fconstructor.
  assert (lenv = nil) by (apply cheat); subst. (*like above*)
  eapply sel_switch_long_correct; eauto.
  eapply match_state; eauto. fsimpl. reflexivity.
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

FDefinition nolabel := fun (s: S.stmt) =>
  forall lbl k, S.find_label s lbl k = None.
FDefinition nolabel' := fun (s: T.stmt) =>
  forall lbl k, T.find_label s lbl k = None.

FLemma sel_builtin_nolabel:
  forall optid ef args result, (sel_builtin optid ef args) = OK result -> nolabel' result.
FProofLemma.
  unfold sel_builtin; intros; red; intros.
  destruct ef; auto. (* destruct lookup_builtin_function; auto.*)
  destruct optid; auto. unfold sel_builtin_default in H; monadInv H;
  fsimpl; reflexivity. unfold sel_builtin_default in H; monadInv H. fsimpl; reflexivity.
  destruct Builtins.lookup_builtin_function; auto. destruct optid; auto. monadInv H.
  destruct (sel_known_builtin b x). monadInv EQ0. fsimpl; reflexivity.
  unfold sel_builtin_default in EQ0. monadInv EQ0. fsimpl; reflexivity.
  unfold Sno_op in H. monadInv H. fsimpl. fsimpl. reflexivity.
  monadInv H. fsimpl; reflexivity.
  repeat (unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity).
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
  unfold sel_builtin_default in H; monadInv H; fsimpl; reflexivity.
Qed. CloseFLemma.

FInduction find_label_commut.
FProof.
all: intros until k'; simpl; fsimpl; intros MC SE; fsimpl in SE; try (monadInv SE); simpl; fsimpl; auto.
+ rewrite (sel_builtin_nolabel o e l s' SE); auto.
Qed. FEnd find_label_commut.

FLemma transl_exprlist_correct:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall sp e m a v lenv,
  S.eval_exprlist ge sp e m lenv a v ->
  forall e' m',
  env_lessdef e e' -> Mem.extends m m' ->
  forall a', transl_exprlist a = OK a' ->
  exists v', T.eval_exprlist tge sp e' m' lenv a' v' /\ Val.lessdef_list v v'.
FProofLemma.
  induction 5; intros; simpl.
  exists (@nil val); split; auto. simpl in H3. monadInv H3. fconstructor.
  simpl in H5. monadInv H5.
  exploit transl_expr_correct; eauto.
  intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. fconstructor.
Qed. CloseFLemma.

MetaData eval_builtin_arg.
Axiom eval_builtin_arg:
  forall ge sp e m a v,
  T.eval_expr ge sp e m nil a v ->
  T.eval_builtin_arg ge sp e m (builtin_arg a) v.
FEnd eval_builtin_arg.

FLemma sel_builtin_arg_correct:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall sp e e' m m' a v c,
  env_lessdef e e' -> Mem.extends m m' ->
  S.eval_expr ge sp e m nil a v ->
  forall a', sel_builtin_arg a c = OK a' ->
  exists v',
     T.eval_builtin_arg tge sp e' m' a' v'
  /\ Val.lessdef v v'.
FProofLemma.
  intros. unfold sel_builtin_arg in H4. monadInv H4.
  exploit transl_expr_correct; eauto. intros (v1 & A & B).
  exists v1; split; auto.
  destruct (builtin_arg_ok (builtin_arg x)).
  (* destruct (builtin_arg_ok (builtin_arg (sel_expr a)) c).*)
  apply eval_builtin_arg; eauto.
  constructor; auto.
Qed. CloseFLemma.

FLemma sel_builtin_args_correct:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall sp e e' m m',
  env_lessdef e e' -> Mem.extends m m' ->
  forall al vl,
  S.eval_exprlist ge sp e m nil al vl ->
  forall cl args', sel_builtin_args al cl = OK args' ->
  exists vl',
     list_forall2 (T.eval_builtin_arg tge sp e' m')
                  args'
                  vl'
  /\ Val.lessdef_list vl vl'.
FProofLemma.
  induction 7; intros; simpl.
- exists (@nil val). split. simpl in H3. monadInv H3. constructor. constructor.
- simpl in H5. monadInv H5. monadInv EQ. assert (lenv = nil) by (apply cheat). subst. (* lenv issue *)
  exploit sel_builtin_arg_correct; eauto. unfold sel_builtin_arg. rewrite EQ0. simpl. reflexivity.
  intros (v1' & A & B).
  edestruct IHeval_exprlist as (vl' & C & D); eauto.
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed. CloseFLemma.

FLemma sel_builtin_res_correct:
  forall oid v e v' e',
  env_lessdef e e' -> Val.lessdef v v' ->
  env_lessdef (S.set_optvar oid v e) (T.set_builtin_res (sel_builtin_res oid) v' e').
FProofLemma.
  intros. destruct oid; simpl; auto. apply set_var_lessdef; auto.
Qed. CloseFLemma.

FLemma senv_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.senv_match TRANSL).
Qed. CloseFLemma.

FLemma sel_builtin_default_correct:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall optid ef al sp e1 m1 vl t v m2 e1' m1' f k,
  S.eval_exprlist ge sp e1 m1 nil al vl ->
  external_call ef ge vl m1 t v m2 ->
  env_lessdef e1 e1' -> Mem.extends m1 m1' ->
  forall result, sel_builtin_default optid ef al = OK result ->
  exists e2' m2',
     plus T.step tge (T.State f result k sp e1' m1')
                 t (T.State f T.Sskip k sp e2' m2')
  /\ env_lessdef (S.set_optvar optid v e1) e2'
  /\ Mem.extends m2 m2'.
FProofLemma.
  intros. unfold sel_builtin_default in H5. monadInv H5.
  exploit sel_builtin_args_correct; eauto. intros (vl' & A & B).
  exploit external_call_mem_extends; eauto. intros (v' & m2' & D & E & F & _).
  econstructor; exists m2'; split.
  apply plus_one.
  fconstructor. eapply external_call_symbols_preserved. eexact (senv_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSF eq_refl eq_refl). eexact D.
  split; auto. apply sel_builtin_res_correct; auto.
Qed. CloseFLemma.

MetaData eval_sel_known_builtin.
Axiom eval_sel_known_builtin:
  forall tge sp e m bf args a vl v le,
  sel_known_builtin bf args = Some a ->
  T.eval_exprlist tge sp e m le args vl ->
  exists v', T.eval_expr tge sp e m le a v' /\ Val.lessdef v v'.
FEnd eval_sel_known_builtin.

MetaData sel_builtin_transl_exprlist.
Axiom sel_builtin_transl_exprlist:
  forall source optid ef al, sel_builtin optid ef al = OK source ->
  exists al', transl_exprlist al = OK al'.
FEnd sel_builtin_transl_exprlist.

FLemma sel_builtin_correct:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall optid ef al sp e1 m1 vl t v m2 e1' m1' f k,
  S.eval_exprlist ge sp e1 m1 nil al vl ->
  external_call ef ge vl m1 t v m2 ->
  env_lessdef e1 e1' -> Mem.extends m1 m1' ->
  forall source, sel_builtin optid ef al = OK source ->
  exists e2' m2',
     plus T.step tge (T.State f source k sp e1' m1')
                 t (T.State f T.Sskip k sp e2' m2')
  /\ env_lessdef (S.set_optvar optid v e1) e2'
  /\ Mem.extends m2 m2'.
FProofLemma.
  intros.
  exploit sel_builtin_transl_exprlist; eauto. intros [al' EQal'].
  exploit transl_exprlist_correct; eauto. intros (vl' & A & B).
  exploit external_call_mem_extends; eauto. intros (v' & m2' & D & E & F & _).
  unfold sel_builtin in H5. unfold sel_builtin_default in H5.
  destruct ef;
    try (monadInv H5; eapply sel_builtin_default_correct; eauto;
      unfold sel_builtin_default; rewrite EQ; reflexivity).
  destruct (Builtins.lookup_builtin_function name sg) as [bf|] eqn:LKUP; eauto using sel_builtin_default_correct.
  simpl in D. red in D. rewrite LKUP in D. inv D.
  destruct optid as [id|]; monadInv H5. rewrite EQ in EQal'. injection EQal' as EQal'; subst al'.
- destruct (sel_known_builtin bf x) as [a|] eqn:SKB; eauto using sel_builtin_default_correct. monadInv EQ0.
  exploit eval_sel_known_builtin; eauto. intros (v'' & U & V).
  econstructor; exists m2'; split.
  apply plus_one. fconstructor.
  split; auto. apply set_var_lessdef; auto. apply Val.lessdef_trans with v'; eauto.
- exists e1', m2'; split.
  eapply plus_two. fconstructor. fconstructor. auto.
  simpl; auto.
Qed. CloseFLemma.

FInduction transl_step_correct.
FProof.
intros until cunit; intros LINK TRANSL A B; intros T1 ME;
  apply MS_state_inv in ME as (?f'&?s'&?k'&?e'&?m'&->&_&TF&TS&MC&LD&ME); fsimpl in TS; try (monadInv TS).
exploit sel_builtin_correct; eauto. assert (lenv = nil) by (apply cheat); subst. (* lenv issue *)
  eauto.
intros (e2' & m2' & P & Q & R).
  left; econstructor; split. eexact P. eauto using match_states_skip.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Builtin.

Trait Comp_External extends Base, Comp_Builtin.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

FInductive match_states : S.program -> S.program -> S.state -> T.state -> Prop :=
| match_builtin_1: forall cunit prog hf ef args optid f sp e k m al f' e' k' m' env
      (LINK: linkorder cunit prog)
      (* (HF: helper_functions_declared cunit hf) *)
      (* (TF: sel_function (prog_defmap cunit) hf f = OK f') *)
      (* (TYF: type_function f = OK env) *)
      (MC: match_cont cunit hf env k k')
      (EA: S.eval_exprlist ge sp e m al args)
      (LDE: env_lessdef e e')
      (ME: Mem.extends m m'),
    match_states
      (S.Callstate (External ef) args (S.Kcall optid f sp e k) m)
      (T.State f' (sel_builtin optid ef al) k' sp e' m')
| match_builtin_2: forall cunit hf v v' optid f sp e k m f' e' m' k' env
      (LINK: linkorder cunit prog)
      (* (HF: helper_functions_declared cunit hf) *)
      (* (TF: sel_function (prog_defmap cunit) hf f = OK f') *)
      (* (TYF: type_function f = OK env) *)
      (MC: match_cont cunit hf env k k')
      (LDV: Val.lessdef v v')
      (LDE: env_lessdef (set_optvar optid v e) e')
      (ME: Mem.extends m m'),
    match_states
      (S.Returnstate v (S.Kcall optid f sp e k) m)
      (T.State f' Sskip k' sp e' m').

FInduction transl_step_correct.
FProof.
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME; apply MS_state_inv in ME as (?f'&?s'&?k'&?e'&?m'&T1eq&_&TF&TS&MC&LD&ME); fsimpl in TS; try (monadInv TS).
+ (* destruct TF as (hf & HF & TF).*) unfold match_fundef in TF.
  monadInv TF.
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  apply plus_one; fconstructor. eapply external_call_symbols_preserved; eauto. eapply senv_preserved; eauto.
  econstructor; eauto.
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

Inherit eventually.

FInductive match_cont: S.program -> S.cont -> T.cont -> Prop :=
with match_call_cont: S.cont -> T.cont -> Prop :=
| match_cont_call: forall cunit prog id f sp e k f' e' k',
      linkorder cunit prog ->
      transl_function f = OK f' ->
      match_cont cunit k k' ->
      env_lessdef e e' ->
      match_call_cont (S.Kcall id f e sp k) (T.Kcall id f' e' sp k').

Closing Fact match_cont_call_inv : forall id f e sp k tk,
  match_call_cont (S.Kcall id f e sp k) tk ->
  exists f' e' k' cunit prog,
  tk = T.Kcall id f' e' sp k' /\ linkorder cunit prog /\
    transl_function f = OK f' /\ match_cont cunit k k' /\ env_lessdef e e'
  by plain { intros * H; inv H; eauto 10 }.

FInduction call_cont_commut with call_cont_commut'.
FProof.
all: intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd call_cont_commut with call_cont_commut'.

FInduction match_is_call_cont with match_is_call_cont'.
FProof.
- intros. fsimpl; auto.
Qed. FEnd match_is_call_cont with match_is_call_cont'.

FInduction find_label_commut.
FProof.
all: intros until k'; simpl; fsimpl; intros MC SE; fsimpl in SE; try (monadInv SE); simpl; fsimpl; auto.
- (* call *)
  destruct (classify_call e); simpl; auto; try (monadInv SE; fsimpl; auto).
  rewrite (sel_builtin_nolabel o ef l s' SE); auto.
- (* tailcall *)
  destruct (classify_call e); simpl; auto; monadInv SE; fsimpl; auto.
Qed. FEnd find_label_commut.

FInduction expr_is_addrof_ident_correct_helper about S.constant
  motive (fun (c : S.constant) => forall id,
     expr_is_addrof_ident (S.Econst c) = Some id -> S.Econst c = S.Econst (S.Oaddrsymbol id Ptrofs.zero)).
FProof.
all: intros; fsimpl in H; fsimpl in H; try discriminate.
destruct (Ptrofs.eq_dec i0 Ptrofs.zero).
- subst. rewrite Ptrofs.eq_true in H. inv H. auto.
- rewrite Ptrofs.eq_false in H by auto. discriminate.
Qed. FEnd expr_is_addrof_ident_correct_helper.

FInduction expr_is_addrof_ident_correct about
  S.expr motive (fun (e : S.expr) =>
    forall id,
    expr_is_addrof_ident e = Some id ->
    e = S.Econst (S.Oaddrsymbol id Ptrofs.zero)).
FProof.
all: intros; fsimpl in H1; fsimpl in H0; fsimpl in H; fsimpl; intros; try discriminate.
+ intros. fsimpl in H. eapply expr_is_addrof_ident_correct_helper.
  fsimpl. auto.
Qed. FEnd expr_is_addrof_ident_correct.

FLemma classify_call_correct:
  forall prog tprog ge tge cunit (LINK: linkorder cunit prog) (TRANSF: match_prog prog tprog),
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall sp e m a v fd lenv,
  S.eval_expr ge sp e m lenv a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call a with
  | self__Selection.Call_default => True
  | self__Selection.Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero
  | self__Selection.Call_builtin ef => fd = AST.External ef
  end.
FProofLemma.
  unfold classify_call; intros.
  destruct (expr_is_addrof_ident a) as [id|] eqn:EA; auto.
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  apply S.eval_expr_const_inv in H1. fsimpl in H1. inv H1. unfold Genv.symbol_address in *.
  destruct (Genv.find_symbol (Genv.globalenv prog) id) as [b|] eqn:FS; try discriminate.
  rewrite Genv.find_funct_find_funct_ptr in H2.
  assert (DFL: exists b1, Genv.find_symbol (Genv.globalenv prog) id = Some b1 /\ Vptr b Ptrofs.zero = Vptr b1 Ptrofs.zero) by (exists b; auto).
  assert (self__Selection.defmap = prog_defmap cunit) as -> by (apply cheat). (* linking *)
  unfold globdef; destruct (prog_defmap cunit)!id as [[[f|ef] |gv] |] eqn:G; auto.
  destruct (ef_inline ef) eqn:INLINE; auto.
  destruct (prog_defmap_linkorder _ _ _ _ LINK G) as (gd & P & Q).
  inv Q. inv H0.
- apply Genv.find_def_symbol in P. destruct P as (b' & X & Y). fold ge in X, Y.
  rewrite <- Genv.find_funct_ptr_iff in Y. congruence.
- simpl in INLINE. discriminate.
Qed. CloseFLemma.

FLemma functions_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall (v v': val) (f: S.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  exists cu tf, Genv.find_funct tge v' = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
FProofLemma.
  intros. inv H3.
  eapply Genv.find_funct_match; eauto.
  discriminate.
Qed. CloseFLemma.

FInduction transl_step_correct.
FProof.
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME; inv ME; fsimpl in TS; try (monadInv TS).
(* return *)
+ apply match_cont_call_inv in MC; unpack MC; subst. (* inv MC.*)
  left; econstructor; split.
  apply plus_one; fconstructor.
  eapply match_states_skip; eauto. assert (cunit = cunit0) by (apply cheat). (* linking *) subst. auto.
  unfold S.set_optvar. unfold T.set_optvar.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.

(* call *)
+ exploit classify_call_correct; eauto.
  assert (lenv = nil) as -> by (apply cheat). (* lenv issue *)
  destruct (classify_call a) as [ | id | ef].
- (* indirect *) monadInv TS. intro.
  exploit transl_expr_correct; eauto. intros [vf' [A B]].
  exploit transl_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros (cunit' & fd' & U & V & W).
  left; econstructor; split.
  apply plus_one; fconstructor; eauto. econstructor; eauto.
  eapply sig_function_translated; eauto.
  eapply match_callstate; eauto.
  eapply match_cont_call with (cunit := cunit); eauto.
- (* direct *)
  intros [b [U V]]. monadInv TS.
  exploit transl_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros (cunit' & fd' & X & Y & Z).
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  (*subst vf.*) econstructor; eauto. rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl). eauto.
  eapply sig_function_translated; eauto.
  eapply match_callstate; eauto.
  eapply match_cont_call with (cunit := cunit); eauto.
- (* turned into Sbuiltin *)
  intros EQ. subst fd.
  right; left; split. simpl; lia. split; auto. apply cheat. (* builtin stuff missing from match_states *)

(* tailcall *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto. destruct (classify_call a). monadInv TS.
  exploit transl_expr_correct; eauto. intros [vf' [A B]].
  exploit transl_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros (cunit' & fd' & E & F & G).
  left; econstructor; split.
  apply plus_one.
  exploit classify_call_correct. eexact LINK. eauto. eauto. eauto. eauto. eauto.
  destruct (classify_call a) as [ | id | ef]; intros.
  econstructor; eauto. econstructor; eauto. eapply sig_function_translated; eauto.
  destruct H2 as [b [U V]]. subst vf. inv B.
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. eapply sig_function_translated; eauto.
  econstructor; eauto. econstructor; eauto. eapply sig_function_translated; eauto.
  eapply match_callstate with (cunit := cunit'); eauto.
  eapply call_cont_commut; eauto.
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

MetaData eval_addressing.
Axiom eval_addressing:
  forall ge sp e m le chunk a v b ofs,
  T.eval_expr ge sp e m le a v ->
  v = Vptr b ofs ->
  match addressing' chunk a with (mode, args) =>
    exists vl,
    T.eval_exprlist ge sp e m le args vl /\
    eval_addressing ge (Vptr sp Ptrofs.zero) mode vl = Some v
  end.
FEnd eval_addressing.

FLemma eval_load:
  forall tge sp e m le a v chunk v',
  T.eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  T.eval_expr tge sp e m le (load chunk a) v'.
FProofLemma.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (eq_refl _)).
  destruct (addressing' chunk a). intros [vl [EV EQ]].
  eapply T.eval_Eload; eauto.
Qed. CloseFLemma.

FLemma eval_store:
  forall tge sp e m chunk a1 a2 v1 v2 f k m',
  T.eval_expr tge sp e m nil a1 v1 ->
  T.eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  T.step tge (T.State f (store chunk a1 a2) k sp e m)
        E0 (T.State f T.Sskip k sp e m').
FProofLemma.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (eq_refl _)).
  destruct (addressing' chunk a1). intros [vl [EV EQ]].
  eapply T.step_store; eauto.
Qed. CloseFLemma.

FInduction transl_expr_correct.
FProof.
all: intros; simpl; fsimpl.
+ fsimpl in TR. monadInv TR. exploit H; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed. FEnd transl_expr_correct.

FInduction find_label_commut.
FProof.
all: intros until k'; simpl; fsimpl; intros MC SE; fsimpl in SE; try (monadInv SE); simpl; fsimpl; auto.
+ unfold store. destruct (addressing' m x); fsimpl; auto.
Qed. FEnd find_label_commut.

FInduction transl_step_correct.
FProof.
all: intros until cunit; intros LINK TRANSL A B; intros T1 ME; inv ME; fsimpl in TS; try (monadInv TS).
(* store *)
+ exploit transl_expr_correct. try apply e1. try apply LINK. try apply TRANSL. reflexivity. reflexivity. apply EQ1. apply LD. apply ME0. intros [vaddr' [A B]].
  exploit transl_expr_correct. try apply e0. try apply LINK. try apply TRANSL. reflexivity. reflexivity. apply EQ. apply LD. apply ME0. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  assert (lenv = nil) by (apply cheat). (* lenv nil issue*)
  apply plus_one; eapply eval_store; eauto.
  rewrite <- H. auto. rewrite <- H. auto.
  eauto using match_states_skip.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

Family Selection.
FEnd Selection.

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
