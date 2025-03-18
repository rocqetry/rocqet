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

FDefinition env_lessdef := fun (e1 e2: S.env) =>
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

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
     match_call_cont (S.call_cont k) (T.call_cont k')).
FProof.
+ apply cheat.
+ apply cheat. (* proved by inversion on match_call_cont *)
Qed. FEnd call_cont_commut.

FInduction match_is_call_cont about match_cont motive
  (fun cunit k k' (_ : match_cont cunit k k') =>
    S.is_call_cont k ->
    match_call_cont k k' /\ T.is_call_cont k').
FProof.
all: intros; fsimpl in H0; try contradiction.
+ split. auto. apply cheat. (* TODO *) 
Qed. FEnd match_is_call_cont.

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

FLemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
FProofLemma.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
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
+  fsimpl. destruct (ident_eq lbl l).
  - eauto.
  -  apply H; eauto.
+ fsimpl; auto.
+ (*fsimpl. 
  exploit H; eauto.
  destruct (S.find_label __i lbl k) as [[sx kx] | ];
  destruct (T.find_label x0 lbl k') as [[sy ky] | ];
  intuition. *)
  apply cheat.
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
  apply plus_one; fconstructor. simpl; eauto.
  econstructor; eauto. eapply call_cont_commut; eauto. Unshelve. exact prog. apply cheat.
(* return some *)
+ exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit transl_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  econstructor; eauto. eapply call_cont_commut; eauto. Unshelve. exact prog. apply cheat.
(* label *)  
+ left; econstructor; split. apply plus_one; fconstructor. econstructor; eauto.
(* goto *)  
+ assert (transl_stmt (S.fn_body f) tt tt = OK (T.fn_body f')).
  { monadInv TF; simpl. congruence. }
  exploit (find_label_commut (S.fn_body f) cunit lbl (S.call_cont k)).
    apply match_cont_other. eapply call_cont_commut; eauto. eauto.
  unfold S.function_body in e0. rewrite e0. instantiate (1 := k'0).
  destruct (T.find_label (T.fn_body f') lbl (T.call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H0 as (P & Q).
  left; econstructor; split.
  apply plus_one; fconstructor; eauto.
  econstructor; eauto. Unshelve. exact prog. apply cheat. (* same thing for all of them *)
(* ifthenelse *)  
+ exploit transl_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv b0.
  left; exists (T.State f' (if b then x else x0) k' sp e' m'); split.
  apply plus_one; fconstructor; eauto. eapply eval_condexpr_of_expr; eauto. apply cheat. (* lenv = nil here actually *)
  constructor; eauto. destruct b; eauto.
  (* internal function *)
+ apply cheat.  
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Base.

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

Inherit Cfamtransl.

Family Cminorgen extends Cfamtransl.


FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.
FEnd Comp_Field.


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

Inherit Cfamtransl.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit exit_env.

MetaData shift_exit.
Fixpoint shift_exit (e: exit_env) (n: nat) {struct e} : nat :=
  match e, n with
  | nil, _ => n
  | false :: e', _ => Datatypes.S (shift_exit e' n)
  | true :: e', O => O
  | true :: e', Datatypes.S m => Datatypes.S (shift_exit e' m)
  end.
FEnd shift_exit.

FRecursion transl_stmt.
Case Sloop s :=
  (fun cenv xenv => 
    do ts <- transl_stmt s cenv xenv;
    OK (T.Sloop ts)).
Case Sblock s :=
  (fun cenv xenv =>
      do ts <- transl_stmt s cenv (true :: xenv);
      OK (T.Sblock ts)).
Case Sexit n :=
  (fun cenv xenv =>    
      OK (T.Sexit (shift_exit xenv n))).
FEnd transl_stmt.

FInductive match_cont: S.cont -> T.cont -> compilenv -> exit_env -> callstack -> Prop :=
| match_Kblock: forall k tk cenv xenv cs,
    match_cont k tk cenv xenv cs ->
    match_cont (S.Kblock k) (T.Kblock tk) cenv (true :: xenv) cs
| match_Kblock2: forall k tk cenv xenv cs,
    match_cont k tk cenv xenv cs ->
    match_cont k (T.Kblock tk) cenv (false :: xenv) cs.

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction transl_step_correct.
FProof.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.
+ apply cheat.  
Qed. FEnd transl_step_correct.

FEnd Cminorgen.

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

Inherit Cfamtransl.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion switch_table about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => nat -> list (Z * nat) * nat) by _rect.
Case LSnil := (fun k => (nil, k)).
Case LScons lbl stmt rem :=
(fun k =>
   match lbl with
   | None => let (tbl, dfl) := switch_table rem ((1 + k)%nat) in (tbl, k)
   | Some ni => let (tbl, dfl) := switch_table rem ((1 + k)%nat) in ((ni, k) :: tbl, dfl)
   end).
FEnd switch_table.

Inherit exit_env.

FRecursion switch_env about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => exit_env -> exit_env) by _rect.
Case LSnil := (fun e => e).
Case LScons a b ls' := (fun e => false :: switch_env ls' e).
FEnd switch_env.

(* Extending non mutual induction to be mutual *)
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => earg -> sarg -> res T.stmt)
  with transl_lbl_stmt about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => earg -> sarg -> T.stmt -> res T.stmt) by _rect.

Case Sswitch long e ls :=
  (fun cenv xenv => 
     let (tbl, dfl) := switch_table ls O in
     do te <- transl_expr e cenv;
     transl_lbl_stmt ls cenv (switch_env ls xenv) (T.Sswitch long te tbl dfl)).

Case LSnil 
  := (fun cenv xenv body => OK (T.Sseq (T.Sblock body) T.Sskip)).
Case LScons a s ls' :=
  (fun cenv xenv body =>
     do ts <- transl_stmt s cenv xenv;
     transl_lbl_stmt ls' cenv (List.tail xenv) (T.Sseq (T.Sblock body) ts)).
FEnd transl_stmt with transl_lbl_stmt.

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Cminorgen.

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

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Selection.

FEnd Comp_Switch.

Trait Comp_Call extends Base.

Family Cfam.

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

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> fenv -> env -> mem -> letenv -> list expr -> list val -> Prop :=
  | eval_Enil: forall ge lenv e le m,
      eval_exprlist ge le e m lenv nil nil
  | eval_Econs: forall ge le e m lenv a1 al v1 vl,
      eval_expr ge le e m lenv a1 v1 -> eval_exprlist ge le e m lenv al vl ->
      eval_exprlist ge le e m lenv (a1 :: al) (v1 :: vl).
FEnd eval_exprlist.

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

MetaData eval_exprlist binds eval_Enil, eval_Econs.
Inductive eval_exprlist: genv -> fenv -> env -> mem -> letenv -> list expr -> list val -> Prop :=
  | eval_Enil: forall ge lenv e le m,
      eval_exprlist ge le e m lenv nil nil
  | eval_Econs: forall ge le e m lenv a1 al v1 vl,
      eval_expr ge le e m lenv a1 v1 -> eval_exprlist ge le e m lenv al vl ->
      eval_exprlist ge le e m lenv (a1 :: al) (v1 :: vl).
FEnd eval_exprlist.

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

Inherit Cfamtransl.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit transl_expr.
MetaData transl_exprlist.
Fixpoint transl_exprlist 
  (cenv: compilenv) (el: list S.expr)
                     {struct el}: res (list T.expr) :=
  match el with
  | nil =>
      OK nil
  | e1 :: e2 =>
      do te1 <- transl_expr e1 cenv;
      do te2 <- transl_exprlist cenv e2;
      OK (te1 :: te2)
  end.
FEnd transl_exprlist.

FRecursion transl_stmt.
Case Scall optid sig e el :=
  (fun cenv xenv => 
     do te <- transl_expr e cenv;
     do tel <- transl_exprlist cenv el;
   OK (T.Scall optid sig te tel)).
FEnd transl_stmt.


Inherit transl_expr_correct.

FInductive match_cont: S.cont -> T.cont -> compilenv -> exit_env -> callstack -> Prop :=
| match_Kcall: forall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv',
   transl_funbody cenv sz fn = OK tfn ->
   match_cont k tk cenv xenv cs ->
   match_cont (S.Kcall optid fn e le k)
      (T.Kcall optid tfn te sp tk)
      cenv' nil
      (Frame cenv tfn le e te sp lo hi :: cs). 

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction transl_step_correct.
FProof.
+ apply cheat.
+ apply cheat.  
Qed. FEnd transl_step_correct. 

FEnd Cminorgen.

Family Selection extends Cfamtransl.
Family S extends Cminor. FEnd S.
Family T extends CminorSel. FEnd T.

MetaData call_kind binds Call_default, Call_imm, Call_builtin.
Inductive call_kind : Type :=
  | Call_default
  | Call_imm (id: ident).
  (* | Call_builtin (ef: external_function).*)
FEnd call_kind.

FRecursion expr_is_addrof_ident_cst about S.constant motive (fun (_ : S.constant) => option ident) by _rect.
Case Oaddrsymbol id ofs := (if Ptrofs.eq ofs Ptrofs.zero then Some id else None).
Case _ := None.
FEnd expr_is_addrof_ident_cst.

FRecursion expr_is_addrof_ident about S.expr motive (fun (_ : S.expr) => option ident) by _rect.
Case Econst cst := (expr_is_addrof_ident_cst cst).
Case _ := None.                      
FEnd expr_is_addrof_ident.

FDefinition classify_call := fun (e: S.expr) =>
  match expr_is_addrof_ident e with
  | None => Call_default
  | Some id => Call_imm id
      (*match defmap!id with
      | Some(Gfun(External ef)) => if ef_inline ef then Call_builtin ef else Call_imm id
      | _ => Call_imm id
      end*)
  end.

Inherit transl_expr.

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

(* use default call *)
FRecursion transl_stmt.
Case Scall optid sg fn args :=
  (fun 
      OK (match classify_call fn with
      | Call_default => Scall optid sg (inl _ (sel_expr fn)) (sel_exprlist args)
      | Call_imm id => Scall optid sg (inr _ id) (sel_exprlist args)
      (* | Call_builtin ef => sel_builtin optid ef args*)
          end).
| Cminor.Stailcall sg fn args =>
      OK (match classify_call fn with
      | Call_imm id => Stailcall sg (inr _ id) (sel_exprlist args)
      | _ => Stailcall sg (inl _ (sel_expr fn)) (sel_exprlist args)
      end)
FEnd transl_stmt.

FEnd Selection.

FEnd Comp_Call.

Trait Comp_Builtin extends Base, Comp_Call.

Family Cfam. FEnd Cfam.

Family Csharpminor extends Cfam.
FInductive stmt : Type :=
| Sbuiltin : option ident -> external_function -> list expr -> stmt.

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
