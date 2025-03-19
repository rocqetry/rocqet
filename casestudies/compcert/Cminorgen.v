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
Require Import Csharpminor.
Require Import Cminor.
Require Import Cfamtransl.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

Trait Base.

Family Cminorgen extends Cfamtransl.

Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FDefinition compilenv := PTree.t Z.
FDefinition exit_env : Type := list bool.

FRecursion transl_constant about S.constant motive (fun (_ : S.constant) => T.constant) by _rect.
Case Ointconst n := (T.Ointconst n).
Case Ofloatconst n := (T.Ofloatconst n).
Case Osingleconst n := (T.Osingleconst n).
Case Olongconst n := (T.Olongconst n).
FEnd transl_constant.

FOverride Definition earg := compilenv.

FRecursion transl_expr.
Case Econst c := (fun earg => OK (T.Econst (transl_constant c))).
Case Eunop op e1 := 
  (fun arg => do te1 <- transl_expr e1 arg; OK (T.Eunop op te1)).
Case Ebinop op e1 e2 :=
  (fun arg => 
     do te1 <- transl_expr e1 arg;
     do te2 <- transl_expr e2 arg;
     OK (T.Ebinop op te1 te2)).
FEnd transl_expr.

FOverride Definition sarg := exit_env.

FRecursion transl_stmt.
Case Sifthenelse e s1 s2 :=
 (fun earg sarg => 
    do te <- transl_expr e earg;
    do ts1 <- transl_stmt s1 earg sarg;
    do ts2 <- transl_stmt s2 earg sarg;
    OK (T.Sifthenelse te ts1 ts2)).
FEnd transl_stmt.

(* Stack layout *)
FDefinition block_alignment : Z -> Z := fun sz =>
    if zlt sz 2 then 1
    else if zlt sz 4 then 2
    else if zlt sz 8 then 4 else 8.

FDefinition assign_variable : compilenv * Z -> ident * Z -> compilenv * Z := 
    fun cenv_stacksize id_sz => 
    let (id, sz) := id_sz in
    let (cenv, stacksize) := cenv_stacksize in
    let ofs := align stacksize (block_alignment sz) in
    (PTree.set id ofs cenv, ofs + Z.max 0 sz).

FDefinition assign_variables : compilenv * Z -> list (ident * Z) -> compilenv * Z :=
    fun cenv_stacksize vars => List.fold_left assign_variable vars cenv_stacksize.

FDefinition build_compilenv : S.function -> compilenv * Z :=
    fun f => assign_variables (PTree.empty Z, 0) (VarSort.sort (S.fn_vars f)).

(* Translate Function, Fundef, Program *)
FDefinition transl_funbody := 
fun (cenv: compilenv) (stacksize: Z) (f: S.function) =>
  do tbody <- transl_stmt (S.fn_body f) cenv nil ;
  OK (T.mkfunction
        (S.fn_sig f)
        (S.fn_params f)
        (S.fn_temps f)
        stacksize
        tbody).

FOverride Definition transl_function := fun f =>
  let (cenv, stacksize) := build_compilenv f in
  if zle stacksize Ptrofs.max_unsigned
  then transl_funbody cenv stacksize f
  else Error(msg "Cminorgen: too many local variables, stack size exceeded").

Inherit transl_program.

(* Correctness *)

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

(* Csharpminor *)
(* temp_env = env *)
(* env = fenv *)
FDefinition match_temps := fun (f: meminj) (le: S.env) (te: T.env) =>
  forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ Val.inject f v v'.

MetaData match_var.
Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
  | match_var_local: forall b sz ofs,
      Val.inject f (Vptr b Ptrofs.zero) (Vptr sp (Ptrofs.repr ofs)) ->
      match_var f sp (Some(b, sz)) (Some ofs)
  | match_var_global:
      match_var f sp None None.
FEnd match_var.

MetaData match_env.
Record match_env (f: meminj) (cenv: compilenv)
                 (e: S.fenv) (sp: T.fenv)
                 (lo hi: block) : Prop :=
  mk_match_env {
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);
    me_low_high:
      Ple lo hi;
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> Ple lo b /\ Plt b hi;
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz);
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> Plt b lo -> Plt tb sp
  }.
FEnd match_env.

MetaData match_globalenvs.
Inductive match_globalenvs (ge: S.genv) (f: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).
FEnd match_globalenvs.

FDefinition match_bounds := fun (e: S.fenv) (m: mem) =>
  forall id b sz ofs p,
    PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.

MetaData is_reachable_from_env.
Inductive is_reachable_from_env (f: meminj) (e: S.fenv) (sp: T.fenv) (ofs: Z) : Prop :=
  | is_reachable_intro: forall id b sz delta,
      e!id = Some(b, sz) ->
      f b = Some(sp, delta) ->
      delta <= ofs < delta + sz ->
      is_reachable_from_env f e sp ofs.
FEnd is_reachable_from_env.

FDefinition padding_freeable := fun (f: meminj) (e: S.fenv) (tm: mem) (sp: T.fenv) (sz: Z) =>
  forall ofs,
  0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.

MetaData frame binds Frame.
Inductive frame : Type :=
   Frame(cenv: compilenv)
       (tf: T.function)
       (e: S.fenv)
       (le: S.env)
       (te: T.env)
       (sp: T.fenv)
       (lo hi: block).
FEnd frame.

FDefinition callstack : Type := list frame.

MetaData match_callstack.
Inductive match_callstack (ge: S.genv) (f: meminj) (m: mem) (tm: mem):
                          callstack -> block -> block -> Prop :=
  | mcs_nil:
      forall hi bound tbound,
      match_globalenvs ge f hi ->
      Ple hi bound -> Ple hi tbound ->
      match_callstack ge f m tm nil bound tbound
  | mcs_cons:
      forall cenv tf e le te sp lo hi cs bound tbound
        (BOUND: Ple hi bound)
        (TBOUND: Plt sp tbound)
        (MTMP: match_temps f le te)
        (MENV: match_env f cenv e sp lo hi)
        (BOUND: match_bounds e m)
        (PERM: padding_freeable f e tm sp (T.fn_stackspace tf))
        (MCS: match_callstack ge f m tm cs lo sp),
      match_callstack ge f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound.
FEnd match_callstack.

FInduction transl_constant_correct about S.constant
  motive (fun (cst : S.constant) =>
    forall f tge sp v,
       S.eval_constant cst = Some v ->
       exists tv,
          T.eval_constant (transl_constant cst) tge sp = Some tv
       /\ Val.inject f v tv).
FProof.
all: intros; inv H.
+ exists (Vint i); do 2 fsimpl. fsimpl in H1. inv H1. auto.
+ exists (Vfloat f); do 2 fsimpl. fsimpl in H1. inv H1. auto.
+ exists (Vsingle f); do 2 fsimpl. fsimpl in H1. inv H1. auto.
+ exists (Vlong i); do 2 fsimpl. fsimpl in H1. inv H1. auto.
Qed. FEnd transl_constant_correct.

Ltac TrivialExists :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ Val.inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ Val.inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.

FLemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  Val.inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ Val.inject f v tv.
FProofLemma.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_int f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_intu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_int f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_intu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_long f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_longu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_long f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_longu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
Qed. CloseFLemma.

FLemma val_inject_val_of_bool:
  forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
FProofLemma.
  intros; destruct b; constructor.
Qed. CloseFLemma.

FLemma val_inject_val_of_optbool:
  forall f ob, Val.inject f (Val.of_optbool ob) (Val.of_optbool ob).
FProofLemma.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed. CloseFLemma.

FLemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ Val.inject f v tv.
FProofLemma.
  destruct op; simpl; intros; inv H.
- TrivialExists. apply Val.add_inject; auto.
- TrivialExists. apply Val.sub_inject; auto.
- TrivialExists. inv H0; inv H1; constructor.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H4. TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H4. TrivialExists.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists. apply Val.addl_inject; auto.
- TrivialExists. apply Val.subl_inject; auto.
- TrivialExists. inv H0; inv H1; constructor.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H4. TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H4. TrivialExists.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- (* cmp *)
  TrivialExists. inv H0; inv H1; auto. apply val_inject_val_of_optbool.
- (* cmpu *)
  TrivialExists. unfold Val.cmpu.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  replace (Val.cmpu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  apply val_inject_val_of_optbool.
  symmetry. eapply Val.cmpu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  simpl; auto.
- (* cmpf *)
  TrivialExists. inv H0; inv H1; auto. apply val_inject_val_of_optbool.
- (* cmpfs *)
  TrivialExists. inv H0; inv H1; auto. apply val_inject_val_of_optbool.
- (* cmpl *)
  unfold Val.cmpl in *. inv H0; inv H1; simpl in H4; inv H4.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
- (* cmplu *)
  unfold Val.cmplu in *.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  simpl in H4; inv H4.
  replace (Val.cmplu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
  symmetry. eapply Val.cmplu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  discriminate.
Qed. CloseFLemma.
  
FInduction transl_expr_correct about S.eval_expr motive
  (fun ge fenv e m lenv a v (_ : S.eval_expr ge fenv e m lenv a v) =>
     forall prog tprog tge, match_prog prog tprog ->
     Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
     forall f tm cenv tf te tfenv lo hi cs
            (MINJ: Mem.inject f m tm)
            (MATCH: match_callstack ge f m tm
               (Frame cenv tf fenv e te tfenv lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm)),
    forall ta
       (TR: transl_expr a cenv = OK ta),
          exists tv,
            T.eval_expr tge tfenv te tm lenv ta tv
         /\ Val.inject f v tv).
FProof.
all: intros; fsimpl in TR; try (monadInv TR).
(* Evar *)
+ inv MATCH. exploit MTMP; eauto. intros [tv [A B]].
  exists tv; split. fconstructor; auto. auto.
(* Econst *)  
+ exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split; eauto. fconstructor; eauto.
(* Eunop *)  
+ exploit H; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit eval_unop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split; auto. fconstructor; eauto.
(* Ebinop *)  
+ exploit H0; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit H; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. fconstructor; eauto. auto.
Qed. FEnd transl_expr_correct.

MetaData match_cont.
Inductive match_cont: S.cont -> T.cont -> compilenv -> exit_env -> callstack -> Prop :=
| match_Kstop: forall cenv xenv,
   match_cont S.Kstop T.Kstop cenv xenv nil
| match_Kseq: forall s k ts tk cenv xenv cs,
   transl_stmt s cenv xenv = OK ts ->
   match_cont k tk cenv xenv cs ->
   match_cont (S.Kseq s k) (T.Kseq ts tk) cenv xenv cs
| match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
   transl_stmt s1 cenv xenv = OK ts1 ->
   match_cont (S.Kseq s2 k) tk cenv xenv cs ->
   match_cont (S.Kseq (S.Sseq s1 s2) k)
     (T.Kseq ts1 tk) cenv xenv cs.
FEnd match_cont.

Closing Fact match_Kstop_inv : forall tk cenv xenv cs,
    match_cont S.Kstop tk cenv xenv cs ->
    tk = T.Kstop /\ cs = nil
by plain { intros until cs; intros H; inv H; eauto }.

MetaData match_states.
Inductive match_states (ge : S.genv): S.state -> T.state -> Prop :=
| match_state:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt s cenv xenv = OK ts)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack ge f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv xenv cs),
      match_states ge (S.State fn s k e le m)
                   (T.State tfn ts tk sp te tm)
| match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt s1 cenv xenv = OK ts1)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack ge f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (S.Kseq s2 k) tk cenv xenv cs),
      match_states ge (S.State fn (S.Sseq s1 s2) k e le m)
                   (T.State tfn ts1 tk sp te tm)
| match_callstate:
      forall fd args k m tfd targs tk tm f cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack ge f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: S.is_call_cont k)
      (ARGSINJ: Val.inject_list f args targs),
      match_states ge (S.Callstate fd args k m)
                   (T.Callstate tfd targs tk tm)
| match_returnstate:
      forall v k m tv tk tm f cs cenv
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack ge f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: Val.inject f v tv),
      match_states ge (S.Returnstate v k m)
        (T.Returnstate tv tk tm).
FEnd match_states.

FRecursion seq_left_depth about S.stmt motive (fun (_: S.stmt) => nat) by _rect.
Case Sseq s1 s2 := (Datatypes.S (seq_left_depth s1)).
Case _ := O.
FEnd seq_left_depth.

FDefinition measure := fun (S: S.state) =>
  match S with
  | self__Cminorgen.S.State fn s k e le m => seq_left_depth s
  | _ => O
  end.

Closing Fact kstop_not_kseq : forall s k, S.Kstop = S.Kseq s k -> False
    by plain { intros until k; intros H; discriminate; eauto }.

Closing Fact kseq_injective : forall s0 k0 s k, S.Kseq s0 k0 = S.Kseq s k -> s0 = s /\ k = k0
    by plain { intros until k; intros H; injection H; eauto }.

Closing Fact Sseq_injective : forall s0 k0 s k, S.Sseq s0 k0 = S.Sseq s k -> s0 = s /\ k = k0
    by plain { intros until k; intros H; injection H; eauto }.

FLemma match_temps_assign:
  forall f le te id v tv,
  match_temps f le te ->
  Val.inject f v tv ->
  match_temps f (PTree.set id v le) (PTree.set id tv te).
FProofLemma.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H1. exists tv; auto.
  eauto.
Qed. CloseFLemma.

FLemma match_callstack_set_temp:
  forall ge f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  Val.inject f v tv ->
  match_callstack ge f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack ge f m tm (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
FProofLemma.
  intros. inv H0. constructor; auto.
  eapply match_temps_assign; eauto.
Qed. CloseFLemma.

FLemma free_list_freeable:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b lo hi,
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
FProofLemma.
  induction l; simpl; intros.
  contradiction.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  destruct H0. inv H.
  eauto with mem.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed. CloseFLemma.

FLemma in_blocks_of_env:
  forall e id b sz,
  e!id = Some(b, sz) -> In (b, 0, sz) (S.blocks_of_env e).
FProofLemma.
  unfold S.blocks_of_env; intros.
  change (b, 0, sz) with (S.block_of_binding (id, (b, sz))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed. CloseFLemma.

FLemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
FProofLemma.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi].
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed. CloseFLemma.

FLemma match_callstack_incr_bound:
  forall ge f m tm cs bound tbound bound' tbound',
  match_callstack ge f m tm cs bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_callstack ge f m tm cs bound' tbound'.
FProofLemma.
  intros. inv H.
  econstructor; eauto. extlia. extlia.
  constructor; auto. extlia. extlia.
Qed. CloseFLemma.

FLemma match_temps_invariant:
  forall f f' le te,
  match_temps f le te ->
  inject_incr f f' ->
  match_temps f' le te.
FProofLemma.
  intros; red; intros. destruct (H _ _ H1) as [v' [A B]]. exists v'; eauto.
Qed. CloseFLemma.

Ltac geninv x :=
  let H := fresh in (generalize x; intro H; inv H).

FLemma match_env_invariant:
  forall f1 cenv e sp lo hi f2,
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> f1 b = Some(sp, delta)) ->
  (forall b, Plt b lo -> f2 b = f1 b) ->
  match_env f2 cenv e sp lo hi.
FProofLemma.
  intros. destruct H. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
(* bounded *)
  intros. eauto.
(* below *)
  intros. rewrite H2 in H; eauto.
Qed. CloseFLemma.

FLemma match_bounds_invariant:
  forall e m1 m2,
  match_bounds e m1 ->
  (forall id b sz ofs p,
   PTree.get id e = Some(b, sz) -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_bounds e m2.
FProofLemma.
  intros; red; intros. eapply H; eauto.
Qed. CloseFLemma.

FLemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv lo hi f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b hi -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
FProofLemma.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto.
Qed. CloseFLemma.

FLemma match_callstack_invariant:
  forall ge f1 m1 tm1 f2 m2 tm2 cs bound tbound,
  match_callstack ge f1 m1 tm1 cs bound tbound ->
  inject_incr f1 f2 ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall sp ofs, Plt sp tbound -> Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b bound -> f2 b = f1 b) ->
  (forall b b' delta, f2 b = Some(b', delta) -> Plt b' tbound -> f1 b = Some(b', delta)) ->
  match_callstack ge f2 m2 tm2 cs bound tbound.
FProofLemma.
  induction 1; intros.
  (* base case *)
  econstructor; eauto.
  inv H. constructor; intros; eauto.
  eapply IMAGE; eauto. eapply H6; eauto. extlia.
  (* inductive case *)
  assert (Ple lo hi) by (eapply me_low_high; eauto).
  econstructor; eauto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
    intros. apply H3. extlia.
  eapply match_bounds_invariant; eauto.
    intros. eapply H1; eauto.
    exploit me_bounded; eauto. extlia.
  eapply padding_freeable_invariant; eauto.
    intros. apply H3. extlia.
  eapply IHmatch_callstack; eauto.
    intros. eapply H1; eauto. extlia.
    intros. eapply H2; eauto. extlia.
    intros. eapply H3; eauto. extlia.
    intros. eapply H4; eauto. extlia.
Qed. CloseFLemma.

FLemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
FProofLemma.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed. CloseFLemma.

FLemma match_callstack_freelist:
  forall ge f cenv tf e le te sp lo hi cs m m' tm,
  Mem.inject f m tm ->
  Mem.free_list m (S.blocks_of_env e) = Some m' ->
  match_callstack ge f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  exists tm',
  Mem.free tm sp 0 (T.fn_stackspace tf) = Some tm'
  /\ match_callstack ge f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f m' tm'.
FProofLemma.
  intros until tm; intros INJ FREELIST MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm sp 0 (T.fn_stackspace tf) = Some tm'}).
  apply Mem.range_perm_free.
  red; intros.
  exploit PERM; eauto. intros [A | A].
  auto.
  inv A. assert (Mem.range_perm m b 0 sz Cur Freeable).
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply Mem.perm_inject; eauto. apply H3. lia.
  destruct X as [tm' FREE].
  exploit nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
  rewrite NEXT; rewrite NEXT'.
  apply match_callstack_incr_bound with lo sp; try lia.
  apply match_callstack_invariant with f m tm; auto.
  intros. eapply perm_freelist; eauto.
  intros. eapply Mem.perm_free_1; eauto. left; unfold block; extlia. extlia. extlia.
  eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto. intros [id [sz A]].
  exists 0; exists sz; split.
  eapply in_blocks_of_env; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_max. eauto.
Qed. CloseFLemma.

(*FInduction match_call_cont about match_cont motive
  (fun k tk cenv xenv cs (_ : match_cont k tk cenv xenv cs) =>    
    match_cont k tk cenv xenv cs ->
    match_cont (S.call_cont k) (T.call_cont tk) cenv nil cs).
FProof.
all: intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_call_cont.*)
Closing Fact match_call_cont:
  forall k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  match_cont (S.call_cont k) (T.call_cont tk) cenv nil cs
by plain { induction 1; simpl; auto; econstructor; eauto }.

FInduction transl_find_label about S.stmt motive
  (fun (s : S.stmt) =>
     forall k xenv cenv lbl cs ts tk,
       transl_stmt s cenv xenv = OK ts ->
       match_cont k tk cenv xenv cs ->
       match S.find_label s lbl k with
       | None => T.find_label ts lbl tk = None
       | Some(s', k') =>
           exists ts', exists tk', exists xenv',
             T.find_label ts lbl tk = Some(ts', tk')
             /\ transl_stmt s' cenv xenv' = OK ts'
             /\ match_cont k' tk' cenv xenv' cs
       end).
FProof.
all: intros; fsimpl in H; try (monadInv H); simpl; do 2 fsimpl; auto.
(* seq *)
+ unfold transl_stmtSseq in *. monadInv H1. exploit H. eauto. eapply match_Kseq. eexact EQ1. eauto.
  fsimpl. instantiate (1:=lbl). destruct (S.find_label __i lbl (S.Kseq __i0 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H1. eapply H0; eauto. 

(* return *)  
+  destruct o; fsimpl in H; monadInv H; fsimpl; auto.
   
(* label *)   
+ unfold transl_stmtSlabel in *. monadInv H0. fsimpl. 
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  eapply H; eauto.  

(* ifthenelse *)  
+ unfold transl_stmtSifthenelse in *. monadInv H1.
  exploit H. eauto. eauto. fsimpl. instantiate (1:=lbl).
  destruct (S.find_label __i lbl k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto. 
  intro. rewrite H1. eapply H0; eauto. 
Qed. FEnd transl_find_label.

FLemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k',
  transl_funbody cenv size f = OK tf ->
  match_cont k tk cenv xenv cs ->
  S.find_label (S.fn_body f) lbl (S.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     T.find_label (T.fn_body tf) lbl (T.call_cont tk) = Some(ts', tk')
  /\ transl_stmt s' cenv xenv' = OK ts'
  /\ match_cont k' tk' cenv xenv' cs.
FProofLemma.
  intros. monadInv H. simpl. fsimpl.
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0. 
  instantiate (1 := lbl). rewrite H1. auto.
Qed. CloseFLemma.

FLemma bool_of_val_inject:
  forall f v tv b,
  Val.bool_of_val v b -> Val.inject f v tv -> Val.bool_of_val tv b.
FProofLemma.
  intros. inv H0; inv H; constructor; auto.
Qed. CloseFLemma.

FLemma symbols_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.find_symbol_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma senv_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  Senv.equiv ge tge.
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.senv_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma function_ptr_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall (b: block) (f: S.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
    Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.find_funct_ptr_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma functions_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall (v: val) (f: S.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
FProofLemma.
intros until tge; intros TRANSL A B. subst.
apply (Genv.find_funct_transf_partial TRANSL).
Qed. CloseFLemma.

FLemma sig_preserved_body:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf ->
  (T.fn_sig tf) = S.fn_sig f.
FProofLemma.
  intros. unfold transl_funbody in H. monadInv H2; reflexivity.
Qed. CloseFLemma.

FLemma sig_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall f tf,
  transl_fundef f = OK tf ->
  T.funsig tf = S.funsig f.
FProofLemma.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv f).
  case (zle z Ptrofs.max_unsigned); simpl bind; try congruence.
  intros. monadInv H2. simpl. eapply sig_preserved_body; eauto.
  intro. inv H2. reflexivity.
Qed. CloseFLemma.

Require Import Permutation.
Remark permutation_norepet:
  forall (A: Type) (l l': list A), Permutation l l' -> list_norepet l -> list_norepet l'.
Proof.
  induction 1; intros.
  constructor.
  inv H0. constructor; auto. red; intros; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  inv H. simpl in H2. inv H3. constructor. simpl; intuition. constructor. intuition. auto.
  eauto.
Qed.

FDefinition cenv_compat := fun (cenv: compilenv) (vars: list (ident * Z)) (tsz: Z) =>
  forall id sz,
  In (id, sz) vars ->
  exists ofs,
      PTree.get id cenv = Some ofs
   /\ Mem.inj_offset_aligned ofs sz
   /\ 0 <= ofs
   /\ ofs + Z.max 0 sz <= tsz.

FDefinition cenv_separated := fun (cenv: compilenv) (vars: list (ident * Z)) =>
  forall id1 sz1 ofs1 id2 sz2 ofs2,
  In (id1, sz1) vars -> In (id2, sz2) vars ->
  PTree.get id1 cenv = Some ofs1 -> PTree.get id2 cenv = Some ofs2 ->
  id1 <> id2 ->
  ofs1 + sz1 <= ofs2 \/ ofs2 + sz2 <= ofs1.

FLemma block_alignment_pos:
  forall sz, block_alignment sz > 0.
FProofLemma.
  unfold block_alignment; intros.
  destruct (zlt sz 2). lia.
  destruct (zlt sz 4). lia.
  destruct (zlt sz 8); lia.
Qed. CloseFLemma.

FLemma inj_offset_aligned_block:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz.
FProofLemma.
  intros; red; intros.
  apply Z.divide_trans with (block_alignment sz).
  unfold align_chunk. unfold block_alignment.
  generalize Z.divide_1_l; intro.
  generalize Z.divide_refl; intro.
  assert (2 | 4). exists 2; auto.
  assert (2 | 8). exists 4; auto.
  assert (4 | 8). exists 2; auto.
  destruct (zlt sz 2).
  destruct chunk; simpl in *; auto; extlia.
  destruct (zlt sz 4).
  destruct chunk; simpl in *; auto; extlia.
  destruct (zlt sz 8).
  destruct chunk; simpl in *; auto; extlia.
  destruct chunk; simpl; auto.
  apply align_divides. apply block_alignment_pos.
Qed. CloseFLemma.

FLemma assign_variable_sound:
  forall cenv1 sz1 id sz cenv2 sz2 vars,
  assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) ->
  ~In id (map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ (id, sz) :: nil) sz2
  /\ cenv_separated cenv2 (vars ++ (id, sz) :: nil).
FProofLemma.
  unfold assign_variable; intros until vars; intros ASV NOREPET POS COMPAT SEP.
  inv ASV.
  assert (LE: sz1 <= align sz1 (block_alignment sz)). apply align_le. apply block_alignment_pos.
  assert (EITHER: forall id' sz',
             In (id', sz') (vars ++ (id, sz) :: nil) ->
             In (id', sz') vars /\ id' <> id \/ (id', sz') = (id, sz)).
    intros. rewrite in_app in H. destruct H.
    left; split; auto. red; intros; subst id'. elim NOREPET.
    change id with (fst (id, sz')). apply in_map; auto.
    simpl in H. destruct H. auto. contradiction.
  split; red; intros.
  apply EITHER in H. destruct H as [[P Q] | P].
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  exists ofs.
  split. rewrite PTree.gso; auto.
  split. auto. split. auto. zify; lia.
  inv P. exists (align sz1 (block_alignment sz)).
  split. apply PTree.gss.
  split. apply inj_offset_aligned_block.
  split. lia.
  lia.
  apply EITHER in H; apply EITHER in H0.
  destruct H as [[P Q] | P]; destruct H0 as [[R S] | R].
  rewrite PTree.gso in *; auto. eapply SEP; eauto.
  inv R. rewrite PTree.gso in H1; auto. rewrite PTree.gss in H2; inv H2.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs1) by congruence. subst ofs.
  left. zify; lia.
  inv P. rewrite PTree.gso in H2; auto. rewrite PTree.gss in H1; inv H1.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs2) by congruence. subst ofs.
  right. zify; lia.
  congruence.
Qed. CloseFLemma.

FLemma assign_variable_incr:
  forall id sz cenv stksz cenv' stksz',
  assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') -> stksz <= stksz'.
FProofLemma.
  simpl; intros. inv H.
  generalize (align_le stksz (block_alignment sz) (block_alignment_pos sz)).
  assert (0 <= Z.max 0 sz). apply Zmax_bound_l. lia.
  lia.
Qed. CloseFLemma.

FLemma assign_variables_sound:
  forall vars' cenv1 sz1 cenv2 sz2 vars,
  assign_variables (cenv1, sz1) vars' = (cenv2, sz2) ->
  list_norepet (map fst vars' ++ map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ vars') sz2 /\ cenv_separated cenv2 (vars ++ vars').
FProofLemma.
  induction vars'; simpl; intros.
  rewrite app_nil_r. inv H; auto.
  destruct a as [id sz].
  simpl in H0. inv H0. rewrite in_app in H6.
  rewrite list_norepet_app in H7. destruct H7 as [P [Q R]].
  destruct (assign_variable (cenv1, sz1) (id, sz)) as [cenv' sz'] eqn:?.
  exploit assign_variable_sound.
    eauto.
    instantiate (1 := vars). tauto.
    auto. auto. auto.
  intros [A B].
  exploit IHvars'.
    eauto.
    instantiate (1 := vars ++ ((id, sz) :: nil)).
    rewrite list_norepet_app. split. auto.
    split. rewrite map_app. apply list_norepet_append_commut. simpl. constructor; auto.
    rewrite map_app. simpl. red; intros. rewrite in_app in H4. destruct H4.
    eauto. simpl in H4. destruct H4. subst y. red; intros; subst x. tauto. tauto.
    generalize (assign_variable_incr _ _ _ _ _ _ Heqp). lia.
    auto. auto.
  rewrite app_ass. auto.
Qed. CloseFLemma.

FLemma build_compilenv_sound:
  forall f cenv sz,
  build_compilenv f = (cenv, sz) ->
  list_norepet (map fst (S.fn_vars f)) ->
  cenv_compat cenv (S.fn_vars f) sz /\ cenv_separated cenv (S.fn_vars f).
FProofLemma.
  unfold build_compilenv; intros.
  set (vars1 := S.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  assert (cenv_compat cenv vars2 sz /\ cenv_separated cenv vars2).
    change vars2 with (nil ++ vars2).
    eapply assign_variables_sound.
    eexact H.
    simpl. rewrite app_nil_r. apply permutation_norepet with (map fst vars1); auto.
    apply Permutation_map. auto.
    lia.
    red; intros. contradiction.
    red; intros. contradiction.
  destruct H1 as [A B]. split.
  red; intros. apply A. apply Permutation_in with vars1; auto.
  red; intros. eapply B; eauto; apply Permutation_in with vars1; auto.
Qed. CloseFLemma.

FDefinition cenv_remove := fun (cenv: compilenv) (vars: list (ident * Z)) =>
  fold_right (fun id_lv ce => PTree.remove (fst id_lv) ce) cenv vars.

FLemma cenv_remove_gso:
  forall id vars cenv,
  ~In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = PTree.get id cenv.
FProofLemma.
  induction vars; simpl; intros.
  auto.
  rewrite PTree.gro. apply IHvars. intuition. intuition.
Qed. CloseFLemma.

FLemma cenv_remove_gss:
  forall id vars cenv,
  In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = None.
FProofLemma.
  induction vars; simpl; intros.
  contradiction.
  rewrite PTree.grspec. destruct (PTree.elt_eq id (fst a)). auto.
  destruct H; intuition auto with exfalso.
Qed. CloseFLemma.

FDefinition cenv_mem_separated := fun (cenv: compilenv) (vars: list (ident * Z)) (f: meminj) (sp: block) (m: mem) =>
  forall id sz ofs b delta ofs' k p,
  In (id, sz) vars -> PTree.get id cenv = Some ofs ->
  f b = Some (sp, delta) ->
  Mem.perm m b ofs' k p ->
  ofs <= ofs' + delta < sz + ofs -> False.

FLemma match_env_alloc:
  forall f1 id cenv e sp lo m1 sz m2 b ofs f2,
  match_env f1 (PTree.remove id cenv) e sp lo (Mem.nextblock m1) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_env f2 cenv (PTree.set id (b, sz) e) sp lo (Mem.nextblock m2).
FProofLemma.
  intros until f2; intros ME ALLOC CENV INCR SAME OTHER ENV.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  inv ME; constructor.
(* vars *)
  intros. rewrite PTree.gsspec. destruct (peq id0 id).
  (* the new var *)
  subst id0. rewrite CENV. constructor. econstructor. eauto.
  rewrite Ptrofs.add_commut; rewrite Ptrofs.add_zero; auto.
  (* old vars *)
  generalize (me_vars0 id0). rewrite PTree.gro; auto. intros M; inv M.
  constructor; eauto.
  constructor.
(* low-high *)
  rewrite NEXTBLOCK; extlia.
(* bounded *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inv H. rewrite NEXTBLOCK; extlia.
  exploit me_bounded0; eauto. rewrite NEXTBLOCK; extlia.
(* inv *)
  intros. destruct (eq_block b (Mem.nextblock m1)).
  subst b. rewrite SAME in H; inv H. exists id; exists sz. apply PTree.gss.
  rewrite OTHER in H; auto. exploit me_inv0; eauto.
  intros [id1 [sz1 EQ]]. exists id1; exists sz1. rewrite PTree.gso; auto. congruence.
(* incr *)
  intros. rewrite OTHER in H. eauto. unfold block in *; extlia.
Qed. CloseFLemma.

FLemma match_callstack_alloc_right:
  forall ge f m tm cs tf tm' sp le te cenv,
  match_callstack ge f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.alloc tm 0 (T.fn_stackspace tf) = (tm', sp) ->
  Mem.inject f m tm ->
  match_temps f le te ->
  (forall id, cenv!id = None) ->
  match_callstack ge f m tm'
      (Frame cenv tf S.empty_fenv le te sp (Mem.nextblock m) (Mem.nextblock m) :: cs)
      (Mem.nextblock m) (Mem.nextblock tm').
FProofLemma.
  intros.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  constructor.
  extlia.
  unfold block in *; extlia.
  auto.
  constructor; intros.
    rewrite H3. rewrite PTree.gempty. constructor.
    extlia.
    rewrite PTree.gempty in H4; discriminate.
    eelim Mem.fresh_block_alloc; eauto. eapply Mem.valid_block_inject_2; eauto.
    rewrite RES. change (Mem.valid_block tm tb). eapply Mem.valid_block_inject_2; eauto.
  red; intros. rewrite PTree.gempty in H4. discriminate.
  red; intros. left. eapply Mem.perm_alloc_2; eauto.
  eapply match_callstack_invariant with (tm1 := tm); eauto.
  rewrite RES; auto.
  intros. eapply Mem.perm_alloc_1; eauto.
Qed. CloseFLemma.

FLemma match_callstack_alloc_left:
  forall ge f1 m1 tm id cenv tf e le te sp lo cs sz m2 b f2 ofs,
  match_callstack ge f1 m1 tm
    (Frame (PTree.remove id cenv) tf e le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_callstack ge f2 m2 tm
    (Frame cenv tf (PTree.set id (b, sz) e) le te sp lo (Mem.nextblock m2) :: cs)
    (Mem.nextblock m2) (Mem.nextblock tm).
FProofLemma.
  intros. inv H.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (LO: Ple lo (Mem.nextblock m1)) by (eapply me_low_high; eauto).
  constructor.
  extlia.
  auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_alloc; eauto.
  red; intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inversion H. subst b0 sz0 id0. eapply Mem.perm_alloc_3; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_alloc_4; eauto.
  exploit me_bounded; eauto. unfold block in *; extlia.
  red; intros. exploit PERM; eauto. intros [A|A]. auto. right.
  inv A. apply is_reachable_intro with id0 b0 sz0 delta; auto.
  rewrite PTree.gso. auto. congruence.
  eapply match_callstack_invariant with (m1 := m1); eauto.
  intros. eapply Mem.perm_alloc_4; eauto.
  unfold block in *; extlia.
  intros. apply H4. unfold block in *; extlia.
  intros. destruct (eq_block b0 b).
  subst b0. rewrite H3 in H. inv H. extlia.
  rewrite H4 in H; auto.
Qed. CloseFLemma.

FLemma match_callstack_alloc_variables_rec:
  forall ge tm sp tf cenv le te lo cs,
  Mem.valid_block tm sp ->
  T.fn_stackspace tf <= Ptrofs.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < T.fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < T.fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  S.alloc_variables e1 m1 vars e2 m2 ->
  forall f1,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (T.fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack ge f1 m1 tm
    (Frame (cenv_remove cenv vars) tf e1 le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack ge f2 m2 tm
      (Frame cenv tf e2 le te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject f2 m2 tm.
FProofLemma.
  intros until cs; intros VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
  simpl in MCS. exists f1; auto.
  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject.
    eexact MINJ.
    eexact H.
    eexact VALID.
    instantiate (1 := ofs). zify. lia.
    intros. exploit STKSIZE; eauto. lia.
    intros. apply STKPERMS. zify. lia.
    replace (sz - 0) with sz by lia. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. lia.
  intros [f2 [A [B [C D]]]].
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5.
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    lia.
    eapply SEP2. apply in_cons; eauto. eauto.
    rewrite D in H5; eauto. eauto. auto.
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto.
    rewrite cenv_remove_gso; auto.
    apply UNBOUND with sz; auto with coqlib.
Qed. CloseFLemma.

FLemma match_callstack_alloc_variables:
  forall ge tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (T.fn_stackspace fn) = (tm2, sp) ->
  T.fn_stackspace fn <= Ptrofs.max_unsigned ->
  S.alloc_variables S.empty_fenv m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (T.fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack ge f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack ge f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2.
FProofLemma.
  intros.
  eapply match_callstack_alloc_variables_rec; eauto.
  eapply Mem.valid_new_block; eauto.
  intros. eapply Mem.perm_alloc_3; eauto.
  intros. apply Mem.perm_implies with Freeable; auto with mem. eapply Mem.perm_alloc_2; eauto.
  instantiate (1 := f1). red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto.
  eapply match_callstack_alloc_right; eauto.
  intros. destruct (In_dec peq id (map fst vars)).
  apply cenv_remove_gss; auto.
  rewrite cenv_remove_gso; auto.
  destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto.
  eapply Mem.alloc_right_inject; eauto.
Qed. CloseFLemma.

FLemma assign_variables_domain:
  forall id vars cesz,
  (fst (assign_variables cesz vars))!id <> None ->
  (fst cesz)!id <> None \/ In id (map fst vars).
FProofLemma.
  induction vars; simpl; intros.
  auto.
  exploit IHvars; eauto. unfold assign_variable. destruct a as [id1 sz1].
  destruct cesz as [cenv stksz]. simpl.
  rewrite PTree.gsspec. destruct (peq id id1). auto. tauto.
Qed. CloseFLemma.

FLemma build_compilenv_domain:
  forall f cenv sz id ofs,
  build_compilenv f = (cenv, sz) ->
  cenv!id = Some ofs -> In id (map fst (S.fn_vars f)).
FProofLemma.
  unfold build_compilenv; intros.
  set (vars1 := S.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  generalize (assign_variables_domain id vars2 (PTree.empty Z, 0)).
  rewrite H. simpl. intros. destruct H1. congruence.
  rewrite PTree.gempty in H1. congruence.
  apply Permutation_in with (map fst vars2); auto.
  apply Permutation_map. apply Permutation_sym; auto.
Qed. CloseFLemma.

MetaData set_params'.
Fixpoint set_params' (vl: list val) (il: list ident) (te: T.env) : T.env :=
  match il, vl with
  | i1 :: is, v1 :: vs => set_params' vs is (PTree.set i1 v1 te)
  | i1 :: is, nil => set_params' nil is (PTree.set i1 Vundef te)
  | _, _ => te
  end.
FEnd set_params'.

FLemma bind_parameters_agree_rec:
  forall f vars vals tvals le1 le2 te,
  S.bind_parameters vars vals le1 = Some le2 ->
  Val.inject_list f vals tvals ->
  match_temps f le1 te ->
  match_temps f le2 (set_params' tvals vars te).
FProofLemma.
Opaque PTree.set.
  induction vars; simpl; intros.
  destruct vals; try discriminate. inv H. auto.
  destruct vals; try discriminate. inv H0.
  simpl. eapply IHvars; eauto.
  red; intros. rewrite PTree.gsspec in *. destruct (peq id a).
  inv H0. exists v'; auto.
  apply H1; auto.
Qed. CloseFLemma.

FLemma create_undef_temps_val:
  forall id v temps, (S.create_undef_temps temps)!id = Some v -> In id temps /\ v = Vundef.
FProofLemma.
  induction temps; simpl; intros.
  rewrite PTree.gempty in H. congruence.
  rewrite PTree.gsspec in H. destruct (peq id a).
  split. auto. congruence.
  exploit IHtemps; eauto. tauto.
Qed. CloseFLemma.

FLemma set_params'_outside:
  forall id il vl te, ~In id il -> (set_params' vl il te)!id = te!id.
FProofLemma.
  induction il; simpl; intros. auto.
  destruct vl; rewrite IHil.
  apply PTree.gso. intuition. intuition.
  apply PTree.gso. intuition. intuition.
Qed. CloseFLemma.

FLemma set_params'_inside:
  forall id il vl te1 te2,
  In id il ->
  (set_params' vl il te1)!id = (set_params' vl il te2)!id.
FProofLemma.
  induction il; simpl; intros.
  contradiction.
  destruct vl; destruct (List.in_dec peq id il); auto;
  repeat rewrite set_params'_outside; auto;
  assert (a = id) by intuition; subst a; repeat rewrite PTree.gss; auto.
Qed. CloseFLemma.

FLemma set_params_set_params':
  forall il vl id,
  list_norepet il ->
  (S.set_params vl il)!id = (set_params' vl il (PTree.empty val))!id.
FProofLemma.
  induction il; simpl; intros.
  auto.
  inv H. destruct vl.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
Qed. CloseFLemma.

FLemma set_locals_outside:
  forall e id il,
  ~In id il -> (S.set_locals il e)!id = e!id.
FProofLemma.
  induction il; simpl; intros.
  auto.
  rewrite PTree.gso. apply IHil. tauto. intuition.
Qed. CloseFLemma.

FLemma set_locals_inside:
  forall e id il,
  In id il -> (S.set_locals il e)!id = Some Vundef.
FProofLemma.
  induction il; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss.
  rewrite PTree.gsspec. destruct (peq id a). auto. auto.
Qed. CloseFLemma.

FLemma set_locals_set_params':
  forall vars vals params id,
  list_norepet params ->
  list_disjoint params vars ->
  (S.set_locals vars (S.set_params vals params)) ! id =
  (set_params' vals params (S.set_locals vars (PTree.empty val))) ! id.
FProofLemma.
  intros. destruct (in_dec peq id vars).
  assert (~In id params). apply list_disjoint_notin with vars; auto. apply list_disjoint_sym; auto.
  rewrite set_locals_inside; auto. rewrite set_params'_outside; auto. rewrite set_locals_inside; auto.
  rewrite set_locals_outside; auto. rewrite set_params_set_params'; auto.
  destruct (in_dec peq id params).
  apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto.
  rewrite set_locals_outside; auto.
Qed. CloseFLemma.

FLemma bind_parameters_agree:
  forall f params temps vals tvals le,
  S.bind_parameters params vals (S.create_undef_temps temps) = Some le ->
  Val.inject_list f vals tvals ->
  list_norepet params ->
  list_disjoint params temps ->
  match_temps f le (S.set_locals temps (S.set_params tvals params)).
FProofLemma.
  intros; red; intros.
  exploit bind_parameters_agree_rec; eauto.
  instantiate (1 := S.set_locals temps (PTree.empty val)).
  red; intros. exploit create_undef_temps_val; eauto. intros [A B]. subst v0.
  exists Vundef; split. apply set_locals_inside; auto. auto.
  intros [v' [A B]]. exists v'; split; auto.
  rewrite <- A. apply set_locals_set_params'; auto.
Qed. CloseFLemma.

FLemma match_callstack_function_entry:
  forall ge fn cenv tf m e m' tm tm' sp f cs args targs le,
  build_compilenv fn = (cenv, (T.fn_stackspace tf)) ->
  (T.fn_stackspace tf) <= Ptrofs.max_unsigned ->
  list_norepet (map fst (S.fn_vars fn)) ->
  list_norepet (S.fn_params fn) ->
  list_disjoint (S.fn_params fn) (S.fn_temps fn) ->
  S.alloc_variables S.empty_fenv m (S.fn_vars fn) e m' ->
  S.bind_parameters (S.fn_params fn) args (S.create_undef_temps (S.fn_temps fn)) = Some le ->
  Val.inject_list f args targs ->
  Mem.alloc tm 0 (T.fn_stackspace tf) = (tm', sp) ->
  match_callstack ge f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let te := S.set_locals (S.fn_temps fn) (S.set_params targs (S.fn_params fn)) in
  exists f',
     match_callstack ge f' m' tm'
                     (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f' m' tm'.
FProofLemma.
intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto.
Qed. CloseFLemma.

Require Import Coq.Program.Equality.

FInduction transl_step_correct about S.step motive
  (fun ge S1 t S2 (_: S.step ge S1 t S2) =>
     forall prog tprog tge, match_prog prog tprog ->
     Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
     forall T1, match_states ge S1 T1 ->
     (exists T2, plus T.step tge T1 t T2 /\ match_states ge S2 T2)
     \/ (measure S2 < measure S1 /\ t = E0 /\ match_states ge S2 T1)%nat).
FProof.
all: intros until tge; intros TRANSL A B.

(* Both require dependent induction on MK which Rocqet doesn't support *)
(* skip seq *)
+ apply cheat.
(* skip call *)  
+ apply cheat.
  
(* assign *)  
+ intros T1 MSTATE. inv MSTATE. fsimpl in TR. monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; econstructor; split.
  apply plus_one. fconstructor; eauto.
  econstructor; eauto. fsimpl; reflexivity.
  eapply match_callstack_set_temp; eauto.
  apply cheat. (* fdiscriminate *)
  
(* seq *)  
+ intros T1 MSTATE. inv MSTATE. fsimpl in TR. monadInv TR.
  left; econstructor; split.
  apply plus_one. fconstructor.
  econstructor; eauto.
  constructor; eauto.
  (* seq 2 *)
  right. split. simpl. fsimpl. apply Sseq_injective in H1; destruct H1; subst. auto. split.
  auto. apply Sseq_injective in H1; destruct H1; subst. econstructor; eauto.
  
(* return none *)  
+ intros T1 MSTATE. inv MSTATE. fsimpl in TR. monadInv TR. left.
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply T.step_return_0. eauto.
  econstructor; eauto. eapply match_call_cont; eauto.
  simpl; auto.
  apply cheat. (* fdiscriminate *)
  
(* return some *)  
+ intros T1 MSTATE. inv MSTATE. fsimpl in TR. monadInv TR. left.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply T.step_return_1. eauto. eauto.
  econstructor; eauto. eapply match_call_cont; eauto.
  apply cheat. (* fdiscriminate *)
  
(* label *)  
+ intros T1 MSTATE. inv MSTATE. fsimpl in TR. monadInv TR.
  left; econstructor; split.
  apply plus_one. fconstructor.
  econstructor; eauto.
  apply cheat. (* fdiscriminate *)
  
(* goto *)
+ intros T1 MSTATE; inv MSTATE. fsimpl in TR; monadInv TR.
  exploit transl_find_label_body; eauto.
  intros [ts' [tk' [xenv' [A [B C]]]]].
  left; econstructor; split.
  apply plus_one. apply T.step_goto. eexact A.
  econstructor; eauto.
  apply cheat. (* fdiscriminate *)
  
(* ifthenelse *)  
+ intros T1 MSTATE; inv MSTATE. fsimpl in TR; monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; exists (T.State tfn (if b then x0 else x1) tk sp0 te tm); split.
  apply plus_one. eapply T.step_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
  econstructor; eauto. destruct b; auto.
  apply cheat. (* fdiscriminate *)

(* internal function *)  
+ intros T1 MSTATE; inv MSTATE. fsimpl in TR; monadInv TR. generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Ptrofs.max_unsigned); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := T.mkfunction (S.fn_sig f)
                        (S.fn_params f)
                        (S.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm 0 (T.fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit match_callstack_function_entry; eauto. simpl; eauto. simpl; auto.
  intros [f2 [MCS2 MINJ2]].
  left; econstructor; split.
  apply plus_one. fconstructor; simpl; eauto using Val.has_argtype_list_inject.
  econstructor. eexact TRBODY. eauto. eexact MINJ2. eexact MCS2.
  inv MK; fsimpl in ISCC; contradiction || econstructor; eauto.   
Qed. FEnd transl_step_correct.

FLemma match_globalenvs_init:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall m,
  Genv.init_mem prog = Some m ->
  match_globalenvs ge (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
FProofLemma.
  intros. constructor.
  intros. unfold Mem.flat_inj. apply pred_dec_true; auto.
  intros. unfold Mem.flat_inj in H0. unfold Mem.flat_inj in H3.
  destruct (plt b1 (Mem.nextblock m)). inversion H3. reflexivity. inversion H3.
  rewrite <- H0. intros. eapply Genv.find_symbol_not_fresh; eauto.  
  rewrite <- H0. intros. eapply Genv.find_funct_ptr_not_fresh; eauto.
  rewrite <- H0. intros. eapply Genv.find_var_info_not_fresh; eauto.
Qed. CloseFLemma.

FLemma transl_initial_states:
  forall prog tprog ge tge, match_prog prog tprog ->
  Genv.globalenv prog = ge -> Genv.globalenv tprog = tge ->
  forall S', S.initial_state prog S' ->
  exists R, T.initial_state tprog R /\ match_states ge S' R.
FProofLemma.
 intros until tge; intros TRANSL A B. induction 1. subst.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  apply (Genv.init_mem_transf_partial TRANSL). eauto.
  simpl. (*fold tge.*) rewrite (symbols_preserved prog tprog (Genv.globalenv prog) (Genv.globalenv tprog) TRANSL eq_refl eq_refl).
  replace (AST.prog_main tprog) with (AST.prog_main prog). eexact H0.
  symmetry. unfold transl_program in TRANSL.
  eapply match_program_main; eauto.
  eexact FIND.
  rewrite <- H2. eapply sig_preserved; eauto.
  eapply match_callstate with (f := Mem.flat_inj (Mem.nextblock m0)) (cs := @nil frame) (cenv := PTree.empty Z).
  auto.
  eapply Genv.initmem_inject; eauto.
  apply mcs_nil with (Mem.nextblock m0). eapply match_globalenvs_init; eauto. extlia. extlia.
  constructor. fsimpl; auto.
  constructor.
Qed. CloseFLemma.

FLemma transl_final_states:
  forall ge S' R r,
  match_states ge S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma.
intros. inv H0. inv H. (*inv MK;*) apply match_Kstop_inv in MK; destruct MK; subst. inv RESINJ. constructor.
Qed. CloseFLemma.

FEnd Cminorgen.

FEnd Base.

(* moved to base *)
(*Trait Comp_Float extends Base.

Family Cminorgen.

FRecursion transl_constant.
Case Ofloatconst n := (T.Ofloatconst n).
Case Osingleconst n := (T.Osingleconst n).
FEnd transl_constant.

FEnd Cminorgen.

FEnd Comp_Float. *)                 

Trait Comp_Loops extends Base.

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

(*FInductive match_cont: S.cont -> T.cont -> compilenv -> exit_env -> callstack -> Prop :=
| match_Kblock: forall k tk cenv xenv cs,
    match_cont k tk cenv xenv cs ->
    match_cont (S.Kblock k) (T.Kblock tk) cenv (true :: xenv) cs
| match_Kblock2: forall k tk cenv xenv cs,
    match_cont k tk cenv xenv cs ->
    match_cont k (T.Kblock tk) cenv (false :: xenv) cs.*)

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction match_call_cont.
FProof.
+ apply cheat.
+ apply cheat.
Qed. FEnd match_call_cont. 

FInduction transl_find_label.
FProof.
+ apply cheat.
+ apply cheat.
+ apply cheat.
Qed. FEnd transl_find_label.
  
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

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

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
Case Sbuiltin optid ef el :=
   (fun cenv xenv => 
      do tel <- transl_exprlist cenv el;
      OK (T.Sbuiltin optid ef tel)).
FEnd transl_stmt.

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction transl_find_label.
FProof.
all: intros; fsimpl in H; try (monadInv H); simpl; do 2 fsimpl; auto.
Qed. FEnd transl_find_label.
  
FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Cminorgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

Inherit compilenv.

FDefinition var_addr : compilenv -> ident -> T.expr := fun cenv id =>
  match PTree.get id cenv with
  | Some ofs => T.Econst (T.Oaddrstack (Ptrofs.repr ofs))
  | None => T.Econst (T.Oaddrsymbol id Ptrofs.zero)
  end.

FRecursion transl_expr.
Case Eaddrof id := (fun cenv => OK (var_addr cenv id)).
Case Eload chunk e :=
  (fun cenv => 
     do te <- transl_expr e cenv;
     OK (T.Eload chunk te)).
FEnd transl_expr.

FRecursion transl_stmt.
Case Sstore chunk e1 e2 :=
(fun cenv xenv => 
   do te1 <- transl_expr e1 cenv;
   do te2 <- transl_expr e2 cenv;
   OK (T.Sstore chunk te1 te2)).
FEnd transl_stmt.

FInduction transl_expr_correct.
FProof.
+ apply cheat.
+ apply cheat.
Qed. FEnd transl_expr_correct.

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction transl_find_label.
FProof.
all: intros; fsimpl in H; try (monadInv H); simpl; do 2 fsimpl; auto.
Qed. FEnd transl_find_label.
  
FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Cminorgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family Cminorgen extends Cfamtransl.
Family S extends Csharpminor. FEnd S.
Family T extends Cminor. FEnd T.

FRecursion transl_stmt.
Case Scall optid sig e el :=
  (fun cenv xenv => 
     do te <- transl_expr e cenv;
     do tel <- transl_exprlist cenv el;
   OK (T.Scall optid sig te tel)).
FEnd transl_stmt.

Inherit transl_expr_correct.

(*FInductive match_cont: S.cont -> T.cont -> compilenv -> exit_env -> callstack -> Prop :=
| match_Kcall: forall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv',
   transl_funbody cenv sz fn = OK tfn ->
   match_cont k tk cenv xenv cs ->
   match_cont (S.Kcall optid fn e le k)
      (T.Kcall optid tfn te sp tk)
      cenv' nil
      (Frame cenv tfn le e te sp lo hi :: cs). *)

FRecursion seq_left_depth.
Case _ := O.
FEnd seq_left_depth.

FInduction match_call_cont.
FProof.
+ apply cheat.
Qed. FEnd match_call_cont. 

FInduction transl_find_label.
FProof.
+ apply cheat.
Qed. FEnd transl_find_label.

FInduction transl_step_correct.
FProof.
+ apply cheat.
+ apply cheat.
+ apply cheat.  
Qed. FEnd transl_step_correct. 

FEnd Cminorgen.

FEnd Comp_Call.

From Rocqet Require Import Switch.
Trait Comp_Switch extends Comp_Loops.

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

(* Will be mutual, I think *)
FInduction transl_find_label.
FProof.
+ apply cheat.
Qed. FEnd transl_find_label.

FInduction transl_step_correct.
FProof.
+ apply cheat.
Qed. FEnd transl_step_correct.

FEnd Cminorgen.

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

Family Cminorgen.
Final Family S := Csharpminor.
Final Family T := Cminor.
FEnd Cminorgen.

FEnd Comp.
