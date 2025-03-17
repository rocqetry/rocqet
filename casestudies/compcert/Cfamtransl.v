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

Require Import Cfam.

Trait Base.

Trait Cfamtransl.
Family S extends Cfam. FEnd S.
Family T extends Cfam. FEnd T.

From Rocqet Require Import Errors.
Local Open Scope error_monad_scope.

FOpaque Definition earg : Type := cheat.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => earg -> res T.expr) by _rect.
Case Evar id := (fun _ => OK (T.Evar id)).
FEnd transl_expr.

FOpaque Definition sarg : Type := cheat.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => earg -> sarg -> res T.stmt) by _rect.
Case Sskip := (fun _ _ => OK (T.Sskip)).
Case Sassign id e :=
  (fun earg _ =>
     do te <- transl_expr e earg;
     OK (T.Sassign id te)).
Case Sseq s1 s2 :=
 (fun earg sarg =>
    do ts1 <- transl_stmt s1 earg sarg; 
    do ts2 <- transl_stmt s2 earg sarg; 
    OK (T.Sseq ts1 ts2)).
Case Sreturn expr :=
  (fun earg _ =>
     match expr with
     | None => OK (T.Sreturn None)
     | Some expr =>
          do te <- transl_expr expr earg;
          OK (T.Sreturn (Some te))
     end).
Case Slabel lbl s :=
  (fun earg sarg =>                          
     do ts <- transl_stmt s earg sarg;
     OK (T.Slabel lbl ts)).
Case Sgoto lbl := (fun earg sarg => OK (T.Sgoto lbl)).
FEnd transl_stmt.

FOpaque Definition transl_function : S.function -> res T.function :=
  cheat.

FDefinition transl_fundef : S.fundef -> res T.fundef := fun f =>
   transf_partial_fundef transl_function f.

FDefinition transl_program : S.program -> res T.program := fun p =>
  transform_partial_program transl_fundef p.

FEnd Cfamtransl.

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

FInductive match_cont: S.cont -> T.cont -> compilenv -> exit_env -> callstack -> Prop :=
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

FInduction match_call_cont about match_cont motive
  (fun k tk cenv xenv cs (_ : match_cont k tk cenv xenv cs) =>    
    match_cont k tk cenv xenv cs ->
    match_cont (S.call_cont k) (T.call_cont tk) cenv nil cs).
FProof.
all: intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_call_cont.

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
+ (*fsimpl in H1. monadInv H1. exploit H. eauto. eapply match_Kseq. eexact EQ1. eauto.
  destruct (S.find_label __i lbl (S.Kseq __i0 k)) as [[s' k'] | ].*)  
  (*intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.*)
  apply cheat.
  
+  destruct o; fsimpl in H; monadInv H; fsimpl; auto.
+ (*fsimpl in H0. monadInv H0.
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.*)
  (*eapply H. transl_find_label with xenv; auto.*)
  apply cheat.

  (*TODO*)
+ apply cheat.
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
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0. assumption. 
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
(* skip seq *)
+ (*fsimpl in TR. monadInv TR. left.
  dependent induction MK. apply kstop_not_kseq in x; exfalso; eauto.
  econstructor; split.
  apply plus_one. fconstructor.
  apply kseq_injective in x; destruct x; subst.
  econstructor; eauto. 
  econstructor; split.
  apply kseq_injective in x; destruct x; subst.
  apply plus_one. fconstructor.
    apply kseq_injective in x; destruct x; subst.
    eapply match_state_seq; eauto. *)
  (* other cases of the induction *)
  (*exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.*)
  apply cheat.
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
  fconstructor; eauto.
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
Qed. FEnd transl_step_correct.

FLemma match_globalenvs_init:
  forall (prog: S.program) ge (A : ge = Genv.globalenv prog) m,
  Genv.init_mem prog = Some m ->
  match_globalenvs ge (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
FProofLemma.
  (*intros. constructor.
  intros. unfold Mem.flat_inj. apply pred_dec_true; auto.
  intros. unfold Mem.flat_inj in H0.
  destruct (plt b1 (Mem.nextblock m)); congruence.
  intros. eapply Genv.find_symbol_not_fresh; eauto. apply cheat.
  intros. eapply Genv.find_funct_ptr_not_fresh; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto.*)
apply cheat.
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
  fconstructor. fsimpl; auto.
  constructor.
Qed. CloseFLemma.

FLemma transl_final_states:
  forall ge S' R r,
  match_states ge S' R -> S.final_state S' r -> T.final_state R r.
FProofLemma.
intros. inv H0. inv H. apply match_Kstop_inv in MK; destruct MK; subst. inv RESINJ. constructor.
Qed. CloseFLemma.

FEnd Cminorgen.

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
