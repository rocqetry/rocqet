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
Require Import FunInd.
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

Family C.
FInductive expr : Type :=
| Eval : val -> type -> expr (* constant *)
| Evar : ident -> type -> expr (* variable *)
| Eunop  : Cop.unary_operation -> expr -> type -> expr
| Ebinop : Cop.binary_operation -> expr -> expr -> type -> expr
| Ecast : expr -> type -> expr (* type cast (ty)r *)
| Eseqand : expr -> expr -> type -> expr (* sequential "and" r1 && r2 *)
| Eseqor : expr -> expr -> type -> expr (* sequential "or" r1 || r2 *)
| Econdition : expr -> expr -> expr -> type -> expr (* conditional r1 ? r2 : r3 *)
| Esizeof : type -> type -> expr (* size of a type *)
| Ealignof : type -> type -> expr (* natural alignment of a type *)
| Ecomma : expr -> expr -> type -> expr (* sequence expression r1, r2 *)
| Eparen : expr -> type -> type -> expr
with exprlist : Type :=
| Enil : exprlist
| Econs : expr -> exprlist -> exprlist.

FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect.
Case Eval v ty := ty.
Case Evar x ty := ty.
Case Eunop op e ty := ty.
Case Ebinop op e1 e2 ty := ty.
Case Ecast r ty := ty.
Case Eseqand r1 r2 ty := ty.
Case Eseqor r1 r2 ty := ty.
Case Econdition r1 r2 r3 ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.
Case Ecomma r1 r2 ty := ty.
Case Eparen e ty' ty := ty.
FEnd typeof.

FDefinition label := ident.
FInductive stmt : Type :=
| Sseq : stmt -> stmt -> stmt
| Sskip : stmt
| Sdo : expr -> stmt(* evaluate expression for side effects *)
| Sifthenelse : expr -> stmt -> stmt -> stmt(* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

MetaData function binds fn_return, fn_callconv, fn_params, fn_vars, fn_body.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: stmt
}.
FEnd function.

FDefinition var_names := fun (vars: list(ident * type)) =>
  List.map (@fst ident type) vars.

FDefinition fundef := Ctypes.fundef function.

FDefinition type_of_function : function -> type := fun f =>
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f =>
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

FRecursion seq_of_labeled_statement about lbl_stmts
  motive (fun (_ : lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons i s sl' := (Sseq s (seq_of_labeled_statement sl')).
FEnd seq_of_labeled_statement.

(* Semantics *)
MetaData genv binds genv_genv, genv_cenv.
Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.
FEnd genv.

FDefinition globalenv : program -> genv := fun p =>
  {| self__C.genv_genv := Genv.globalenv p; self__C.genv_cenv := p.(prog_comp_env) |}.

FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z) := fun ge e =>
    List.map (block_of_binding ge) (PTree.elements e).

MetaData assign_loc.
Inductive assign_loc (ge : genv) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                              bitfield -> val -> trace -> mem -> val -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ge ty m b ofs Full v E0 m' v
  | assign_loc_volatile: forall v chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store (genv_genv ge) chunk m b ofs v t m' ->
      assign_loc ge ty m b ofs Full v t m' v
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (alignof_blockcopy (genv_cenv ge) ty | Ptrofs.unsigned ofs') ->
      (alignof_blockcopy (genv_cenv ge) ty | Ptrofs.unsigned ofs) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof (genv_cenv ge) ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof (genv_cenv ge) ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof (genv_cenv ge) ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ge ty m b ofs Full (Vptr b' ofs') E0 m' (Vptr b' ofs')
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ge ty m b ofs (Bits sz sg pos width) v E0 m' v'.
FEnd assign_loc.

MetaData alloc_variables.
Inductive alloc_variables (ge : genv) : env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables ge e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof (genv_cenv ge) ty) = (m1, b1) ->
      alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables ge e m ((id, ty) :: vars) e2 m2.
FEnd alloc_variables.

MetaData bind_parameters.
Inductive bind_parameters (ge : genv) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ge e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl v1' b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m b Ptrofs.zero Full v1 E0 m1 v1' ->
      bind_parameters ge e m1 params vl m2 ->
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2.
FEnd bind_parameters.

FInductive cont: Type :=
| Kstop: cont
| Kdo: cont -> cont(* Kdo k = after x in x; *)
| Kseq: stmt -> cont -> cont(* Kseq s2 k = after s1 in s1;s2 *)
| Kifthenelse: stmt -> stmt -> cont -> cont(* Kifthenelse s1 s2 k = after x in if (x) { s1 } else { s2 } *)
| Kreturn: cont -> cont. (* Kreturn k = after e in return e; *)

FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kdo k := k.
Case Kseq s k := (call_cont k).
Case Kifthenelse s1 s2 k := (call_cont k).
Case Kreturn k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.
Case Kstop := True.
Case Kdo k := False.
Case Kseq s k := False.
Case Kifthenelse s1 s2 k := False.
Case Kreturn k := False.
FEnd is_call_cont.

MetaData state binds State, ExprState, Callstate, Returnstate, Stuckstate.
Inductive state: Type :=
| State(* execution of a stmt *)
    (f: function) (s: stmt)
    (k: cont) (e: env) (m: mem) : state
| ExprState(* reduction of an expression *)
    (f: function) (r: expr)
    (k: cont) (e: env) (m: mem) : state
| Callstate(* calling a function *)
    (fd: fundef) (args: list val)
    (k: cont) (m: mem) : state
| Returnstate(* returning from a function *)
    (res: val) (k: cont) (m: mem) : state
| Stuckstate. (* undefined behavior occurred *)
FEnd state.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont))
  with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sskip := (fun lbl k => None).
Case Sseq s1 s2 :=
  (fun lbl k =>
     match find_label s1 lbl (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sdo r := (fun lbl k => None).
Case Sifthenelse a s1 s2 :=
  (fun lbl k =>
      match find_label s1 lbl k with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sreturn a := (fun lbl k => None).
Case Slabel lbl' s' := (fun lbl k => if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sgoto lbl' := (fun lbl k => None).

Case LSnil := (fun lbl k => None).
Case LScons i s sl' :=
  (fun lbl k =>
    match find_label s lbl (Kseq (seq_of_labeled_statement sl') k) with
    | Some sk => Some sk
    | None => find_label_ls sl' lbl k
    end).
FEnd find_label with find_label_ls.

(* deterministic evaluation strategy *)

FRecursion simple about expr motive (fun (_ : expr) => bool) by _rec.
Case Eval v ty := true.
Case Evar x ty := true.
Case Eunop op e ty := (simple e).
Case Ebinop op e1 e2 ty := (simple e1 && simple e2).
Case Ecast r ty := (simple r).
Case Esizeof ty' ty := true.
Case Ealignof ty' ty := true.
Case _ := false.
FEnd simple.

FRecursion simplelist about exprlist motive (fun (_ : exprlist) => bool) by _rec.
Case Enil := true.
Case Econs e el := (simple e && simplelist el).
FEnd simplelist.

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
| esr_val: forall ge e m v ty,
    eval_simple_rvalue ge e m (Eval v ty) v
| esr_unop: forall ge e m op r1 ty v1 v,
    eval_simple_rvalue ge e m r1 v1 ->
    sem_unary_operation op v1 (typeof r1) m = Some v ->
    eval_simple_rvalue ge e m (Eunop op r1 ty) v
| esr_binop: forall ge e m op r1 r2 ty v1 v2 v,
    eval_simple_rvalue ge e m r1 v1 -> eval_simple_rvalue ge e m r2 v2 ->
    sem_binary_operation (genv_cenv ge) op v1 (typeof r1) v2 (typeof r2) m = Some v ->
    eval_simple_rvalue ge e m (Ebinop op r1 r2 ty) v
| esr_cast: forall ge e m ty r1 v1 v,
    eval_simple_rvalue ge e m r1 v1 ->
    Cop.sem_cast v1 (typeof r1) ty m = Some v ->
    eval_simple_rvalue ge e m (Ecast r1 ty) v
| esr_sizeof: forall ge e m ty1 ty,
    eval_simple_rvalue ge e m (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.sizeof (genv_cenv ge) ty1)))
| esr_alignof: forall ge e m ty1 ty,
    eval_simple_rvalue ge e m (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.alignof (genv_cenv ge) ty1))).

FDefinition is_val : expr -> Prop := fun e => exists v ty, e = Eval v ty.

MetaData kind binds LV, RV.
Inductive kind : Type := LV | RV.
FEnd kind.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_top: forall k,
    leftcontext k k (fun x => x)
| lctx_unop: forall k C op ty,
    leftcontext k RV C -> leftcontext k RV (fun x => Eunop op (C x) ty)
| lctx_binop_left: forall k C op e2 ty,
    leftcontext k RV C -> leftcontext k RV (fun x => Ebinop op (C x) e2 ty)
| lctx_binop_right: forall k C op e1 ty,
    simple e1 = true -> leftcontext k RV C ->
    leftcontext k RV (fun x => Ebinop op e1 (C x) ty)
| lctx_cast: forall k F ty,
    leftcontext k RV F -> leftcontext k RV (fun x => Ecast (F x) ty)
| lctx_seqand: forall k F r2 ty,
    leftcontext k RV F -> leftcontext k RV (fun x => Eseqand (F x) r2 ty)
| lctx_seqor: forall k F r2 ty,
    leftcontext k RV F -> leftcontext k RV (fun x => Eseqor (F x) r2 ty)
| lctx_condition: forall k F r2 r3 ty,
    leftcontext k RV F -> leftcontext k RV (fun x => Econdition (F x) r2 r3 ty)
| lctx_comma: forall k F e2 ty,
    leftcontext k RV F -> leftcontext k RV (fun x => Ecomma (F x) e2 ty)
| lctx_paren: forall k F tycast ty,
    leftcontext k RV F -> leftcontext k RV (fun x => Eparen (F x) tycast ty)

with leftcontextlist: kind -> (expr -> exprlist) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k RV C -> leftcontextlist k (fun x => Econs (C x) el)
  | lctx_list_tail: forall k C e1,
      simple e1 = true -> leftcontextlist k C ->
      leftcontextlist k (fun x => Econs e1 (C x)).

Closing Fact leftcontext_val_top :
  forall r v ty c k1 k2,
  c r = Eval v ty ->
  leftcontext k1 k2 c ->
  c = (fun x => x)
  by {intros *; intros H1 H2; inv H2; try discriminate; auto}.

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_expr: forall ge f r k e m v ty,
    eval_simple_rvalue ge e m r v ->
    ~ is_val r ->
    ty = typeof r ->
    estep ge (ExprState f r k e m)
      E0 (ExprState f (Eval v ty) k e m)

| step_seqand_true: forall ge f F r1 r2 ty k e m v,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some true ->
    estep ge (ExprState f (F (Eseqand r1 r2 ty)) k e m)
      E0 (ExprState f (F (Eparen r2 type_bool ty)) k e m)
| step_seqand_false: forall ge f F r1 r2 ty k e m v,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some false ->
    estep ge (ExprState f (F (Eseqand r1 r2 ty)) k e m)
      E0 (ExprState f (F (Eval (Vint Int.zero) ty)) k e m)

| step_seqor_true: forall ge f F r1 r2 ty k e m v,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some true ->
    estep ge (ExprState f (F (Eseqor r1 r2 ty)) k e m)
      E0 (ExprState f (F (Eval (Vint Int.one) ty)) k e m)
| step_seqor_false: forall ge f F r1 r2 ty k e m v,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some false ->
    estep ge (ExprState f (F (Eseqor r1 r2 ty)) k e m)
      E0 (ExprState f (F (Eparen r2 type_bool ty)) k e m)

| step_condition: forall ge f F r1 r2 r3 ty k e m v b,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some b ->
    estep ge (ExprState f (F (Econdition r1 r2 r3 ty)) k e m)
      E0 (ExprState f (F (Eparen (if b then r2 else r3) ty ty)) k e m)

| step_comma: forall ge f F r1 r2 ty k e m v,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r1 v ->
    ty = typeof r2 ->
    estep ge (ExprState f (F (Ecomma r1 r2 ty)) k e m)
      E0 (ExprState f (F r2) k e m)

| step_paren: forall ge f F r tycast ty k e m v1 v,
    leftcontext RV RV F ->
    eval_simple_rvalue ge e m r v1 ->
    sem_cast v1 (typeof r) tycast m = Some v ->
    estep ge (ExprState f (F (Eparen r tycast ty)) k e m)
      E0 (ExprState f (F (Eval v ty)) k e m).

FInductive sstep: genv -> state -> trace -> state -> Prop :=
| step_do_1: forall ge f x k e m,
    sstep ge (State f (Sdo x) k e m)
      E0 (ExprState f x (Kdo k) e m)
| step_do_2: forall ge f v ty k e m,
    sstep ge (ExprState f (Eval v ty) (Kdo k) e m)
      E0 (State f Sskip k e m)

| step_seq: forall ge f s1 s2 k e m,
    sstep ge (State f (Sseq s1 s2) k e m)
      E0 (State f s1 (Kseq s2 k) e m)
| step_skip_seq: forall ge f s k e m,
    sstep ge (State f Sskip (Kseq s k) e m)
      E0 (State f s k e m)

| step_ifthenelse_1: forall ge f a s1 s2 k e m,
    sstep ge (State f (Sifthenelse a s1 s2) k e m)
      E0 (ExprState f a (Kifthenelse s1 s2 k) e m)
| step_ifthenelse_2: forall ge f v ty s1 s2 k e m b,
    Cop.bool_val v ty m = Some b ->
    sstep ge (ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m)
      E0 (State f (if b then s1 else s2) k e m)

| step_return_0: forall ge f k e m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    sstep ge (State f (Sreturn None) k e m)
      E0 (Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f x k e m,
      sstep ge (State f (Sreturn (Some x)) k e m)
        E0 (ExprState f x (Kreturn k) e m)
| step_return_2: forall ge f v1 ty k e m v2 m',
      Cop.sem_cast v1 ty (fn_return f) m = Some v2 ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      sstep ge (ExprState f (Eval v1 ty) (Kreturn k) e m)
        E0 (Returnstate v2 (call_cont k) m')
| step_skip_call: forall ge f k e m m',
   is_call_cont k ->
   Mem.free_list m (blocks_of_env ge e) = Some m' ->
   sstep ge (State f Sskip k e m)
     E0 (Returnstate Vundef k m')

| step_label: forall ge f lbl s k e m,
      sstep ge (State f (Slabel lbl s) k e m)
         E0 (State f s k e m)

| step_goto: forall ge f lbl k e m s' k',
    find_label (fn_body f) lbl (call_cont k) = Some (s', k') ->
    sstep ge (State f (Sgoto lbl) k e m)
       E0 (State f s' k' e m)

| step_internal_function: forall ge f vargs k m e m1 m2,
   list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
   alloc_variables ge empty_env m ((fn_params f) ++ (fn_vars f)) e m1 ->
   bind_parameters ge e m1 (fn_params f) vargs m2 ->
   sstep ge (Callstate (Internal f) vargs k m)
      E0 (State f (fn_body f) k e m2).

FDefinition step : genv -> state -> trace -> state -> Prop := fun ge S t S' =>
  estep ge S t S' \/ sstep ge S t S'.

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol (genv_genv ge) p.(prog_main) = Some b ->
      Genv.find_funct_ptr (genv_genv ge) b = Some f ->
      type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.
FEnd final_state.

FEnd C.


Family Clight.
FInductive expr : Type :=
| Econst_int: int -> type -> expr(* integer literal *)
| Econst_float: float -> type -> expr(* double float literal *)
| Econst_single: float32 -> type -> expr(* single float literal *)
| Econst_long: int64 -> type -> expr(* long integer literal *)
| Etempvar: ident -> type -> expr (* temporary variable *)
| Eunop: Cop.unary_operation -> expr -> type -> expr (* unary operation *)
| Ebinop: Cop.binary_operation -> expr -> expr -> type -> expr (* binary operation *)
| Ecast: expr -> type -> expr
| Esizeof: type -> type -> expr (* size of a type *)
| Ealignof: type -> type -> expr (* alignment of a type *)
.


FRecursion typeof about expr motive (fun (_ : expr) => type) by _rect.
Case Econst_int i ty := ty.
Case Econst_float f ty := ty.
Case Econst_single s ty := ty.
Case Econst_long l ty := ty.
Case Etempvar v ty := ty.
Case Esizeof ty' ty := ty.
Case Ealignof ty' ty := ty.
Case Ecast e ty := ty.
Case Eunop op e ty := ty.
Case Ebinop op e0 e1 ty := ty.
FEnd typeof.

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip : stmt (* do nothing *)
| Sset : ident -> expr -> stmt (* assignment tempvar = rvalue *)
| Sseq : stmt -> stmt -> stmt (* sequence *)
| Sifthenelse : expr -> stmt -> stmt -> stmt (* conditional *)
| Sreturn : option expr -> stmt (* return statement *)
| Slabel : label -> stmt -> stmt
| Sgoto : label -> stmt
with lbl_stmts : Type :=(* cases of a switch *)
| LSnil: lbl_stmts
| LScons: option Z -> stmt -> lbl_stmts -> lbl_stmts.

MetaData function binds fn_return, fn_callconv, fn_params, fn_vars, fn_body.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: stmt
}.
FEnd function.

FDefinition var_names := fun (vars: list(ident * type)) =>
  List.map (@fst ident type) vars.

FDefinition fundef := Ctypes.fundef function.

FDefinition type_of_function : function -> type := fun f =>
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

FDefinition type_of_fundef : fundef -> type := fun f =>
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

FDefinition program := Ctypes.program function.

FRecursion seq_of_labeled_statement about lbl_stmts
  motive (fun (_ : lbl_stmts) => stmt) by _rect.
Case LSnil := Sskip.
Case LScons i s sl' := (Sseq s (seq_of_labeled_statement sl')).
FEnd seq_of_labeled_statement.

(* Semantics *)

MetaData genv binds genv_genv, genv_cenv.
Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.
FEnd genv.
FDefinition globalenv : program -> genv := fun p =>
  {| self__Clight.genv_genv := Genv.globalenv p; self__Clight.genv_cenv := p.(prog_comp_env) |}.


FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).
FDefinition temp_env := PTree.t val.

MetaData assign_loc.
Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                                            bitfield -> val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs Full v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs Full (Vptr b' ofs') m'
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ce ty m b ofs (Bits sz sg pos width) v m'.
FEnd assign_loc.

MetaData alloc_variables.
Inductive alloc_variables (ge : genv) : env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables ge e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof (genv_cenv ge) ty) = (m1, b1) ->
      alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables ge e m ((id, ty) :: vars) e2 m2.
FEnd alloc_variables.

MetaData bind_parameters.
Inductive bind_parameters (ge : genv) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ge e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc (genv_cenv ge) ty m b Ptrofs.zero Full v1 m1 ->
      bind_parameters ge e m1 params vl m2 ->
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2.
FEnd bind_parameters.

FInductive eval_expr : genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Econst_int: forall ge e le m i ty,
    eval_expr ge e le m (Econst_int i ty) (Vint i)
| eval_Econst_float: forall ge e le m f ty,
    eval_expr ge e le m (Econst_float f ty) (Vfloat f)
| eval_Econst_single: forall ge e le m f ty,
    eval_expr ge e le m (Econst_single f ty) (Vsingle f)
| eval_Econst_long: forall ge e le m i ty,
    eval_expr ge e le m (Econst_long i ty) (Vlong i)
| eval_Eunop:  forall ge e le m op a ty v1 v,
    eval_expr ge e le m a v1 ->
    sem_unary_operation op v1 (typeof a) m = Some v ->
    eval_expr ge e le m (Eunop op a ty) v
| eval_Ebinop: forall ge e le m op a1 a2 ty v1 v2 v,
    eval_expr ge e le m a1 v1 ->
    eval_expr ge e le m a2 v2 ->
    sem_binary_operation (genv_cenv ge) op v1 (typeof a1) v2 (typeof a2) m = Some v ->
    eval_expr ge e le m (Ebinop op a1 a2 ty) v
| eval_Ecast: forall ge e le m a ty v1 v,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v ->
    eval_expr ge e le m (Ecast a ty) v
| eval_Etempvar: forall ge e le m id ty v,
    PTree.get id le = Some v ->
    eval_expr ge e le m (Etempvar id ty) v
| eval_Esizeof: forall ge e le m ty1 ty,
    eval_expr ge e le m (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.sizeof (genv_cenv ge) ty1)))
| eval_Ealignof: forall ge e le m ty1 ty,
    eval_expr ge e le m (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.alignof (genv_cenv ge) ty1))).

FInductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont. (* Kseq s2 k = after s1 in s1;s2 *)

FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.
Case Kstop := Kstop.
Case Kseq s k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont about cont motive (fun (c : cont) => Prop) by _rect.
Case Kstop := True.
Case Kseq s k := False.
FEnd is_call_cont.

FRecursion find_label about stmt motive (fun (_ : stmt) => label -> cont -> option (stmt * cont))
  with find_label_ls about lbl_stmts motive (fun (_ : lbl_stmts) => label -> cont -> option (stmt * cont)) by _rect.
Case Sskip := (fun lbl k => None).
Case Sset id e := (fun lbl k => None).
Case Sseq s1 s2 :=
  (fun lbl k =>
    match find_label s1 lbl (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label s2 lbl k
    end).
Case Sifthenelse a s1 s2 :=
 (fun lbl k =>
     match find_label s1 lbl k with
      | Some sk => Some sk
      | None => find_label s2 lbl k
      end).
Case Sreturn a := (fun lbl k => None).
Case Slabel lbl' s' :=
  (fun lbl k =>  if ident_eq lbl lbl' then Some(s', k) else find_label s' lbl k).
Case Sgoto lbl' :=  (fun lbl k => None).

Case LSnil := (fun lbl k => None).
Case LScons i s sl' :=
  (fun lbl k =>
    match find_label s lbl (Kseq (seq_of_labeled_statement sl') k) with
    | Some sk => Some sk
    | None => find_label_ls sl' lbl k
    end).
FEnd find_label with find_label_ls.

MetaData state binds State, Callstate, Returnstate.
Inductive state: Type :=
  | State
      (f: function)
      (s: stmt)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) : state.
FEnd state.

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z)  := fun ge e =>
  List.map (block_of_binding ge) (PTree.elements e).

(* To be overriden in SimplExpr & Cshmgen *)
FOpaque Definition function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop := cheat.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
  step ge (State f Sskip (Kseq s k) e le m)
    E0 (State f s k e le m)
| step_set: forall ge f id a k e le m v,
  eval_expr ge e le m a v ->
  step ge (State f (Sset id a) k e le m)
    E0 (State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
  step ge (State f (Sseq s1 s2) k e le m)
    E0 (State f s1 (Kseq s2 k) e le m)
| step_ifthenelse: forall ge f a s1 s2 k e le m v1 b,
    eval_expr ge e le m a v1 ->
    Cop.bool_val v1 (typeof a) m = Some b ->
    step ge (State f (Sifthenelse a s1 s2) k e le m)
      E0 (State f (if b then s1 else s2) k e le m)
| step_return_0: forall ge f k e le m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (State f (Sreturn None) k e le m)
      E0 (Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f a k e le m v v' m',
    eval_expr ge e le m a v ->
    Cop.sem_cast v (typeof a) (fn_return f) m = Some v' ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (State f (Sreturn (Some a)) k e le m)
      E0 (Returnstate v' (call_cont k) m')
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (State f Sskip k e le m)
      E0 (Returnstate Vundef k m')
| step_label: forall ge f lbl s k e le m,
  step ge (State f (Slabel lbl s) k e le m)
    E0 (State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
  find_label (fn_body f) lbl (call_cont k) = Some (s', k') ->
  step ge (State f (Sgoto lbl) k e le m)
    E0 (State f s' k' e le m)
| step_internal_function: forall ge f vargs k m e le m1,
      function_entry ge f vargs m e le m1 ->
      step ge (Callstate (Internal f) vargs k m)
        E0 (State f (fn_body f) k e le m1).

MetaData initial_state.
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.
FEnd final_state.

FEnd Clight.

(* C -> Clight *)
Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight.
  Inherit temp_env.

  FDefinition create_undef_temps := fix rec (temps: list (ident * type)): temp_env :=
    match temps with
    | nil => PTree.empty val
    | (id, t) :: temps' => PTree.set id Vundef (rec temps')
    end.

  Inherit alloc_variables.
  Inherit bind_parameters.

  MetaData function_entry1.
  Inductive function_entry1 (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry1_intro: forall m1,
      list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
      alloc_variables ge empty_env m ((fn_params f) ++ (fn_vars f)) e m1 ->
      bind_parameters ge e m1 (fn_params f) vargs m' ->
      le = create_undef_temps (fn_temps f) ->
      function_entry1 ge f vargs m e le m'.
  FEnd function_entry1.
  FOverride Definition function_entry := function_entry1.
FEnd T.

Local Open Scope gensym_monad_scope.

MetaData makeseq_rec.
Fixpoint makeseq_rec (s: T.stmt) (l: list T.stmt) : T.stmt :=
   match l with
   | nil => s
   | s' :: l' => makeseq_rec (T.Sseq s s') l'
    end.
FEnd makeseq_rec.

FDefinition makeseq : list T.stmt -> T.stmt := fun l =>
  makeseq_rec T.Sskip l.

MetaData set_destination binds SDbase, SDcons.
Inductive set_destination : Type :=
| SDbase (tycast ty: type) (tmp: ident)
| SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).
FEnd set_destination.

MetaData destination binds For_val, For_effects, For_set.
Inductive destination : Type :=
| For_val
| For_effects
| For_set (sd: set_destination).
FEnd destination.

MetaData do_set.
Fixpoint do_set (sd: set_destination) (a: T.expr) : list T.stmt :=
    match sd with
    | SDbase tycast ty tmp => T.Sset tmp (T.Ecast a tycast) :: nil
    | SDcons tycast ty tmp sd' => T.Sset tmp (T.Ecast a tycast) :: do_set sd' (T.Etempvar tmp ty)
    end.
FEnd do_set.

FDefinition finish := fun (dst: destination) (sl: list T.stmt) (a: T.expr) =>
  match dst with
  | self__SimplExpr.For_val => (sl, a)
  | self__SimplExpr.For_effects => (sl, a)
  | self__SimplExpr.For_set sd => (sl ++ do_set sd a, a)
  end.

FDefinition sd_temp := fun (sd: set_destination) =>
  match sd with self__SimplExpr.SDbase _ _ tmp => tmp | self__SimplExpr.SDcons _ _ tmp _ => tmp end.

FDefinition sd_head_type := fun (sd: set_destination) =>
  match sd with self__SimplExpr.SDbase _ ty _ => ty | self__SimplExpr.SDcons _ ty _ _ => ty end.

FDefinition temp_for_sd : type -> set_destination -> mon ident := fun ty sd =>
  if type_eq ty (sd_head_type sd) then ret (sd_temp sd) else gensym ty.

FDefinition dummy_expr := T.Econst_int Int.zero type_int32s.

FRecursion eval_simpl_expr about T.expr motive (fun (_ : T.expr) => option val) by _rect.
Case Econst_float n ty := (Some(Vfloat n)).
Case Econst_int n ty := (Some(Vint n)).
Case Econst_single n ty := (Some(Vsingle n)).
Case Econst_long n ty := (Some(Vlong n)).
Case Ecast b ty :=
  (match eval_simpl_expr b with
    | None => None
    | Some v => Cop.sem_cast v (T.typeof b) ty Mem.empty
    end).
Case Etempvar id ty := None.
Case Esizeof ty' ty := None.
Case Ealignof ty' ty := None.
Case _ := None.
FEnd eval_simpl_expr.

MetaData makeif.
Function makeif (a: T.expr) (s1 s2: T.stmt) : T.stmt :=
  match eval_simpl_expr a with
  | Some v =>
      match Cop.bool_val v (T.typeof a) Mem.empty with
      | Some b => if b then s1 else s2
      | None => T.Sifthenelse a s1 s2
      end
  | None => T.Sifthenelse a s1 s2
  end.
FEnd makeif.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => composite_env -> destination -> mon (list T.stmt * T.expr))
      with transl_exprlist about S.exprlist motive (fun (_ : S.exprlist) => composite_env -> mon (list T.stmt * list T.expr)) by _rect.
Case Evar id ty := (fun ce dst => ret (finish dst nil (T.Etempvar id ty))).
Case Eval v ty :=
  (fun ce dst =>
    match v with
    | Vint n => ret (finish dst nil (T.Econst_int n ty))
    | Vlong n =>  ret (finish dst nil (T.Econst_long n ty))
    | Vfloat n => ret (finish dst nil (T.Econst_float n ty))
    | Vsingle n => ret (finish dst nil (T.Econst_single n ty))
    | _ => error (msg "SimplExpr.transl_expr: Eval") end).
Case Ecast r1 ty :=
  (fun ce dst =>
      match dst with
      | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
          do (sl1, a1) <- transl_expr r1 ce For_val;
          ret (finish dst sl1 (T.Ecast a1 ty))
      | self__SimplExpr.For_effects =>
          transl_expr r1 ce For_effects end).
Case Ecomma r1 r2 ty :=
   (fun ce dst =>
      do (sl1, a1) <- transl_expr r1 ce For_effects;
      do (sl2, a2) <- transl_expr r2 ce dst;
      ret (sl1 ++ sl2, a2)).
Case Econdition r1 r2 r3 ty :=
  (fun ce dst =>
      do (sl1, a1) <- transl_expr r1 ce For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := SDbase ty ty t in
          do (sl2, a2) <- transl_expr r2 ce (For_set sd);
          do (sl3, a3) <- transl_expr r3 ce (For_set sd);
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce For_effects;
          do (sl3, a3) <- transl_expr r3 ce For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := SDcons ty ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (For_set sd');
          do (sl3, a3) <- transl_expr r3 ce (For_set sd');
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      end).
Case Eseqor r1 r2 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 ce (For_set sd);
          ret (sl1 ++
               makeif a1 (T.Sset t (T.Econst_int Int.one ty)) (makeseq sl2) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce For_effects;
          ret (sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq (do_set sd (T.Econst_int Int.one ty))) (makeseq sl2) :: nil,
               dummy_expr)
      end).
Case Eseqand r1 r2 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 ce (For_set sd);
          ret (sl1 ++
               makeif a1 (makeseq sl2) (T.Sset t (T.Econst_int Int.zero ty)) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (T.Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      end).
Case Esizeof ty' ty := (fun ce dst => ret (finish dst nil (T.Esizeof ty' ty))).
Case Ealignof ty' ty := (fun ce dst => ret (finish dst nil (T.Ealignof ty' ty))).
Case Eparen e tycast ty := (fun ce dst => error (msg "SimplExpr.transl_expr: paren")).
Case Eunop op r1 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce For_val;
    ret (finish dst sl1 (T.Eunop op a1 ty))).
Case Ebinop op r1 r2 ty :=
  (fun ce dst =>
     do (sl1, a1) <- transl_expr r1 ce For_val;
     do (sl2, a2) <- transl_expr r2 ce For_val;
     ret (finish dst (sl1 ++ sl2) (T.Ebinop op a1 a2 ty))).

Case Enil := (fun ce => ret (nil, nil)).
Case Econs r1 rl2 :=
  (fun ce =>
     do (sl1, a1) <- transl_expr r1 ce For_val;
     do (sl2, al2) <- transl_exprlist rl2 ce;
      ret (sl1 ++ sl2, a1 :: al2)).
FEnd transl_expr with transl_exprlist.

FDefinition transl_expression : S.expr -> composite_env -> mon (T.stmt * T.expr) := fun r ce =>
  do (sl, a) <- transl_expr r ce For_val; ret (makeseq sl, a).

FDefinition transl_expr_stmt : S.expr -> composite_env -> mon T.stmt := fun r ce =>
  do (sl, a) <- transl_expr r ce For_effects; ret (makeseq sl).

FDefinition transl_if : S.expr -> T.stmt -> T.stmt -> composite_env -> mon T.stmt  := fun r s1 s2 ce =>
  do (sl, a) <- transl_expr r ce For_val;
  ret (makeseq (sl ++ makeif a s1 s2 :: nil)).

Closing Fact is_Sskip:
  forall s, {s = S.Sskip} + {s <> S.Sskip} by {  destruct s; ((left; reflexivity) || (right; congruence)) }.

FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => composite_env -> mon T.stmt)
       with transl_lblstmt about S.lbl_stmts motive (fun (_ : S.lbl_stmts) => composite_env -> mon T.lbl_stmts) by _rect.
Case Sskip := (fun ce => ret T.Sskip).
Case Sdo e := (fun ce => transl_expr_stmt e ce).
Case Sseq s1 s2 :=
  (fun ce =>
     do ts1 <- transl_stmt s1 ce;
     do ts2 <- transl_stmt s2 ce;
     ret (T.Sseq ts1 ts2)).
Case Sifthenelse e s1 s2 :=
  (fun ce =>
     do ts1 <- transl_stmt s1 ce;
     do ts2 <- transl_stmt s2 ce;
     do (s', a) <- transl_expression e ce;
     if is_Sskip s1 && is_Sskip s2 then
       ret (T.Sseq s' T.Sskip)
     else
       ret (T.Sseq s' (T.Sifthenelse a ts1 ts2))).
Case Sreturn e :=
  (fun ce =>
    match e with
    | None => ret (T.Sreturn None)
    | Some e =>
        do (s', a) <- transl_expression e ce;
        ret (T.Sseq s' (T.Sreturn (Some a)))
    end).
Case Slabel lbl s1 :=
  (fun ce =>
     do ts1 <- transl_stmt s1 ce;
     ret (T.Slabel lbl ts1)).
Case Sgoto lbl := (fun ce => ret (T.Sgoto lbl)).

Case LSnil := (fun ce => ret T.LSnil).
Case LScons c s ls1 :=
  (fun ce =>
      do ts <- transl_stmt s ce;
      do tls1 <- transl_lblstmt ls1 ce;
      ret (T.LScons c ts tls1)).
FEnd transl_stmt with transl_lblstmt.

FDefinition transl_function : S.function -> composite_env -> res T.function := fun f ce =>
  match transl_stmt (S.fn_body f) ce (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody g i =>
      OK (T.mkfunction
              (S.fn_return f)
              (S.fn_callconv f)
              (S.fn_params f)
              (S.fn_vars f)
              g.(gen_trail)
              tbody)
  end.

Local Open Scope error_monad_scope.

FDefinition transl_fundef : composite_env -> S.fundef -> res T.fundef := fun ce fd =>
    match fd with
    | Internal f =>
        do tf <- transl_function f ce; OK (Internal tf)
    | External ef targs tres cc =>
      OK (External ef targs tres cc)
    end.

FDefinition transl_program : S.program -> res T.program := fun p =>
  do p1 <- AST.transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.

(* Relational specification of translation *)
FDefinition final : destination -> T.expr -> list T.stmt := fun dst a =>
match dst with
| self__SimplExpr.For_val => nil
| self__SimplExpr.For_effects => nil
| self__SimplExpr.For_set sd => do_set sd a
end.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_val_effect: forall ce le v ty any tmp,
    tr_expr ce le For_effects (S.Eval v ty) nil any tmp
| tr_val_value: forall ce le v ty a tmp,
    T.typeof a = ty ->
    (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      T.eval_expr tge e le' m a v) ->
    tr_expr ce le For_val (S.Eval v ty) nil a tmp
| tr_val_set: forall ce le sd v ty a any tmp,
    T.typeof a = ty ->
    (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      T.eval_expr tge e le' m a v) ->
    tr_expr ce le (For_set sd) (S.Eval v ty)
                (do_set sd a) any tmp
| tr_sizeof: forall ce le dst ty' ty tmp,
    tr_expr ce le dst (S.Esizeof ty' ty)
        (final dst (T.Esizeof ty' ty))
        (T.Esizeof ty' ty) tmp
| tr_alignof: forall ce le dst ty' ty tmp,
    tr_expr ce le dst (S.Ealignof ty' ty)
        (final dst (T.Ealignof ty' ty))
        (T.Ealignof ty' ty) tmp
| tr_unop: forall ce le dst op e1 ty tmp sl1 a1,
    tr_expr ce le For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Eunop op e1 ty)
                (sl1 ++ final dst (T.Eunop op a1 ty))
                (T.Eunop op a1 ty) tmp
| tr_binop: forall ce le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_val e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le dst (S.Ebinop op e1 e2 ty)
                (sl1 ++ sl2 ++ final dst (T.Ebinop op a1 a2 ty))
                (T.Ebinop op a1 a2 ty) tmp
| tr_cast_effects: forall ce le e1 ty sl1 a1 any tmp,
    tr_expr ce le For_effects e1 sl1 a1 tmp ->
    tr_expr ce le For_effects (S.Ecast e1 ty)
                sl1 any tmp
| tr_cast_val: forall ce le dst e1 ty sl1 a1 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Ecast e1 ty)
                (sl1 ++ final dst (T.Ecast a1 ty))
                (T.Ecast a1 ty) tmp
| tr_seqand_val: forall ce le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le For_val (S.Eseqand e1 e2 ty)
          (sl1 ++ makeif a1 (makeseq sl2)
                            (T.Sset t (T.Econst_int Int.zero ty)) :: nil)
          (T.Etempvar t ty) tmp
| tr_seqand_effects: forall ce le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_effects e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le For_effects (S.Eseqand e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil)
                  any tmp
| tr_seqand_set: forall ce le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le (For_set sd) (S.Eseqand e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq sl2)
                                    (makeseq (do_set sd (T.Econst_int Int.zero ty))) :: nil)
                  any tmp
| tr_seqor_val: forall ce le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le For_val (S.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 (T.Sset t (T.Econst_int Int.one ty))
                                    (makeseq sl2) :: nil)
                  (T.Etempvar t ty) tmp
| tr_seqor_effects: forall ce le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_effects e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le For_effects (S.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil)
                  any tmp
| tr_seqor_set: forall ce le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le (For_set sd) (S.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq (do_set sd (T.Econst_int Int.one ty)))
                                    (makeseq sl2) :: nil)
                  any tmp
| tr_condition_val: forall ce le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 ->
    tr_expr ce le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
    tr_expr ce le For_val (S.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    (T.Etempvar t ty) tmp
| tr_condition_effects: forall ce le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_effects e2 sl2 a2 tmp2 ->
    tr_expr ce le For_effects e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
    tr_expr ce le For_effects (S.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    any tmp
| tr_condition_set: forall ce le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2 ->
    tr_expr ce le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
    tr_expr ce le (For_set sd) (S.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    any tmp
| tr_comma: forall ce le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
    tr_expr ce le For_effects e1 sl1 a1 tmp1 ->
    tr_expr ce le dst e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le dst (S.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
| tr_paren_val: forall ce le e1 tycast ty sl1 a1 t tmp,
    tr_expr ce le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp ->
    In t tmp ->
    tr_expr ce le For_val (S.Eparen e1 tycast ty) sl1 (T.Etempvar t ty) tmp
| tr_paren_effects: forall ce le e1 tycast ty sl1 a1 tmp any,
    tr_expr ce le For_effects e1 sl1 a1 tmp ->
    tr_expr ce le For_effects (S.Eparen e1 tycast ty) sl1 any tmp
| tr_paren_set: forall ce le t sd e1 tycast ty sl1 a1 tmp any,
    tr_expr ce le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp ->
    In t tmp ->
    tr_expr ce le (For_set sd) (S.Eparen e1 tycast ty) sl1 any tmp

with tr_exprlist : composite_env -> T.temp_env -> S.exprlist -> list T.stmt -> list T.expr -> list ident -> Prop :=
| tr_nil: forall ce le tmp,
    tr_exprlist ce le S.Enil nil nil tmp
| tr_cons: forall ce le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp,
      tr_expr ce le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist ce le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_exprlist ce le (S.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp.

Closing Fact tr_val_inv :
  forall ce le dst v ty sl a tmp,
  tr_expr ce le dst (S.Eval v ty) sl a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    sl = nil
      /\ T.typeof a = ty
      /\ (forall tge e le' m,
          (forall id, In id tmp -> le'!id = le!id) ->
            T.eval_expr tge e le' m a v)
  | self__SimplExpr.For_effects => sl = nil
  | self__SimplExpr.For_set sd =>
    exists b, sl = do_set sd b
        /\ T.typeof b = ty
        /\ (forall tge e le' m,
            (forall id, In id tmp -> le'!id = le!id) ->
              T.eval_expr tge e le' m b v)
  end
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_sizeof_inv :
  forall ce le dst ty' ty sl a tmp,
  tr_expr ce le dst (S.Esizeof ty' ty) sl a tmp ->
  sl = final dst (T.Esizeof ty' ty)
  /\ a = T.Esizeof ty' ty
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_alignof_inv :
  forall ce le dst ty' ty sl a tmp,
  tr_expr ce le dst (S.Ealignof ty' ty) sl a tmp ->
  sl = final dst (T.Ealignof ty' ty)
  /\ a = T.Ealignof ty' ty
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_unop_inv :
  forall ce le dst op e1 ty sl a tmp,
  tr_expr ce le dst (S.Eunop op e1 ty) sl a tmp ->
  exists sl1 a1,
  sl = sl1 ++ final dst (T.Eunop op a1 ty)
  /\ a = T.Eunop op a1 ty
  /\ tr_expr ce le For_val e1 sl1 a1 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_binop_inv :
  forall ce le dst op e1 e2 ty sl a tmp,
  tr_expr ce le dst (S.Ebinop op e1 e2 ty) sl a tmp ->
  exists sl1 a1 tmp1 sl2 a2 tmp2,
  sl = sl1 ++ sl2 ++ final dst (T.Ebinop op a1 a2 ty)
  /\ a = T.Ebinop op a1 a2 ty
  /\ tr_expr ce le For_val e1 sl1 a1 tmp1
  /\ tr_expr ce le For_val e2 sl2 a2 tmp2
  /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_cast_inv :
  forall ce le dst e1 ty sl a tmp,
  tr_expr ce le dst (S.Ecast e1 ty) sl a tmp ->
  (exists a1, dst = For_effects /\ tr_expr ce le For_effects e1 sl a1 tmp)
  \/ (exists sl1 a1, sl = sl1 ++ final dst (T.Ecast a1 ty) /\ a = T.Ecast a1 ty /\ tr_expr ce le For_val e1 sl1 a1 tmp)
  by plain {intros *; intros H; inv H; [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

Closing Fact tr_seqand_inv :
  forall ce le dst e1 e2 ty sl a tmp,
  tr_expr ce le dst (S.Eseqand e1 e2 ty) sl a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1 (makeseq sl2)
      (T.Sset t (T.Econst_int Int.zero ty)) :: nil
    /\ a = T.Etempvar t ty
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists sl1 a1 tmp1 sl2 a2 tmp2,
    sl = sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le For_effects e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp
  | self__SimplExpr.For_set sd =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1
      (makeseq sl2)
      (makeseq (do_set sd (T.Econst_int Int.zero ty)))
      :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  end
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_seqor_inv :
  forall ce le dst e1 e2 ty sl a tmp,
  tr_expr ce le dst (S.Eseqor e1 e2 ty) sl a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1
      (T.Sset t (T.Econst_int Int.one ty))
      (makeseq sl2)
      :: nil
    /\ a = T.Etempvar t ty
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists sl1 a1 tmp1 sl2 a2 tmp2,
    sl = sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le For_effects e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp
  | self__SimplExpr.For_set sd =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1
      (makeseq (do_set sd (T.Econst_int Int.one ty)))
      (makeseq sl2)
      :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  end
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_condition_inv :
  forall ce le dst e1 e2 e3 ty sl a tmp,
  tr_expr ce le dst (S.Econdition e1 e2 e3 ty) sl a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists t sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3,
    sl = sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil
    /\ a = T.Etempvar t ty
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2
    /\ tr_expr ce le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3,
    sl = sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le For_effects e2 sl2 a2 tmp2
    /\ tr_expr ce le For_effects e3 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp
  | self__SimplExpr.For_set sd =>
    exists t sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3,
    sl = sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2
    /\ tr_expr ce le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp /\ In t tmp
  end
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_comma_inv :
  forall ce le dst e1 e2 ty sl a2 tmp,
  tr_expr ce le dst (S.Ecomma e1 e2 ty) sl a2 tmp ->
  exists sl1 a1 tmp1 sl2 tmp2,
  sl = sl1 ++ sl2
  /\ tr_expr ce le For_effects e1 sl1 a1 tmp1
  /\ tr_expr ce le dst e2 sl2 a2 tmp2
  /\ list_disjoint tmp1 tmp2
  /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_paren_inv :
  forall ce le dst e1 tycast ty sl1 a tmp,
  tr_expr ce le dst (S.Eparen e1 tycast ty) sl1 a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists a1 t,
    a = T.Etempvar t ty
    /\ tr_expr ce le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp
    /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists a1, tr_expr ce le For_effects e1 sl1 a1 tmp
  | self__SimplExpr.For_set sd =>
    exists t a1,
    tr_expr ce le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp
    /\ In t tmp
  end
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_nil_inv :
  forall ce le sl al tmp,
  tr_exprlist ce le S.Enil sl al tmp ->
  sl = nil /\ al = nil
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_cons_inv :
  forall ce le e1 el2 sl al tmp,
  tr_exprlist ce le (S.Econs e1 el2) sl al tmp ->
  exists sl1 a1 tmp1 sl2 al2 tmp2,
  sl = sl1 ++ sl2 /\ al = a1 :: al2
  /\ tr_expr ce le For_val e1 sl1 a1 tmp1
  /\ tr_exprlist ce le el2 sl2 al2 tmp2
  /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_expr_invariant
  about tr_expr
  motive (fun ce le dst r sl a tmps (_ : tr_expr ce le dst r sl a tmps) =>
    forall le', (forall x, In x tmps -> le'!x = le!x) ->
    tr_expr ce le' dst r sl a tmps)
with tr_exprlist_invariant
  about tr_exprlist
  motive (fun ce le rl sl al tmps (_ : tr_exprlist ce le rl sl al tmps) =>
    forall le', (forall x, In x tmps -> le'!x = le!x) ->
    tr_exprlist ce le' rl sl al tmps).
FProof.
all: intros; fconstructor.
- intros. apply e0. intros. transitivity (le'!id); auto.
- intros. apply e0. intros. transitivity (le'!id); auto.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone
  about tr_expr
  motive (fun ce le dst r sl a tmps (_ : tr_expr ce le dst r sl a tmps) =>
    forall tmps', incl tmps tmps' ->
    tr_expr ce le dst r sl a tmps')
with tr_exprlist_monotone
  about tr_exprlist
  motive (fun ce le rl sl al tmps (_ : tr_exprlist ce le rl sl al tmps) =>
    forall tmps', incl tmps tmps' ->
    tr_exprlist ce le rl sl al tmps').
FProof.
all: intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

MetaData tr_top.
Inductive tr_top (ce : composite_env):
  T.genv -> T.env ->
  T.temp_env -> mem ->  destination ->
  S.expr -> list T.stmt ->
  T.expr -> list ident -> Prop :=
| tr_top_val_val: forall ge e le m v ty a tmp,
    T.typeof a = ty -> T.eval_expr ge e le m a v ->
    tr_top ce ge e le m For_val (S.Eval v ty) nil a tmp
| tr_top_base: forall ge e le m dst r sl a tmp,
    tr_expr ce le dst r sl a tmp ->
    tr_top ce ge e le m dst r sl a tmp.
FEnd tr_top.

MetaData tr_expression.
Inductive tr_expression (ce : composite_env): S.expr -> T.stmt -> T.expr -> Prop :=
| tr_expression_intro: forall r sl a tmps,
    (forall ge e le m, tr_top ce ge e le m For_val r sl a tmps) ->
    tr_expression ce r (makeseq sl) a.
FEnd tr_expression.

MetaData tr_expr_stmt.
Inductive tr_expr_stmt (ce : composite_env) : S.expr -> T.stmt -> Prop :=
| tr_expr_stmt_intro: forall r sl a tmps,
    (forall ge e le m, tr_top ce ge e le m For_effects r sl a tmps) ->
    tr_expr_stmt ce r (makeseq sl).
FEnd tr_expr_stmt.

MetaData tr_if.
Inductive tr_if (ce : composite_env) : S.expr -> T.stmt -> T.stmt -> T.stmt  -> Prop :=
| tr_if_intro: forall r s1 s2 sl a tmps,
    (forall ge e le m, tr_top ce ge e le m For_val r sl a tmps) ->
    tr_if ce r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).
FEnd tr_if.

FInductive tr_stmt: composite_env -> S.stmt -> T.stmt -> Prop :=
| tr_skip: forall ce,
    tr_stmt ce S.Sskip T.Sskip
| tr_do: forall ce r s,
    tr_expr_stmt ce r s ->
    tr_stmt ce (S.Sdo r) s
| tr_seq: forall ce s1 s2 ts1 ts2,
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    tr_stmt ce (S.Sseq s1 s2) (T.Sseq ts1 ts2)
| tr_ifthenelse_empty: forall ce r s' a,
    tr_expression ce r s' a ->
    tr_stmt ce (S.Sifthenelse r S.Sskip S.Sskip) (T.Sseq s' T.Sskip)
| tr_ifthenelse: forall ce r s1 s2 s' a ts1 ts2,
    tr_expression ce r s' a ->
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    tr_stmt ce (S.Sifthenelse r s1 s2) (T.Sseq s' (T.Sifthenelse a ts1 ts2))
| tr_return_none: forall ce,
    tr_stmt ce (S.Sreturn None) (T.Sreturn None)
| tr_return_some: forall ce r s' a,
    tr_expression ce r s' a ->
    tr_stmt ce (S.Sreturn (Some r)) (T.Sseq s' (T.Sreturn (Some a)))
| tr_label: forall ce lbl s ts,
    tr_stmt ce s ts ->
    tr_stmt ce (S.Slabel lbl s) (T.Slabel lbl ts)
| tr_goto: forall ce lbl,
    tr_stmt ce (S.Sgoto lbl) (T.Sgoto lbl)
with tr_lblstmts: composite_env -> S.lbl_stmts -> T.lbl_stmts -> Prop :=
| tr_ls_nil: forall ce,
    tr_lblstmts ce S.LSnil T.LSnil
| tr_ls_cons: forall ce c s ls ts tls,
    tr_stmt ce s ts ->
    tr_lblstmts ce ls tls ->
    tr_lblstmts ce (S.LScons c s ls) (T.LScons c ts tls).

Closing Fact tr_skip_inv :
  forall ce ts,
  tr_stmt ce S.Sskip ts ->
  ts = T.Sskip
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_do_inv :
  forall ce r s,
  tr_stmt ce (S.Sdo r) s ->
  tr_expr_stmt ce r s
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_seq_inv :
  forall ce s1 s2 ts,
  tr_stmt ce (S.Sseq s1 s2) ts ->
  exists ts1 ts2, ts = T.Sseq ts1 ts2 /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s2 ts2
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_ifthenelse_inv :
  forall ce r s1 s2 ts,
  tr_stmt ce (S.Sifthenelse r s1 s2) ts ->
  (exists s' a, s1 = S.Sskip /\ s2 = S.Sskip /\ ts = T.Sseq s' T.Sskip /\ tr_expression ce r s' a)
  \/ (exists s' a ts1 ts2, ts = T.Sseq s' (T.Sifthenelse a ts1 ts2)
      /\ tr_expression ce r s' a /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s2 ts2)
  by plain {intros *; intros H; inv H; [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

Closing Fact tr_return_inv :
  forall ce r s,
  tr_stmt ce (S.Sreturn r) s ->
  match r with
  | None => s = T.Sreturn None
  | Some r => exists s' a, s = T.Sseq s' (T.Sreturn (Some a)) /\ tr_expression ce r s' a
  end
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_label_inv :
  forall ce lbl s ts,
  tr_stmt ce (S.Slabel lbl s) ts ->
  exists ts', ts = T.Slabel lbl ts' /\ tr_stmt ce s ts'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_goto_inv :
  forall ce lbl ts,
  tr_stmt ce (S.Sgoto lbl) ts ->
  ts = T.Sgoto lbl
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_ls_nil_inv :
  forall ce ts,
  tr_lblstmts ce S.LSnil ts ->
  ts = T.LSnil
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_ls_cons_inv :
  forall ce c s ls ts,
  tr_lblstmts ce (S.LScons c s ls) ts ->
  exists ts' tls, ts = T.LScons c ts' tls /\ tr_stmt ce s ts' /\ tr_lblstmts ce ls tls
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

MetaData tr_function.
Inductive tr_function (ce : composite_env) :  S.function -> T.function -> Prop :=
| tr_function_intro: forall f tf,
    tr_stmt ce f.(S.fn_body) tf.(T.fn_body) ->
    T.fn_return tf = S.fn_return f ->
    T.fn_callconv tf = S.fn_callconv f ->
    T.fn_params tf = S.fn_params f ->
    T.fn_vars tf = S.fn_vars f ->
    tr_function ce f tf.
FEnd tr_function.

FInductive tr_fundef : S.program -> S.fundef -> T.fundef -> Prop :=
| tr_internal: forall p f tf,
    tr_function p.(prog_comp_env) f tf ->
    tr_fundef p (Internal f) (Internal tf).

Closing Fact tr_fundef_internal_inv :
  forall p f tfd,
  tr_fundef p (Internal f) tfd ->
  exists tf, tfd = Internal tf /\ tr_function p.(prog_comp_env) f tf
  by plain {intros *; intros H; inv H; eauto}.

FDefinition match_prog := fun (p: S.program) (tp: T.program) =>
    match_program_gen tr_fundef eq p p tp
 /\ prog_types tp = prog_types p.

FLemma comp_env_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  T.genv_cenv tge = S.genv_cenv ge.
FProofLemma.
  intros. subst. simpl.
  destruct H. generalize (prog_comp_env_eq tprog) (prog_comp_env_eq prog).
  congruence.
Qed. CloseFLemma.

FLemma function_return_preserved:
  forall ce f tf, tr_function ce f tf ->
  T.fn_return tf = S.fn_return f.
FProofLemma.
intros. inv H; auto.
Qed. CloseFLemma.

FInduction tr_simple_expr_nil
  about tr_expr
  motive (fun ce le dst r sl a tmps (_ : tr_expr ce le dst r sl a tmps) =>
    dst = For_val \/ dst = For_effects -> S.simple r = true -> sl = nil)
with tr_simple_exprlist_nil
  about tr_exprlist
  motive (fun ce le rl sl al tmps (_ : tr_exprlist ce le rl sl al tmps) =>
    S.simplelist rl = true -> sl = nil).
FProof.
all:
  assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil)
  by (intros; destruct H; subst dst; auto).
all: intros; fsimpl in *; auto; try (destruct H; discriminate).
- rewrite H; auto. simpl; auto.
- destruct (andb_prop _ _ H2). rewrite H, H0; auto. simpl; auto.
- rewrite H; auto. simpl; auto.
- destruct (andb_prop _ _ H1). rewrite H; auto.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction tr_simple_rvalue
  about S.eval_simple_rvalue
  motive (fun ge e m r v (_ : S.eval_simple_rvalue ge e m r v) =>
    forall prog tprog tge, match_prog prog tprog ->
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall ce le dst sl a tmps,
    tr_expr ce le dst r sl a tmps ->
    match dst with
    | self__SimplExpr.For_val => sl = nil /\ S.typeof r = T.typeof a /\ T.eval_expr tge e le m a v
    | self__SimplExpr.For_effects => sl = nil
    | self__SimplExpr.For_set sd =>
        exists b, sl = do_set sd b
               /\ S.typeof r = T.typeof b
               /\ T.eval_expr tge e le m b v
    end).
FProof.
(* val *)
- intros. fsimpl.
  apply tr_val_inv in H2.
  destruct dst; destruct H2; intuition eauto.
(* unop *)
- intros. fsimpl.
  apply tr_unop_inv in H3; unpack H3.
  exploit (H prog tprog tge); eauto. intros [A [B C]].
  subst sl sl1 a. simpl.
  assert (T.eval_expr tge e le m (T.Eunop op a1 ty) v).
  { fconstructor. congruence. }
  destruct dst.
  + fsimpl. auto.
  + auto.
  + simpl. eexists; repeat split; fsimpl; auto.
(* binop *)
- intros. fsimpl.
  apply tr_binop_inv in H4; unpack H4.
  exploit (H prog tprog tge); eauto. intros [A [B C]].
  exploit (H0 prog tprog tge); eauto. intros [D [E F]].
  subst sl sl1 sl2 a. simpl.
  assert (T.eval_expr tge e le m (T.Ebinop op a1 a2 ty) v).
  { fconstructor. rewrite (comp_env_preserved prog tprog ge tge); congruence. }
  destruct dst.
  + fsimpl. auto.
  + auto.
  + simpl. eexists; repeat split; fsimpl; auto.
(* cast *)
- intros. fsimpl.
  apply tr_cast_inv in H3 as [[a1 []] | [sl1 [a1 [? []]]]].
  (* effects *)
  + destruct dst; try discriminate.
    exploit (H prog tprog tge); eauto.
  (* val *)
  + exploit (H prog tprog tge); eauto.
    intros [A [B C]]. subst sl sl1 a. simpl.
    assert (T.eval_expr tge e le m (T.Ecast a1 ty) v).
    { fconstructor. congruence. }
    destruct dst.
    * fsimpl. auto.
    * auto.
    * simpl. eexists; repeat split; fsimpl; auto.
(* sizeof *)
- intros. rewrite <- (comp_env_preserved prog tprog ge tge); try assumption.
  fsimpl. apply tr_sizeof_inv in H2 as []; subst sl a; simpl.
  destruct dst.
  + repeat split; fsimpl; auto. fconstructor.
  + auto.
  + exists (T.Esizeof ty1 ty).
    repeat split; fsimpl; auto. fconstructor.
(* alignof *)
- intros. rewrite <- (comp_env_preserved prog tprog ge tge); try assumption.
  fsimpl. apply tr_alignof_inv in H2 as []; subst sl a; simpl.
  destruct dst.
  + repeat split; fsimpl; auto. fconstructor.
  + auto.
  + exists (T.Ealignof ty1 ty).
    repeat split; fsimpl; auto. fconstructor.
Qed. FEnd tr_simple_rvalue.

FInduction tr_expr_leftcontext
  about S.leftcontext
  motive (fun from to c (_ : S.leftcontext from to c) =>
    forall ce le e dst sl a tmps,
    tr_expr ce le dst (c e) sl a tmps ->
    exists dst' sl1 sl2 a' tmp',
    tr_expr ce le dst' e sl1 a' tmp'
    /\ sl = sl1 ++ sl2
    /\ incl tmp' tmps
    /\ (forall le' e' sl3,
          tr_expr ce le' dst' e' sl3 a' tmp' ->
          (forall id, ~In id tmp' -> le'!id = le!id) ->
          S.typeof e' = S.typeof e ->
          tr_expr ce le' dst (c e') (sl3 ++ sl2) a tmps))
with tr_expr_leftcontextlist
  about S.leftcontextlist
  motive (fun from c (_ : S.leftcontextlist from c) =>
    forall ce le e sl a tmps,
    tr_exprlist ce le (c e) sl a tmps ->
    exists dst' sl1 sl2 a' tmp',
    tr_expr ce le dst' e sl1 a' tmp'
    /\ sl = sl1 ++ sl2
    /\ incl tmp' tmps
    /\ (forall le' e' sl3,
          tr_expr ce le' dst' e' sl3 a' tmp' ->
          (forall id, ~In id tmp' -> le'!id = le!id) ->
          S.typeof e' = S.typeof e ->
          tr_exprlist ce le' (c e') (sl3 ++ sl2) a tmps)).
FProof.

Ltac TR :=
  econstructor; econstructor; econstructor; econstructor; econstructor;
  split; [eauto | split; [idtac | split]].

Ltac NOTIN :=
  match goal with
  | [ H1: In ?x ?l, H2: list_disjoint ?l _ |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  | [ H1: In ?x ?l, H2: list_disjoint _ ?l |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  end.

Ltac UNCHANGED :=
  match goal with
  | [ H: (forall (id: ident), ~In id _ -> ?le' ! id = ?le ! id) |-
          (forall (id: ident), In id _ -> ?le' ! id = ?le ! id) ] =>
      intros; apply H; NOTIN
  end.

(* base *)
- intros. TR.
  + rewrite app_nil_r; auto.
  + red. auto.
  + intros. rewrite app_nil_r; auto.
(* unop *)
- intros. apply tr_unop_inv in H0; unpack H0; subst.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * subst sl1. rewrite app_assoc. eauto.
  * auto.
  * intros. rewrite app_assoc. fconstructor.
(* binop left *)
- intros. apply tr_binop_inv in H0; unpack H0; subst.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * subst sl1. rewrite <- app_assoc. eauto.
  * red. auto.
  * intros. rewrite app_assoc. fconstructor.
    eapply tr_expr_invariant; eauto. UNCHANGED.
(* binop right *)
- intros. apply tr_binop_inv in H0; unpack H0; subst.
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl2. rewrite app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2'). rewrite <- app_assoc.
    fconstructor. eapply tr_expr_invariant; eauto. UNCHANGED.
(* cast *)
- intros. apply tr_cast_inv in H0 as [[a1 []] | [sl1 [a1 [? []]]]].
  (* for effects *)
  + exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * eauto.
    * auto.
    * intros. subst dst. eauto using tr_cast_effects.
  (* generic *)
  + exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl sl1. rewrite app_assoc. eauto.
    * auto.
    * intros. rewrite app_assoc. subst a. eauto using tr_cast_val.
(* seqand *)
- intros. apply tr_seqand_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_seqand_val.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_seqand_effects.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_seqand_set.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
(* seqor *)
- intros. apply tr_seqor_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_seqor_val.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_seqor_effects.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_seqor_set.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
(* condition *)
- intros. apply tr_condition_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_condition_val.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto. -- auto. -- auto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_condition_effects.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto. -- auto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply tr_condition_set.
      -- apply S; auto.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- eapply tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto. -- auto. -- auto.
(* comma *)
- intros. apply tr_comma_inv in H0. unpack H0.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl sl1. rewrite app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. eapply tr_comma with (tmp2 := tmp2).
    * apply S; auto.
    * eapply tr_expr_invariant; eauto. UNCHANGED.
    * auto. * auto. * auto.
(* paren *)
- intros. apply tr_paren_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * rewrite Q. eauto.
  * red. auto.
  * intros. eapply tr_paren_val; eauto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * rewrite Q. eauto.
  * red. auto.
  * intros. eapply tr_paren_effects; eauto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * rewrite Q. eauto.
  * red. auto.
  * intros. eapply tr_paren_set; eauto.
(* cons left *)
- intros. apply tr_cons_inv in H0; unpack H0; subst.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl1. rewrite app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. fconstructor.
    eapply tr_exprlist_invariant; eauto. UNCHANGED.
(* cons right *)
- intros. apply tr_cons_inv in H0; unpack H0; subst.
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl2. eauto.
  + red. auto.
  + intros. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2').
    fconstructor. eapply tr_expr_invariant; eauto. UNCHANGED.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FLemma tr_top_leftcontext:
  forall ce tge e le m dst rtop sl a tmps,
  tr_top ce tge e le m dst rtop sl a tmps ->
  forall r c,
  rtop = c r ->
  S.leftcontext S.RV S.RV c ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_top ce tge e le m dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' m' r' sl3,
        tr_expr ce le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        S.typeof r' = S.typeof r ->
        tr_top ce tge e le' m' dst (c r') (sl3 ++ sl2) a tmps).
FProofLemma.
induction 1; intros.
(* val to val *)
- apply (S.leftcontext_val_top r v ty) in H2; auto. subst c r.
  exists For_val. repeat eexists.
  + apply tr_top_val_val; eauto.
  + instantiate (1 := nil); auto.
  + apply incl_refl.
  + intros. rewrite app_nil_r. constructor. auto.
(* base *)
- subst r. exploit tr_expr_leftcontext; eauto.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  exists dst' sl1 sl2 a' tmp'. repeat split.
  + apply tr_top_base; auto.
  + auto.
  + auto.
  + intros. apply tr_top_base. apply S; auto.
Qed. CloseFLemma.

FLemma sem_cast_deterministic:
  forall v ty ty' m1 v1 m2 v2,
  sem_cast v ty ty' m1 = Some v1 ->
  sem_cast v ty ty' m2 = Some v2 ->
  v1 = v2.
FProofLemma.
unfold sem_cast; intros. destruct (classify_cast ty ty'); try congruence.
- destruct v; try congruence.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
- destruct v; try congruence.
  destruct (negb Archi.ptr64); try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
Qed. CloseFLemma.

FInduction eval_simpl_expr_sound
  about T.eval_expr
  motive (fun tge e le m a v (_ : T.eval_expr tge e le m a v) =>
    match eval_simpl_expr a with Some v' => v' = v | None => True end).
FProof.
all: intros; fsimpl; auto.
- destruct (eval_simpl_expr a); auto. subst.
  destruct (sem_cast v1 (T.typeof a) ty Mem.empty) as [v'|] eqn:C; auto.
  eapply sem_cast_deterministic; eauto.
Qed. FEnd eval_simpl_expr_sound.

FLemma static_bool_val_sound:
  forall v t m b, bool_val v t Mem.empty = Some b -> bool_val v t m = Some b.
FProofLemma.
  intros until b; unfold bool_val.
  destruct (classify_bool t); destruct v; destruct Archi.ptr64 eqn:SF; auto;
  simpl; congruence.
Qed. CloseFLemma.

FLemma step_makeif:
  forall tge f a s1 s2 k e le m v1 b,
  T.eval_expr tge e le m a v1 ->
  bool_val v1 (T.typeof a) m = Some b ->
  star T.step tge (T.State f (makeif a s1 s2) k e le m)
             E0 (T.State f (if b then s1 else s2) k e le m).
FProofLemma.
  intros. functional induction (makeif a s1 s2).
- specialize (eval_simpl_expr_sound tge _ _ _ _ _ H). cbv. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (T.typeof a) m = Some true) by (apply static_bool_val_sound; auto).
  replace b with true by congruence. constructor.
- specialize (eval_simpl_expr_sound tge _ _ _ _ _ H). cbv. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (T.typeof a) m = Some false) by (apply static_bool_val_sound; auto).
  replace b with false by congruence. constructor.
- apply star_one. eapply T.step_ifthenelse; eauto.
- apply star_one. eapply T.step_ifthenelse; eauto.
Qed. CloseFLemma.

MetaData Kseqlist.
Fixpoint Kseqlist (sl: list T.stmt) (k: T.cont) :=
match sl with
| nil => k
| s :: l => T.Kseq s (Kseqlist l k)
end.
FEnd Kseqlist.

FLemma Kseqlist_app:
  forall sl1 sl2 k,
  Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k).
FProofLemma.
induction sl1; simpl; congruence.
Qed. CloseFLemma.

FLemma push_seq:
  forall tge f sl k e le m,
  star T.step tge (T.State f (makeseq sl) k e le m)
              E0 (T.State f T.Sskip (Kseqlist sl k) e le m).
FProofLemma.
intros. unfold makeseq. generalize T.Sskip. revert sl k.
induction sl; simpl; intros.
apply star_refl.
eapply star_right. apply IHsl. fconstructor. traceEq.
Qed. CloseFLemma.

FInductive match_cont : composite_env -> S.cont -> T.cont -> Prop :=
| match_Kstop: forall ce,
    match_cont ce S.Kstop T.Kstop
| match_Kseq: forall ce s k ts tk,
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont ce (S.Kseq s k) (T.Kseq ts tk)
with match_cont_exp : composite_env -> destination -> T.expr -> S.cont -> T.cont -> Prop :=
| match_Kdo: forall ce k a tk,
    match_cont ce k tk ->
    match_cont_exp ce For_effects a (S.Kdo k) tk
| match_Kifthenelse_empty: forall ce a k tk,
    match_cont ce k tk ->
    match_cont_exp ce For_val a (S.Kifthenelse S.Sskip S.Sskip k) (T.Kseq T.Sskip tk)
| match_Kifthenelse_1: forall ce a s1 s2 k ts1 ts2 tk,
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    match_cont ce k tk ->
    match_cont_exp ce For_val a (S.Kifthenelse s1 s2 k) (T.Kseq (T.Sifthenelse a ts1 ts2) tk)
| match_Kreturn: forall ce k a tk,
    match_cont ce k tk ->
    match_cont_exp ce For_val a (S.Kreturn k) (T.Kseq (T.Sreturn (Some a)) tk).

FInduction match_cont_is_call_cont
  about match_cont
  motive (fun ce k tk (_ : match_cont ce k tk) =>
    S.is_call_cont k -> forall ce', match_cont ce' k tk).
FProof.
- intros. fconstructor.
- intros. fsimpl in *. contradiction.
Qed. FEnd match_cont_is_call_cont.

FInduction match_cont_call_cont
  about match_cont
  motive (fun ce k tk (_ : match_cont ce k tk) =>
    forall ce', match_cont ce' (S.call_cont k) (T.call_cont tk)).
FProof.
all: intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_cont_call_cont.

Closing Fact is_call_cont_preserved :
  forall ce k tk, match_cont ce k tk -> S.is_call_cont k -> T.is_call_cont tk
  by plain {intros *; intros MK; inv MK; auto}.

Closing Fact match_cont_seq_inv :
  forall ce s k tk,
  match_cont ce (S.Kseq s k) tk ->
  exists ts tk', tk = T.Kseq ts tk' /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact match_cont_exp_no_set :
  forall ce sd a k tk,
  ~ match_cont_exp ce (For_set sd) a k tk
  by {intros; intro Hc; inversion Hc}.

Closing Fact match_cont_exp_do_inv :
  forall ce dst a k tk,
  match_cont_exp ce dst a (S.Kdo k) tk ->
  dst = For_effects /\ match_cont ce k tk
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact match_cont_exp_ifthenelse_inv :
  forall ce dst a s1 s2 k tk,
  match_cont_exp ce dst a (S.Kifthenelse s1 s2 k) tk ->
  (exists tk', dst = For_val /\ s1 = S.Sskip /\ s2 = S.Sskip /\ tk = T.Kseq T.Sskip tk' /\ match_cont ce k tk')
  \/ (exists ts1 ts2 tk', dst = For_val /\ tk = T.Kseq (T.Sifthenelse a ts1 ts2) tk'
      /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s2 ts2 /\ match_cont ce k tk')
  by plain {intros *; intros H; inv H; [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

Closing Fact match_cont_exp_return_inv :
  forall ce dst a k tk,
  match_cont_exp ce dst a (S.Kreturn k) tk ->
  exists tk', dst = For_val /\ tk = T.Kseq (T.Sreturn (Some a)) tk'
    /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; eauto}.

MetaData match_states.
Inductive match_states (prog: S.program) (tge : T.genv) : S.state -> T.state -> Prop :=
    | match_exprstates: forall f r k e m tf sl tk le dest a tmps
        (* (LINK: linkorder cu prog)*)
        (TRF: tr_function prog.(prog_comp_env) f tf)
        (TR: tr_top prog.(prog_comp_env) tge e le m dest r sl a tmps)
        (MK: match_cont_exp prog.(prog_comp_env) dest a k tk),
        match_states prog tge (S.ExprState f r k e m)
                      (T.State tf T.Sskip (Kseqlist sl tk) e le m)
    | match_regularstates: forall f s k e m tf ts tk le
        (* (LINK: linkorder cu prog) *)
        (TRF: tr_function prog.(prog_comp_env) f tf)
        (TR: tr_stmt prog.(prog_comp_env) s ts)
        (MK: match_cont prog.(prog_comp_env) k tk),
        match_states prog tge (S.State f s k e m)
                      (T.State tf ts tk e le m)
    | match_callstates: forall fd args k m tfd tk
        (* (LINK: linkorder cu prog)*)
        (TR: tr_fundef prog fd tfd)
        (MK: forall ce, match_cont ce k tk),
        match_states prog tge (S.Callstate fd args k m)
                      (T.Callstate tfd args tk m)
    | match_returnstates: forall res k m tk
        (MK: forall ce, match_cont ce k tk),
        match_states prog tge (S.Returnstate res k m)
                      (T.Returnstate res tk m)
    | match_stuckstate: forall S,
        match_states prog tge S.Stuckstate S.
FEnd match_states.

FInduction tr_seq_of_labeled_statement
  about tr_lblstmts
  motive (fun ce ls tls (_ : tr_lblstmts ce ls tls) =>
    tr_stmt ce (S.seq_of_labeled_statement ls) (T.seq_of_labeled_statement tls)).
FProof.
all: intros; do 2 fsimpl; fconstructor.
Qed. FEnd tr_seq_of_labeled_statement.

FDefinition nolabel := fun (lbl: T.label) (s: T.stmt) =>
  forall k, T.find_label s lbl k = None.

FDefinition nolabel_list := fix rec (lbl: T.label) (sl: list T.stmt) :=
  match sl with
  | nil => True
  | s1 :: sl' => nolabel lbl s1 /\ rec lbl sl'
  end.

FLemma nolabel_list_app:
  forall lbl sl2 sl1, nolabel_list lbl sl1 -> nolabel_list lbl sl2 -> nolabel_list lbl (sl1 ++ sl2).
FProofLemma.
  intros lbl. induction sl1; simpl; intros. auto. tauto.
Qed. CloseFLemma.

FLemma makeseq_nolabel:
  forall lbl sl, nolabel_list lbl sl -> nolabel lbl (makeseq sl).
FProofLemma.
  intros lbl.
  assert (forall sl s, nolabel lbl s -> nolabel_list lbl sl -> nolabel lbl (makeseq_rec s sl)).
  { induction sl; intros. auto. destruct H0. apply IHsl; fsimpl; auto.
    red. intros; fsimpl. rewrite H. apply H0. }
  intros. unfold makeseq. apply H; auto. red. fsimpl. auto.
Qed. CloseFLemma.

FLemma makeif_nolabel:
  forall lbl a s1 s2, nolabel lbl s1 -> nolabel lbl s2 -> nolabel lbl (makeif a s1 s2).
FProofLemma.
  intros. functional induction (makeif a s1 s2); auto.
  - red; fsimpl; intros. rewrite H; auto.
  - red; fsimpl; intros. rewrite H; auto.
Qed. CloseFLemma.

FLemma nolabel_do_set:
  forall lbl sd a, nolabel_list lbl (do_set sd a).
FProofLemma.
  intros lbl. induction sd; intros; split; auto; red; fsimpl; auto.
Qed. CloseFLemma.

FLemma nolabel_final:
  forall lbl dst a, nolabel_list lbl (final dst a).
FProofLemma.
  destruct dst; simpl; intros. auto. auto. apply nolabel_do_set.
Qed. CloseFLemma.

FInduction tr_find_label_expr
  about tr_expr
  motive (fun ce le dst r sl a tmps (_ : tr_expr ce le dst r sl a tmps) =>
    forall lbl, nolabel_list lbl sl)
with tr_find_label_exprlist
  about tr_exprlist
  motive (fun ce le rl sl al tmps (_ : tr_exprlist ce le rl sl al tmps) =>
    forall lbl, nolabel_list lbl sl).
FProof.
Ltac NoLabelTac :=
  match goal with
  | [ |- nolabel_list ?lbl nil ] => exact I
  | [ |- nolabel_list ?lbl (do_set _ _) ] => apply (nolabel_do_set lbl) (*; NoLabelTac*)
  | [ |- nolabel_list ?lbl (final _ _) ] => apply (nolabel_final lbl) (*; NoLabelTac*)
  | [ |- nolabel_list ?lbl (_ :: _) ] => simpl; split; NoLabelTac
  | [ |- nolabel_list ?lbl (_ ++ _) ] => apply (nolabel_list_app lbl); NoLabelTac
  | [ H: _ -> nolabel_list ?lbl ?x |- nolabel_list ?lbl ?x ] => apply H; NoLabelTac
  | [ |- nolabel ?lbl (makeseq _) ] => apply (makeseq_nolabel lbl); NoLabelTac
  | [ |- nolabel ?lbl (makeif _ _ _) ] => apply (makeif_nolabel lbl); NoLabelTac
  | [ |- nolabel _ _ ] => red; intros; fsimpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.
all: intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FLemma tr_find_label_top:
  forall ce tge lbl e le m dst r sl a tmps,
  tr_top ce tge e le m dst r sl a tmps -> nolabel_list lbl sl.
FProofLemma.
  induction 1.
  - exact I.
  - eapply tr_find_label_expr. eassumption.
Qed. CloseFLemma.

FLemma tr_find_label_expression:
  forall ce (tge: T.genv) lbl r s a,
  tr_expression ce r s a -> forall k, T.find_label s lbl k = None.
FProofLemma.
  intros. inv H.
  assert (nolabel lbl (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with
    (e := T.empty_env) (le := PTree.empty val) (m := Mem.empty) (tge := tge).
  eauto. apply H.
Qed. CloseFLemma.

FLemma tr_find_label_expr_stmt:
  forall ce (tge: T.genv) lbl r s,
  tr_expr_stmt ce r s -> forall k, T.find_label s lbl k = None.
FProofLemma.
  intros. inv H.
  assert (nolabel lbl (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with
    (e := T.empty_env) (le := PTree.empty val) (m := Mem.empty) (tge := tge).
  eauto. apply H.
Qed. CloseFLemma.

FInduction tr_find_label
  about S.stmt
  motive (fun (s : S.stmt) =>
    forall ce (tge: T.genv) lbl k ts tk
      (TR : tr_stmt ce s ts)
      (MC : match_cont ce k tk),
    match S.find_label s lbl k with
    | None =>
        T.find_label ts lbl tk = None
    | Some (s', k') =>
        exists ts' tk',
          T.find_label ts lbl tk = Some (ts', tk')
        /\ tr_stmt ce s' ts'
        /\ match_cont ce k' tk'
    end)
with tr_find_label_ls
  about S.lbl_stmts
  motive (fun (s : S.lbl_stmts) =>
    forall ce (tge: T.genv) lbl k ts tk
      (TR : tr_lblstmts ce s ts)
      (MC : match_cont ce k tk),
    match S.find_label_ls s lbl k with
    | None =>
        T.find_label_ls ts lbl tk = None
    | Some (s', k') =>
        exists ts' tk',
          T.find_label_ls ts lbl tk = Some (ts', tk')
        /\ tr_stmt ce s' ts'
        /\ match_cont ce k' tk'
    end).
FProof.
(* seq *)
- intros. apply tr_seq_inv in TR; unpack TR; subst. fsimpl.
  exploit (H ce tge lbl (S.Kseq __i0 k)); eauto. fconstructor.
  destruct (S.find_label __i lbl (S.Kseq __i0 k)) as [[s' k'] | ].
  + intros [ts1' [tk' [A [B C]]]]. fsimpl. rewrite A. eauto.
  + intro EQ. fsimpl. rewrite EQ. eapply H0; eauto.
(* skip *)
- intros. apply tr_skip_inv in TR; subst. fsimpl. fsimpl. auto.
(* do *)
- intros. apply tr_do_inv in TR. fsimpl.
  eapply tr_find_label_expr_stmt; eauto.
(* ifthenelse *)
- intros. apply tr_ifthenelse_inv in TR as [He|Hn].
  (* ifthenelse empty *)
  + unpack He; subst.
    assert (Hf: S.find_label (S.Sifthenelse e S.Sskip S.Sskip) lbl k = None)
      by (do 3 fsimpl; auto); rewrite Hf; clear Hf.
    fsimpl. rewrite (tr_find_label_expression ce tge lbl _ _ _ TEMP3).
    fsimpl. auto.
  (* ifthenelse non empty *)
  + unpack Hn; subst. rename s' into sr.
    fsimpl. fsimpl. rewrite (tr_find_label_expression ce tge lbl _ _ _ TEMP0).
    exploit (H ce tge lbl k); eauto.
    destruct (S.find_label __i lbl k) as [[s' k'] | ].
    * intros [ts' [tk' [A [B C]]]]. fsimpl. rewrite A. eauto.
    * intro EQ. fsimpl. rewrite EQ. eapply H0; eauto.
(* return *)
- intros. apply tr_return_inv in TR. destruct o; unpack TR; subst.
  (* return some *)
  + fsimpl. fsimpl. rewrite (tr_find_label_expression ce tge lbl _ _ _ TEMP1).
    fsimpl. auto.
  (* return none *)
  + fsimpl. fsimpl. auto.
(* label *)
- intros. apply tr_label_inv in TR; unpack TR; subst.
  fsimpl. fsimpl. destruct (ident_eq lbl l).
  + eauto.
  + apply H; eauto.
(* goto *)
- intros. apply tr_goto_inv in TR; subst.
  fsimpl. fsimpl. auto.

(* nil *)
- intros. apply tr_ls_nil_inv in TR; subst.
  fsimpl. fsimpl. auto.
(* cons *)
- intros. apply tr_ls_cons_inv in TR; unpack TR; subst. rename ts' into tsr.
  fsimpl. fsimpl. exploit (H ce tge lbl (S.Kseq (S.seq_of_labeled_statement __i0) k)); eauto.
  + fconstructor. apply tr_seq_of_labeled_statement; eauto.
  + destruct (S.find_label __i lbl (S.Kseq (S.seq_of_labeled_statement __i0) k)) as [[s' k'] | ].
    * intros [ts' [tk' [A [B C]]]]. fsimpl. rewrite A. eauto.
    * intro EQ. fsimpl. rewrite EQ. eapply H0; eauto.
Qed. FEnd tr_find_label with tr_find_label_ls.

FRecursion esize about S.expr motive (fun (_ : S.expr) => nat)
  with esizelist about S.exprlist motive (fun (_ : S.exprlist) => nat) by _rect.
Case Evar x ty := 1%nat.
Case Eval v ty := 0%nat.
Case Eunop op r ty := (Datatypes.S(esize r)).
Case Ebinop op r1 r2 ty := (Datatypes.S(esize r1 + esize r2)%nat).
Case Ecast r1 ty := (Datatypes.S(esize r1)).
Case Eseqand r1 r2 ty := (Datatypes.S(esize r1)).
Case Eseqor r1 r2 ty := (Datatypes.S(esize r1)).
Case Econdition r1 r2 r3 ty := (Datatypes.S(esize r1)).
Case Esizeof ty' ty := 1%nat.
Case Ealignof ty' ty:= 1%nat.
Case Ecomma r1 r2 ty := (Datatypes.S(esize r1 + esize r2)%nat).
Case Eparen r1 tycast ty := (Datatypes.S(esize r1)).

Case Enil := 0%nat.
Case Econs r1 rl2 := (Datatypes.S(esize r1 + esizelist rl2)%nat).
FEnd esize with esizelist.

Closing Fact esize_zero_val :
  forall r, esize r = 0%nat -> exists v ty, r = S.Eval v ty
  by {intros [] H; eauto; lia}.

FRecursion measure_stmt about S.stmt motive (fun (_ : S.stmt) => nat) by _rect.
Case Sskip := 0%nat.
Case Sdo r := (2 + esize r)%nat.
Case Sifthenelse r s1 s2 := (2 + esize r)%nat.
Case _ := 0%nat.
FEnd measure_stmt.

FDefinition measure : S.state -> nat := fun st =>
  match st with
  | self__SimplExpr.S.ExprState _ r _ _ _ => (1 + esize r)%nat
  | self__SimplExpr.S.State _ s _ _ _ => measure_stmt s
  | _ => 0%nat
  end.

FInduction leftcontext_size
  about S.leftcontext
  motive (fun from to c (_ : S.leftcontext from to c) =>
    forall e1 e2,
    (esize e1 < esize e2)%nat ->
    (esize (c e1) < esize (c e2))%nat)
with leftcontextlist_size
  about S.leftcontextlist
  motive (fun from c (_ : S.leftcontextlist from c) =>
    forall e1 e2,
    (esize e1 < esize e2)%nat ->
    (esizelist (c e1) < esizelist (c e2))%nat).
FProof.
all: intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FLemma tr_val_gen:
  forall ce le dst v ty a tmp,
  T.typeof a = ty ->
  (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      T.eval_expr tge e le' m a v) ->
  tr_expr ce le dst (S.Eval v ty) (final dst a) a tmp.
FProofLemma.
  intros. destruct dst; simpl; fconstructor.
Qed. CloseFLemma.

FInduction estep_simulation about S.estep
  motive (fun ge S1 t S2 (_ : S.estep ge S1 t S2) =>
    forall prog tprog tge, match_prog prog tprog ->
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall T1 (MS : match_states prog tge S1 T1),
    exists T2,
    (plus T.step tge T1 t T2 \/ (star T.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
    /\ match_states prog tge S2 T2).
FProof.
all: intros; inv MS.
(* expr *)
- assert (tr_expr (prog_comp_env prog) le dest r sl a tmps).
    { inv TR. exfalso; unfold S.is_val in n; eauto. auto. }
  exploit tr_simple_rvalue; eauto. destruct dest.
  (* for value *)
  + intros [SL1 [TY1 EV1]]. subst sl.
    econstructor. split.
    * right; split. apply star_refl. unfold measure. fsimpl.
      destruct (esize r) eqn:Hs.
      -- apply esize_zero_val in Hs. contradiction.
      -- lia.
    * eapply match_exprstates with (tmps := tmps); eauto.
      apply tr_top_val_val; auto using EV1.
  (* for effects *)
  + intros SL1. subst sl.
    econstructor. split.
    * right; split. apply star_refl. unfold measure. fsimpl.
      destruct (esize r) eqn:Hs.
      -- apply esize_zero_val in Hs. contradiction.
      -- lia.
    * eapply match_exprstates with (tmps := tmps); eauto.
      apply tr_top_base. fconstructor.
  (* for set *)
  + apply match_cont_exp_no_set in MK as [].
(* seqand true *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_seqand_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + apply tr_paren_val with (a1 := a2); auto.
          apply tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + apply tr_paren_effects with (a1 := a2); auto.
          apply tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + apply tr_paren_set with (a1 := a2) (t := t); auto.
          apply tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
(* seqand false *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_seqand_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply star_one. fconstructor. fconstructor.
          * reflexivity.
        + reflexivity.
      - eapply match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor. rewrite H0; auto using PTree.gss.
        + intros. apply PTree.gso. congruence.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + apply step_makeif with (b := false) (v1 := v); auto. congruence.
        + reflexivity.
      - eapply match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
(* seqor true *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_seqor_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply star_one. fconstructor. fconstructor.
          * reflexivity.
        + reflexivity.
      - eapply match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor. rewrite H0; auto using PTree.gss.
        + intros. apply PTree.gso. congruence.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + apply step_makeif with (b := true) (v1 := v); auto. congruence.
        + reflexivity.
      - eapply match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
(* seqor false *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_seqor_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + apply tr_paren_val with (a1 := a2); auto.
          apply tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + apply tr_paren_effects with (a1 := a2); auto.
          apply tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- Kseqlist_app.
        eapply match_exprstates; eauto.
        apply S.
        + apply tr_paren_set with (a1 := a2) (t := t); auto.
          apply tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
(* condition *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_condition_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl Kseqlist. destruct b.
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply step_makeif with (b := true) (v1 := v); auto. congruence.
            * apply push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- Kseqlist_app.
          eapply match_exprstates; eauto.
          apply S.
          + apply tr_paren_val with (a1 := a2); auto.
            apply tr_expr_monotone with tmp2; eauto.
          + auto.
          + do 2 fsimpl. auto. }
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply step_makeif with (b := false) (v1 := v); auto. congruence.
            * apply push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- Kseqlist_app.
          eapply match_exprstates; eauto.
          apply S.
          + apply tr_paren_val with (a1 := a3); auto.
            apply tr_expr_monotone with tmp3; eauto.
          + auto.
          + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist. destruct b.
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply step_makeif with (b := true) (v1 := v); auto. congruence.
            * apply push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- Kseqlist_app.
          eapply match_exprstates; eauto.
          apply S.
          + apply tr_paren_effects with (a1 := a2); auto.
            apply tr_expr_monotone with tmp2; eauto.
          + auto.
          + do 2 fsimpl. auto. }
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply step_makeif with (b := false) (v1 := v); auto. congruence.
            * apply push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- Kseqlist_app.
          eapply match_exprstates; eauto.
          apply S.
          + apply tr_paren_effects with (a1 := a3); auto.
            apply tr_expr_monotone with tmp3; eauto.
          + auto.
          + do 2 fsimpl. auto. }
    (* for set *)
    * exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl Kseqlist. destruct b.
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply step_makeif with (b := true) (v1 := v); auto. congruence.
            * apply push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- Kseqlist_app.
          eapply match_exprstates; eauto.
          apply S.
          + apply tr_paren_set with (a1 := a2) (t := t); auto.
            apply tr_expr_monotone with tmp2; eauto.
          + auto.
          + do 2 fsimpl. auto. }
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply step_makeif with (b := false) (v1 := v); auto. congruence.
            * apply push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- Kseqlist_app.
          eapply match_exprstates; eauto.
          apply S.
          + apply tr_paren_set with (a1 := a3) (t := t); auto.
            apply tr_expr_monotone with tmp3; eauto.
          + auto.
          + do 2 fsimpl. auto. }
(* comma *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_comma_inv in H0. unpack H0.
    exploit tr_simple_rvalue; eauto. simpl; intro SL1.
    subst sl0 sl1; simpl Kseqlist.
    eexists. { split.
    - right. split.
      + apply star_refl.
      + rewrite <- Nat.succ_lt_mono.
        apply (leftcontext_size _ _ _ l). fsimpl. lia.
    - eapply match_exprstates; eauto.
      apply S.
      + eapply tr_expr_monotone; eauto.
      + auto.
      + fsimpl. auto. }
(* paren *)
- exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply tr_paren_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit tr_simple_rvalue; eauto. intros [b [SL1 [TY1 EV1]]].
      subst sl1 a'; simpl Kseqlist.
      eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + apply star_one. fconstructor. fconstructor.
            rewrite <- TY1; eauto.
          + reflexivity.
        - eapply match_exprstates; eauto.
          change sl2 with (final For_val (T.Etempvar t (S.typeof r)) ++ sl2).
          apply S.
          + fconstructor.
            * fsimpl. auto.
            * intros. fconstructor. rewrite H0; auto using PTree.gss.
          + intros. apply PTree.gso. congruence.
          + do 2 fsimpl. auto. }
    (* for effects *)
    * eexists. { split.
      - right. split.
        + apply star_refl.
        + simpl. rewrite <- Nat.succ_lt_mono.
          apply (leftcontext_size _ _ _ l). do 2 fsimpl. lia.
      - eapply match_exprstates; eauto.
        exploit tr_simple_rvalue; eauto.
        simpl. intros A. subst sl1.
        apply S.
        + fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit tr_simple_rvalue; eauto. intros [b [SL1 [TY1 EV1]]].
      subst sl1; simpl Kseqlist.
      eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + apply star_one. fconstructor. fconstructor.
            rewrite <- TY1; eauto.
          + reflexivity.
        - eapply match_exprstates; eauto.
          apply S.
          + fconstructor.
            * fsimpl. auto.
            * intros. fconstructor. rewrite H0; auto using PTree.gss.
          + intros. apply PTree.gso. congruence.
          + do 2 fsimpl. auto. }
Qed. FEnd estep_simulation.

FLemma tr_top_val_for_val_inv:
  forall tge ce e le m v ty sl a tmps,
  tr_top ce tge e le m For_val (S.Eval v ty) sl a tmps ->
  sl = nil /\ T.typeof a = ty /\ T.eval_expr tge e le m a v.
FProofLemma.
  intros. inv H.
  - (* finjection H0. *) apply cheat.
  - apply tr_val_inv in H0. intuition.
Qed. CloseFLemma.

FLemma alloc_variables_preserved:
  forall prog tprog ge tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall e m params e' m',
  S.alloc_variables ge e m params e' m' ->
  T.alloc_variables tge e m params e' m'.
FProofLemma.
  intros. induction H2; econstructor; eauto.
  rewrite (comp_env_preserved prog tprog ge tge); auto.
Qed. CloseFLemma.

FLemma bind_parameters_preserved:
  forall prog tprog ge tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall e m params args m',
  S.bind_parameters ge e m params args m' ->
  T.bind_parameters tge e m params args m'.
FProofLemma.
intros. induction H2; econstructor; eauto. inversion H3. subst v m' v1. clear H3.
- eapply T.assign_loc_value; eauto.
- inv H7. eapply T.assign_loc_value; eauto.
- rewrite <- (comp_env_preserved prog tprog ge tge) in *; try assumption.
  eapply T.assign_loc_copy; eauto.
Qed. CloseFLemma.

FLemma blocks_of_env_preserved:
  forall prog tprog ge tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall e, T.blocks_of_env tge e = S.blocks_of_env ge e.
FProofLemma.
  intros; unfold T.blocks_of_env, S.blocks_of_env.
  unfold T.block_of_binding, S.block_of_binding.
  rewrite (comp_env_preserved prog tprog ge tge); auto.
Qed. CloseFLemma.

FInduction sstep_simulation about S.sstep
   motive (fun ge S1 t S2 (_ : S.sstep ge S1 t S2) =>
           forall prog tprog tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
           forall T1 (MS : match_states prog tge S1 T1),
           exists T2,
           (plus T.step tge T1 t T2 \/
              (star T.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
                    /\ match_states prog tge S2 T2).
FProof.
all: intros; inv MS.
(* do 1 *)
- apply tr_do_inv in TR. inv TR.
  eexists. split.
  + right. split. apply push_seq. simpl. fsimpl. lia.
  + econstructor; eauto. fconstructor.
(* do 2 *)
- apply match_cont_exp_do_inv in MK as []; subst. inv TR.
  apply tr_val_inv in H0; subst.
  eexists. split.
  + right. split. apply star_refl. simpl. fsimpl. lia.
  + econstructor; eauto. fconstructor.
(* seq *)
- apply tr_seq_inv in TR; unpack TR; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto. fconstructor.
(* skip seq *)
- apply tr_skip_inv in TR; subst.
  apply match_cont_seq_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto.
(* ifthenelse *)
- apply tr_ifthenelse_inv in TR as [He|Hn].
  (* ifthenelse empty *)
  + unpack He. inv TEMP3. eexists. split.
    * left. eapply plus_left. fconstructor. apply push_seq. auto.
    * econstructor; eauto. fconstructor.
  (* ifthenelse non empty *)
  + unpack Hn. inv TEMP0. eexists. split.
    * left. eapply plus_left. fconstructor. apply push_seq. auto.
    * econstructor; eauto. fconstructor.
(* ifthenelse *)
- apply match_cont_exp_ifthenelse_inv in MK as [He|Hn].
  (* ifthenelse empty *)
  + unpack He; subst.
    exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
    eexists. split.
    * right. destruct b; split; do 2 (simpl; fsimpl); auto.
      -- eapply star_left. fconstructor. constructor. auto.
      -- eapply star_left. fconstructor. constructor. auto.
    * destruct b; econstructor; eauto; fconstructor.
  (* ifthenelse non empty *)
  + unpack Hn; subst.
    exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
    eexists. split.
    * left. eapply plus_two. fconstructor. fconstructor. auto.
    * destruct b; econstructor; eauto.
(* return none *)
- apply tr_return_inv in TR; subst.
  eexists. split.
  + left. apply plus_one. fconstructor. erewrite blocks_of_env_preserved; eauto.
  + econstructor. intros. eapply match_cont_call_cont; eauto.
(* return some 1 *)
- apply tr_return_inv in TR; unpack TR; subst. inv TEMP1.
  eexists. split.
  + left. eapply plus_left. fconstructor. apply push_seq. auto.
  + econstructor; eauto. fconstructor.
(* return some 2 *)
- apply match_cont_exp_return_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. eapply plus_two.
    -- fconstructor.
    -- fconstructor. erewrite function_return_preserved; eauto.
      erewrite blocks_of_env_preserved; eauto.
    -- auto.
  + econstructor. intros. eapply match_cont_call_cont; eauto.
(* skip return *)
- apply tr_skip_inv in TR; subst.
  assert (T.is_call_cont tk). { eapply is_call_cont_preserved; eauto. }
  eexists. split.
  + left. apply plus_one. fconstructor.
    erewrite blocks_of_env_preserved; eauto.
  + econstructor. intros. eapply match_cont_is_call_cont; eauto.
(* label *)
- apply tr_label_inv in TR; unpack TR; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto.
(* goto *)
- apply tr_goto_inv in TR; unpack TR; subst.
  inversion TRF; subst.
  exploit tr_find_label.
  + refine (T.globalenv tprog).
  + eauto.
  + eapply match_cont_call_cont; eauto.
  + rewrite e0. intros [ts' [tk' [A [B C]]]]. eexists. split.
    * left. apply plus_one. fconstructor.
    * econstructor; eauto.
(* internal function *)
- apply tr_fundef_internal_inv in TR; unpack TR. inversion TEMP1; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
    red. econstructor.
    * rewrite H3, H4. auto.
    * rewrite H3, H4. eapply alloc_variables_preserved; eauto.
    * rewrite H3. eapply bind_parameters_preserved; eauto.
    * eauto.
  + econstructor; eauto.
Qed. FEnd sstep_simulation.

FLemma simulation :
     (forall ge S1 t S2 (_ : S.step ge S1 t S2),
     forall prog tprog tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
     forall T1 (MS : match_states prog tge S1 T1),
        exists T2,
         (plus T.step tge T1 t T2 \/
           (star T.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
     /\ match_states prog tge S2 T2).
FProofLemma.
intros ge S1 t S2 STEP. destruct STEP.
- apply estep_simulation; auto.
- apply sstep_simulation; auto.
Qed. CloseFLemma.

FEnd SimplExpr.

FEnd Base.

Trait Comp_break_continue extends Base.

Family C.
FInductive stmt : Type :=
  | Sbreak : stmt
  | Scontinue : stmt.

FRecursion find_label with find_label_ls.
Case _ := (fun lbl k => None).
FEnd find_label with find_label_ls.

FInductive sstep : genv -> state -> trace -> state -> Prop :=
| step_continue_seq : forall ge f s k e m,
    sstep ge (State f Scontinue (Kseq s k) e m)
        E0 (State f Scontinue k e m)
| step_break_seq : forall ge f s k e m,
    sstep ge (State f Sbreak (Kseq s k) e m)
        E0 (State f Sbreak k e m).
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Sbreak : stmt
| Scontinue : stmt.

FRecursion find_label with find_label_ls.
Case _ := (fun lbl k => None).
FEnd find_label with find_label_ls.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_continue_seq: forall ge f s k e le m,
    step ge (State f Scontinue (Kseq s k) e le m)
      E0 (State f Scontinue k e le m)
| step_break_seq: forall ge f s k e le m,
    step ge (State f Sbreak (Kseq s k) e le m)
      E0 (State f Sbreak k e le m).
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.
FRecursion transl_stmt with transl_lblstmt.
Case Sbreak := (fun ce => ret T.Sbreak).
Case Scontinue := (fun ce => ret T.Scontinue).
FEnd transl_stmt with transl_lblstmt.

FInductive tr_stmt: composite_env -> S.stmt -> T.stmt -> Prop :=
| tr_break: forall ce,
    tr_stmt ce S.Sbreak T.Sbreak
| tr_continue: forall ce,
    tr_stmt ce S.Scontinue T.Scontinue.

Closing Fact tr_break_inv :
  forall ce s, tr_stmt ce S.Sbreak s -> s = T.Sbreak
  by plain {intros *; intros H; inv H; eauto}.

Closing Fact tr_continue_inv :
  forall ce s, tr_stmt ce S.Scontinue s -> s = T.Scontinue
  by plain {intros *; intros H; inv H; eauto}.

Inherit tr_find_label_expr_stmt.

FLemma tr_find_label_if:
  forall ce (tge: T.genv) lbl r s,
  tr_if ce r T.Sskip T.Sbreak s ->
  forall k, T.find_label s lbl k = None.
FProofLemma.
  intros. inv H.
  assert (nolabel lbl
    (makeseq
      (sl ++ makeif a T.Sskip T.Sbreak :: nil))).
  apply makeseq_nolabel.
  apply nolabel_list_app.
  eapply tr_find_label_top with
    (e := T.empty_env) (le := PTree.empty val) (m := Mem.empty) (tge := tge).
  eauto.
  simpl; split; auto. apply makeif_nolabel. red; fsimpl; auto. red; fsimpl; auto.
  apply H.
Qed. CloseFLemma.

FInduction tr_find_label with tr_find_label_ls.
FProof.
(* break *)
- intros. apply tr_break_inv in TR; subst.
  fsimpl. fsimpl. auto.
(* continue *)
- intros. apply tr_continue_inv in TR; subst.
  fsimpl. fsimpl. auto.
Qed. FEnd tr_find_label with tr_find_label_ls.

FRecursion measure_stmt.
Case _ := 0%nat.
FEnd measure_stmt.

FInduction sstep_simulation.
FProof.
all: intros; inv MS.
(* continue seq *)
- apply tr_continue_inv in TR; subst.
  apply match_cont_seq_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto. fconstructor.
(* break seq *)
- apply tr_break_inv in TR; subst.
  apply match_cont_seq_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto. fconstructor.
Qed. FEnd sstep_simulation.
FEnd SimplExpr.

FEnd Comp_break_continue.


Trait Comp_Loops extends Base, Comp_break_continue.

Trait C_Swhile extends C.
FInductive stmt : Type :=
  | Swhile : expr -> stmt -> stmt.

FInductive cont : Type :=
  | Kwhile1 : expr -> stmt -> cont -> cont
  | Kwhile2 : expr -> stmt -> cont -> cont.

FRecursion call_cont.
Case Kwhile1 e s k := (call_cont k).
Case Kwhile2 e s k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case Swhile a s1 := (fun lbl k => find_label s1 lbl (Kwhile2 a s1 k)).
FEnd find_label with find_label_ls.

FInductive sstep : genv -> state -> trace -> state -> Prop :=
| step_while : forall ge f x s k e m,
    sstep ge (State f (Swhile x s) k e m)
      E0 (ExprState f x (Kwhile1 x s k) e m)
| step_while_false : forall ge f v ty x s k e m,
    bool_val v ty m = Some false ->
    sstep ge (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
      E0 (State f Sskip k e m)
| step_while_true : forall ge f v ty x s k e m ,
    bool_val v ty m = Some true ->
    sstep ge (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
      E0 (State f s (Kwhile2 x s k) e m)
| step_skip_or_continue_while : forall ge f s0 x s k e m,
    s0 = Sskip \/ s0 = Scontinue ->
    sstep ge (State f s0 (Kwhile2 x s k) e m)
      E0 (State f (Swhile x s) k e m)
| step_break_while : forall ge f x s k e m,
    sstep ge (State f Sbreak (Kwhile2 x s k) e m)
      E0 (State f Sskip k e m).
FEnd C_Swhile.

Trait C_Sdowhile extends C.
FInductive stmt : Type :=
| Sdowhile : expr -> stmt -> stmt. (* do loop *)

FInductive cont : Type :=
| Kdowhile1 : expr -> stmt -> cont -> cont
| Kdowhile2 : expr -> stmt -> cont -> cont.

FRecursion call_cont.
Case Kdowhile1 e s k := (call_cont k).
Case Kdowhile2 e s k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case Sdowhile a s1 := (fun lbl k => find_label s1 lbl (Kdowhile1 a s1 k)).
FEnd find_label with find_label_ls.

FInductive sstep : genv -> state -> trace -> state -> Prop :=
| step_dowhile : forall ge f a s k e m,
    sstep ge (State f (Sdowhile a s) k e m)
      E0 (State f s (Kdowhile1 a s k) e m)
| step_skip_or_continue_dowhile : forall ge f s0 x s k e m,
    s0 = Sskip \/ s0 = Scontinue ->
    sstep ge (State f s0 (Kdowhile1 x s k) e m)
        E0 (ExprState f x (Kdowhile2 x s k) e m)
| step_dowhile_false : forall ge f v ty x s k e m,
    bool_val v ty m = Some false ->
    sstep ge (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
        E0 (State f Sskip k e m)
| step_dowhile_true : forall ge f v ty x s k e m,
    bool_val v ty m = Some true ->
    sstep ge (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
        E0 (State f (Sdowhile x s) k e m)
| step_break_dowhile : forall ge f a s k e m,
    sstep ge (State f Sbreak (Kdowhile1 a s k) e m)
        E0 (State f Sskip k e m).
FEnd C_Sdowhile.

Trait C_Sfor extends C.
FInductive stmt : Type :=
| Sfor : stmt -> expr -> stmt -> stmt -> stmt. (* for loop *)

FInductive cont : Type :=
| Kfor2 : expr -> stmt -> stmt -> cont -> cont
| Kfor3 : expr -> stmt -> stmt -> cont -> cont
| Kfor4 : expr -> stmt -> stmt -> cont -> cont.

FRecursion call_cont.
Case Kfor2 e2 e3 s k := (call_cont k).
Case Kfor3 e2 e3 s k := (call_cont k).
Case Kfor4 e2 e3 s k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case Sfor a1 a2 a3 s1 :=
  (fun lbl k =>
      match find_label a1 lbl (Kseq (Sfor Sskip a2 a3 s1) k) with
      | Some sk => Some sk
      | None =>
          match find_label s1 lbl (Kfor3 a2 a3 s1 k) with
          | Some sk => Some sk
          | None => find_label a3 lbl (Kfor4 a2 a3 s1 k)
          end
      end).
FEnd find_label with find_label_ls.

FInductive sstep : genv -> state -> trace -> state -> Prop :=
| step_for_start : forall ge f a1 a2 a3 s k e m,
    a1 <> Sskip ->
    sstep ge (State f (Sfor a1 a2 a3 s) k e m)
        E0 (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
| step_for : forall ge f a2 a3 s k e m,
    sstep ge (State f (Sfor Sskip a2 a3 s) k e m)
        E0 (ExprState f a2 (Kfor2 a2 a3 s k) e m)
| step_for_false : forall ge f v ty a2 a3 s k e m,
    bool_val v ty m = Some false ->
    sstep ge (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
        E0 (State f Sskip k e m)
| step_for_true : forall ge f v ty a2 a3 s k e m,
    bool_val v ty m = Some true ->
    sstep ge (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
        E0 (State f s (Kfor3 a2 a3 s k) e m)
| step_skip_or_continue_for3 : forall ge f x a2 a3 s k e m,
    x = Sskip \/ x = Scontinue ->
    sstep ge (State f x (Kfor3 a2 a3 s k) e m)
        E0 (State f a3 (Kfor4 a2 a3 s k) e m)
| step_break_for3 : forall ge f a2 a3 s k e m,
    sstep ge (State f Sbreak (Kfor3 a2 a3 s k) e m)
        E0 (State f Sskip k e m)
| step_skip_for4 : forall ge f a2 a3 s k e m,
    sstep ge (State f Sskip (Kfor4 a2 a3 s k) e m)
        E0 (State f (Sfor Sskip a2 a3 s) k e m).
FEnd C_Sfor.

Family C extends C_Swhile, C_Sdowhile, C_Sfor.
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Sloop: stmt -> stmt -> stmt. (* infinite loop *)

FInductive cont : Type :=
| Kloop1: stmt -> stmt -> cont -> cont
| Kloop2: stmt -> stmt -> cont -> cont.

FRecursion call_cont.
Case Kloop1 s1 s2 k := (call_cont k).
Case Kloop2 s1 s2 k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case Sloop s1 s2 :=
  (fun lbl k =>
      match find_label s1 lbl (Kloop1 s1 s2 k) with
      | Some sk => Some sk
      | None => find_label s2 lbl (Kloop2 s1 s2 k)
      end).
FEnd find_label with find_label_ls.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_loop : forall ge f s1 s2 k e le m,
    step ge (State f (Sloop s1 s2) k e le m)
      E0 (State f s1 (Kloop1 s1 s2 k) e le m)
| step_skip_or_continue_loop1 : forall ge f s1 s2 k e le m x,
    x = Sskip \/ x = Scontinue ->
    step ge (State f x (Kloop1 s1 s2 k) e le m)
      E0 (State f s2 (Kloop2 s1 s2 k) e le m)
| step_break_loop1 : forall ge f s1 s2 k e le m,
    step ge (State f Sbreak (Kloop1 s1 s2 k) e le m)
      E0 (State f Sskip k e le m)
| step_skip_loop2 : forall ge f s1 s2 k e le m,
    step ge (State f Sskip (Kloop2 s1 s2 k) e le m)
      E0 (State f (Sloop s1 s2) k e le m)
| step_break_loop2 : forall ge f s1 s2 k e le m,
    step ge (State f Sbreak (Kloop2 s1 s2 k) e le m)
      E0 (State f Sskip k e le m).
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Swhile extends SimplExpr.
Family S extends C_Swhile. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Swhile e s1 :=
  (fun ce =>
    do s' <- transl_if e T.Sskip T.Sbreak ce;
    do ts1 <- transl_stmt s1 ce;
    ret (T.Sloop (T.Sseq s' ts1) T.Sskip)).
FEnd transl_stmt with transl_lblstmt.

FInductive tr_stmt: composite_env -> S.stmt -> T.stmt -> Prop :=
| tr_while: forall ce r s1 s' ts1,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s1 ts1 ->
    tr_stmt ce (S.Swhile r s1)
            (T.Sloop (T.Sseq s' ts1) T.Sskip).

Closing Fact tr_while_inv :
  forall ce r s1 ts,
  tr_stmt ce (S.Swhile r s1) ts ->
  exists s' ts1, ts = (T.Sloop (T.Sseq s' ts1) T.Sskip) /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s1 ts1
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInductive match_cont : composite_env -> S.cont -> T.cont -> Prop :=
| match_Kwhile2 : forall ce r s k s' ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont ce (S.Kwhile2 r s k)
                  (T.Kloop1 (T.Sseq s' ts) T.Sskip tk)
with match_cont_exp : composite_env -> destination -> T.expr -> S.cont -> T.cont -> Prop :=
| match_Kwhile1: forall ce r s k s' a ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont_exp ce For_val a
        (S.Kwhile1 r s k)
        (T.Kseq (makeif a T.Sskip T.Sbreak)
          (T.Kseq ts (T.Kloop1 (T.Sseq s' ts) T.Sskip tk))).

FInduction match_cont_is_call_cont.
FProof.
- intros. fsimpl in *. contradiction.
Qed. FEnd match_cont_is_call_cont.

FInduction match_cont_call_cont.
FProof.
- intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_cont_call_cont.

Closing Fact match_cont_while2_inv :
  forall ce r s k tk,
  match_cont ce (S.Kwhile2 r s k) tk ->
  exists s' ts tk', tk = T.Kloop1 (T.Sseq s' ts) T.Sskip tk' /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact match_cont_exp_while1_inv :
  forall ce dst a r s k tk,
  match_cont_exp ce dst a (S.Kwhile1 r s k) tk ->
  exists s' ts tk', dst = For_val /\ tk = T.Kseq (makeif a T.Sskip T.Sbreak) (T.Kseq ts (T.Kloop1 (T.Sseq s' ts) T.Sskip tk'))
    /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_find_label with tr_find_label_ls.
FProof.
(* while *)
intros. apply tr_while_inv in TR; unpack TR; subst.
rename s' into sr. fsimpl.
exploit (H ce tge lbl (S.Kwhile2 e __i k)); eauto.
- fconstructor.
- do 3 fsimpl. rewrite (tr_find_label_if ce tge lbl _ _ TEMP0).
  destruct (S.find_label __i lbl (S.Kwhile2 e __i k)) as [[s' k'] | ].
  + intros [ts' [tk' [-> [B C]]]]. exists ts' tk'. auto.
  + intros ->. auto.
Qed. FEnd tr_find_label with tr_find_label_ls.

FRecursion measure_stmt.
Case _ := 0%nat.
FEnd measure_stmt.

FInduction sstep_simulation.
FProof.
all: intros; inv MS.
(* while *)
- apply tr_while_inv in TR; unpack TR; subst. inv TEMP0.
  eexists. split.
  + left. eapply plus_left. fconstructor.
    eapply star_left. fconstructor.
    apply push_seq. reflexivity. reflexivity.
  + rewrite Kseqlist_app. econstructor; eauto. simpl.
    fconstructor. econstructor; eauto.
(* while false *)
- apply match_cont_exp_while1_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. simpl. eapply plus_left. fconstructor.
    eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
    eapply star_two. fconstructor. apply T.step_break_loop1.
    reflexivity. reflexivity. reflexivity.
  + econstructor; eauto. fconstructor.
(* while true *)
- apply match_cont_exp_while1_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. simpl. eapply plus_left. fconstructor.
    eapply star_right. apply step_makeif with (v1 := v) (b := true); auto. fconstructor.
    reflexivity. reflexivity.
  + econstructor; eauto. fconstructor.
(* skip-or-continue while *)
- assert (ts = T.Sskip \/ ts = T.Scontinue).
  { destruct o; subst s0; [ apply tr_skip_inv in TR | apply tr_continue_inv in TR ]; auto. }
  apply match_cont_while2_inv in MK; unpack MK; subst.
  eexists. split.
  + left. eapply plus_two. apply T.step_skip_or_continue_loop1; auto.
    apply T.step_skip_loop2. reflexivity.
  + econstructor; eauto. fconstructor.
(* break while *)
- apply tr_break_inv in TR; apply match_cont_while2_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_break_loop1.
  + econstructor; eauto. fconstructor.
Qed. FEnd sstep_simulation.
FEnd SimplExpr_Swhile.

Trait SimplExpr_Sdowhile extends SimplExpr.
Family S extends C_Sdowhile. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Sdowhile e s1 :=
  (fun ce =>
    do s' <- transl_if e T.Sskip T.Sbreak ce;
    do ts1 <- transl_stmt s1 ce;
    ret (T.Sloop ts1 s')).
FEnd transl_stmt with transl_lblstmt.

FInductive tr_stmt: composite_env -> S.stmt -> T.stmt -> Prop :=
| tr_dowhile: forall ce r s1 s' ts1,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s1 ts1 ->
    tr_stmt ce (S.Sdowhile r s1)
            (T.Sloop ts1 s').

Closing Fact tr_dowhile_inv :
  forall ce r s1 ts,
  tr_stmt ce (S.Sdowhile r s1) ts ->
  exists s' ts1, ts = (T.Sloop ts1 s') /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s1 ts1
  by plain {intros *; intros H; inv H; eauto}.

FInductive match_cont : composite_env -> S.cont -> T.cont -> Prop :=
| match_Kdowhile1: forall ce r s k s' ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont ce (S.Kdowhile1 r s k)
                  (T.Kloop1 ts s' tk)
with match_cont_exp : composite_env -> destination -> T.expr -> S.cont -> T.cont -> Prop :=
| match_Kdowhile2: forall ce r s k s' a ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont_exp ce For_val a
      (S.Kdowhile2 r s k)
      (T.Kseq (makeif a T.Sskip T.Sbreak) (T.Kloop2 ts s' tk)).

FInduction match_cont_is_call_cont.
FProof.
- intros. fsimpl in *. contradiction.
Qed. FEnd match_cont_is_call_cont.

FInduction match_cont_call_cont.
FProof.
- intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_cont_call_cont.

Closing Fact match_cont_dowhile1_inv :
  forall ce r s k tk,
  match_cont ce (S.Kdowhile1 r s k) tk ->
  exists s' ts tk', tk = T.Kloop1 ts s' tk' /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact match_cont_exp_dowhile2_inv :
  forall ce dst a r s k tk,
  match_cont_exp ce dst a (S.Kdowhile2 r s k) tk ->
  exists s' ts tk', dst = For_val /\ tk = T.Kseq (makeif a T.Sskip T.Sbreak) (T.Kloop2 ts s' tk')
    /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_find_label with tr_find_label_ls.
FProof.
(* dowhile *)
intros. apply tr_dowhile_inv in TR; unpack TR; subst.
rename s' into sr. fsimpl.
exploit (H ce tge lbl (S.Kdowhile1 e __i k)); eauto.
- fconstructor.
- fsimpl. rewrite (tr_find_label_if ce tge lbl _ _ TEMP0).
  destruct (S.find_label __i lbl (S.Kdowhile1 e __i k)) as [[s' k'] | ].
  + intros [ts' [tk' [-> [B C]]]]. exists ts' tk'. auto.
  + intros ->. auto.
Qed. FEnd tr_find_label with tr_find_label_ls.

FRecursion measure_stmt.
Case _ := 0%nat.
FEnd measure_stmt.

FInduction sstep_simulation.
FProof.
all: intros; inv MS.
(* dowhile *)
- apply tr_dowhile_inv in TR; unpack TR; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_loop.
  + econstructor; eauto. fconstructor.
(* skip-or-continue dowhile *)
- assert (ts = T.Sskip \/ ts = T.Scontinue).
  { destruct o; subst s0; [ apply tr_skip_inv in TR | apply tr_continue_inv in TR ]; auto. }
  apply match_cont_dowhile1_inv in MK; unpack MK. inv TEMP; subst.
  eexists. split.
  + left. eapply plus_left. apply T.step_skip_or_continue_loop1; auto.
    apply push_seq. reflexivity.
  + rewrite Kseqlist_app. econstructor; eauto.
    fconstructor. econstructor; eauto.
(* dowhile false *)
- apply match_cont_exp_dowhile2_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. simpl. eapply plus_left. fconstructor.
    eapply star_right. apply step_makeif with (v1 := v) (b := false); auto. fconstructor.
    reflexivity. reflexivity.
  + econstructor; eauto. fconstructor.
(* dowhile true *)
- apply match_cont_exp_dowhile2_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. simpl. eapply plus_left. fconstructor.
    eapply star_right. apply step_makeif with (v1 := v) (b := true); auto. apply T.step_skip_loop2.
    reflexivity. reflexivity.
  + econstructor; eauto. fconstructor.
(* break dowhile *)
- apply tr_break_inv in TR; apply match_cont_dowhile1_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_break_loop1.
  + econstructor; eauto. fconstructor.
Qed. FEnd sstep_simulation.
FEnd SimplExpr_Sdowhile.

Trait SimplExpr_Sfor extends SimplExpr.
Family S extends C_Sfor. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Sfor s1 e2 s3 s4 :=
  (fun ce =>
    do ts1 <- transl_stmt s1 ce;
    do s' <- transl_if e2 T.Sskip T.Sbreak ce;
    do ts3 <- transl_stmt s3 ce;
    do ts4 <- transl_stmt s4 ce;
    if is_Sskip s1 then
      ret (T.Sloop (T.Sseq s' ts4) ts3)
    else
      ret (T.Sseq ts1 (T.Sloop (T.Sseq s' ts4) ts3))).
FEnd transl_stmt with transl_lblstmt.

FInductive tr_stmt: composite_env -> S.stmt -> T.stmt -> Prop :=
| tr_for_1: forall ce r s3 s4 s' ts3 ts4,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s3 ts3 ->
    tr_stmt ce s4 ts4 ->
    tr_stmt ce (S.Sfor S.Sskip r s3 s4)
            (T.Sloop (T.Sseq s' ts4) ts3)
| tr_for_2: forall ce s1 r s3 s4 s' ts1 ts3 ts4,
    tr_if ce r T.Sskip T.Sbreak s' ->
    s1 <> S.Sskip ->
    tr_stmt ce s1 ts1 ->
    tr_stmt ce s3 ts3 ->
    tr_stmt ce s4 ts4 ->
    tr_stmt ce (S.Sfor s1 r s3 s4)
            (T.Sseq ts1 (T.Sloop (T.Sseq s' ts4) ts3)).

Closing Fact tr_for_inv :
  forall ce s1 r s3 s4 ts,
  tr_stmt ce (S.Sfor s1 r s3 s4) ts ->
  (exists s' ts3 ts4, s1 = S.Sskip /\ ts = T.Sloop (T.Sseq s' ts4) ts3
    /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s3 ts3 /\ tr_stmt ce s4 ts4)
  \/ (exists s' ts1 ts3 ts4, s1 <> S.Sskip /\ ts = (T.Sseq ts1 (T.Sloop (T.Sseq s' ts4) ts3))
    /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s3 ts3 /\ tr_stmt ce s4 ts4)
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInductive match_cont : composite_env -> S.cont -> T.cont -> Prop :=
| match_Kfor3: forall ce r s3 s k ts3 s' ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s3 ts3 ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont ce (S.Kfor3 r s3 s k)
                  (T.Kloop1 (T.Sseq s' ts) ts3 tk)
| match_Kfor4: forall ce r s3 s k ts3 s' ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s3 ts3 ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont ce (S.Kfor4 r s3 s k)
                  (T.Kloop2 (T.Sseq s' ts) ts3 tk)
with match_cont_exp : composite_env -> destination -> T.expr -> S.cont -> T.cont -> Prop :=
| match_Kfor2: forall ce r s3 s k s' a ts3 ts tk,
    tr_if ce r T.Sskip T.Sbreak s' ->
    tr_stmt ce s3 ts3 ->
    tr_stmt ce s ts ->
    match_cont ce k tk ->
    match_cont_exp ce For_val a
      (S.Kfor2 r s3 s k)
      (T.Kseq (makeif a T.Sskip T.Sbreak)
        (T.Kseq ts (T.Kloop1 (T.Sseq s' ts) ts3 tk))).

FInduction match_cont_is_call_cont.
FProof.
all: intros; fsimpl in *; contradiction.
Qed. FEnd match_cont_is_call_cont.

FInduction match_cont_call_cont.
FProof.
all: intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_cont_call_cont.

Closing Fact match_cont_for3_inv :
  forall ce r s3 s k tk,
  match_cont ce (S.Kfor3 r s3 s k) tk ->
  exists ts3 s' ts tk', tk = T.Kloop1 (T.Sseq s' ts) ts3 tk' /\ tr_if ce r T.Sskip T.Sbreak s'
    /\ tr_stmt ce s3 ts3 /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact match_cont_for4_inv :
  forall ce r s3 s k tk,
  match_cont ce (S.Kfor4 r s3 s k) tk ->
  exists ts3 s' ts tk', tk = T.Kloop2 (T.Sseq s' ts) ts3 tk' /\ tr_if ce r T.Sskip T.Sbreak s'
    /\ tr_stmt ce s3 ts3 /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact match_cont_exp_for2_inv :
  forall ce dst a r s3 s k tk,
  match_cont_exp ce dst a (S.Kfor2 r s3 s k) tk ->
  exists ts3 s' ts tk', dst = For_val /\ tk = T.Kseq (makeif a T.Sskip T.Sbreak) (T.Kseq ts (T.Kloop1 (T.Sseq s' ts) ts3 tk'))
    /\ tr_if ce r T.Sskip T.Sbreak s' /\ tr_stmt ce s3 ts3 /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_find_label with tr_find_label_ls.
FProof.
intros. apply tr_for_inv in TR as [TR|TR]; unpack TR; subst; rename s' into sr.
(* for skip *)
- (* fsimpl not working? *)
  rewrite S.find_label_find_label_ls_Sfor_eq. unfold S.find_label_find_label_lsSfor.
  rewrite T.find_label_find_label_ls_Sloop_eq. unfold T.find_label_find_label_lsSloop.
  rewrite T.find_label_find_label_ls_Sseq_eq. unfold T.find_label_find_label_lsSseq.
  rewrite (tr_find_label_if ce tge lbl _ _ TEMP1).
  exploit (H1 ce tge lbl (S.Kfor3 e __i0 __i1 k)); eauto.
  + fconstructor.
  + destruct (S.find_label __i1 lbl (S.Kfor3 e __i0 __i1 k)) as [[s' k'] | ].
    * intros [ts' [tk' [-> [B C]]]]. fsimpl. exists ts' tk'. auto.
    * intros ->. fsimpl.
      exploit (H0 ce tge lbl (S.Kfor4 e __i0 __i1 k)); eauto. fconstructor.
(* for not skip *)
- rewrite S.find_label_find_label_ls_Sfor_eq. unfold S.find_label_find_label_lsSfor.
  rewrite T.find_label_find_label_ls_Sseq_eq. unfold T.find_label_find_label_lsSseq.
  rewrite T.find_label_find_label_ls_Sloop_eq. unfold T.find_label_find_label_lsSloop.
  rewrite T.find_label_find_label_ls_Sseq_eq. unfold T.find_label_find_label_lsSseq.
  rewrite (tr_find_label_if ce tge lbl _ _ TEMP1).
  exploit (H ce tge lbl (S.Kseq (S.Sfor S.Sskip e __i0 __i1) k)); eauto.
  + fconstructor. fconstructor.
  + destruct (S.find_label __i lbl (S.Kseq (S.Sfor S.Sskip e __i0 __i1) k)) as [[s' k'] | ].
    * intros [ts' [tk' [-> [B C]]]]. exists ts' tk'. auto.
    * intros ->.
    { exploit (H1 ce tge lbl (S.Kfor3 e __i0 __i1 k)); eauto.
      - fconstructor.
      - destruct (S.find_label __i1 lbl (S.Kfor3 e __i0 __i1 k)) as [[s' k'] | ].
        + intros [ts' [tk' [-> [B C]]]]. exists ts' tk'. auto.
        + intros ->.
          exploit (H0 ce tge lbl (S.Kfor4 e __i0 __i1 k)); eauto. fconstructor. }
Qed. FEnd tr_find_label with tr_find_label_ls.

FRecursion measure_stmt.
Case _ := 0%nat.
FEnd measure_stmt.

FInduction sstep_simulation.
FProof.
all: intros; inv MS.
(* for start *)
- apply tr_for_inv in TR as [TR|TR]; unpack TR; subst; try congruence.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto. fconstructor. fconstructor.
(* for *)
- apply tr_for_inv in TR as [TR|TR]; unpack TR; subst; try congruence. inv TEMP1.
  eexists. split.
  + left. eapply plus_left. apply T.step_loop.
    eapply star_left. fconstructor. apply push_seq.
    reflexivity. reflexivity.
  + rewrite Kseqlist_app. econstructor; eauto. simpl. fconstructor. econstructor; eauto.
(* for false *)
- apply match_cont_exp_for2_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. simpl. eapply plus_left. fconstructor.
    eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
    eapply star_two. fconstructor. apply T.step_break_loop1.
    reflexivity. reflexivity. reflexivity.
  + econstructor; eauto. fconstructor.
(* for true *)
- apply match_cont_exp_for2_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. simpl. eapply plus_left. fconstructor.
    eapply star_right. apply step_makeif with (v1 := v) (b := true); auto. fconstructor.
    reflexivity. reflexivity.
  + econstructor; eauto. fconstructor.
(* skip-or-continue for3 *)
- assert (ts = T.Sskip \/ ts = T.Scontinue).
  { destruct o; subst x; [ apply tr_skip_inv in TR | apply tr_continue_inv in TR ]; auto. }
  apply match_cont_for3_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_skip_or_continue_loop1; auto.
  + econstructor; eauto. fconstructor.
(* break for3 *)
- apply tr_break_inv in TR; apply match_cont_for3_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_break_loop1.
  + econstructor; eauto. fconstructor.
(* skip for4 *)
- apply tr_skip_inv in TR; apply match_cont_for4_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_skip_loop2.
  + econstructor; eauto. fconstructor.
Qed. FEnd sstep_simulation.
FEnd SimplExpr_Sfor.

Family SimplExpr extends
  SimplExpr_Swhile,
  SimplExpr_Sdowhile,
  SimplExpr_Sfor.
FEnd SimplExpr.

FEnd Comp_Loops.


Trait Comp_Builtin extends Base.

Family C.
FInductive expr : Type :=
| Ebuiltin : external_function -> list type -> exprlist -> type -> expr.

FRecursion typeof.
Case Ebuiltin ef ts es ty := ty.
FEnd typeof.

FRecursion simple.
Case _ := false.
FEnd simple.

Inherit eval_simple_rvalue.

MetaData eval_simple_list.
Inductive eval_simple_list: genv -> env -> mem -> exprlist -> list type -> list val -> Prop :=
  | esrl_nil: forall ge e m,
      eval_simple_list ge e m Enil nil nil
  | esrl_cons: forall ge e m r rl ty tyl v vl v',
      eval_simple_rvalue ge e m r v' -> sem_cast v' (typeof r) ty m = Some v ->
      eval_simple_list ge e m rl tyl vl ->
      eval_simple_list ge e m (Econs r rl) (ty :: tyl) (v :: vl).
FEnd eval_simple_list.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_builtin: forall k C ef tyargs ty,
    leftcontextlist k C ->
    leftcontext k RV (fun x => Ebuiltin ef tyargs (C x) ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f C ef tyargs rargs ty k e m vargs t vres m',
    leftcontext RV RV C ->
    eval_simple_list ge e m rargs tyargs vargs ->
    external_call ef (Genv.to_senv (genv_genv ge)) vargs m t vres m' ->
    estep ge (ExprState f (C (Ebuiltin ef tyargs rargs ty)) k e m)
        t (ExprState f (C (Eval vres ty)) k e m').
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Sbuiltin: option ident -> external_function -> list type -> list expr -> stmt. (* builtin invocation *)

Inherit bind_parameters.

FDefinition set_opttemp := fun (optid: option ident) (v: val) (le: temp_env) =>
  match optid with
  | None => le
  | Some id => PTree.set id v le
  end.

Inherit eval_expr.

MetaData eval_exprlist.
Inductive eval_exprlist : genv -> env -> temp_env -> mem -> list expr -> list type -> list val -> Prop :=
  | eval_Enil: forall ge e le m,
      eval_exprlist ge e le m nil nil nil
  | eval_Econs: forall ge e le m a bl ty tyl v1 v2 vl,
      eval_expr ge e le m a v1 ->
      sem_cast v1 (typeof a) ty m = Some v2 ->
      eval_exprlist ge e le m bl tyl vl ->
      eval_exprlist ge e le m (a :: bl) (ty :: tyl) (v2 :: vl).
FEnd eval_exprlist.

FRecursion find_label with find_label_ls.
Case _ := (fun lbl k => None).
FEnd find_label with find_label_ls.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_builtin: forall ge f optid ef tyargs al k e le m vargs t vres m',
    eval_exprlist ge e le m al tyargs vargs ->
    external_call ef (Genv.to_senv (genv_genv ge)) vargs m t vres m' ->
    step ge (State f (Sbuiltin optid ef tyargs al) k e le m)
        t (State f Sskip k e (set_opttemp optid vres le) m').
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.

FRecursion transl_expr with transl_exprlist.
Case Ebuiltin ef tyargs rl ty :=
  (fun ce dst =>
     do (sl, al) <- transl_exprlist rl ce;
      match dst with
      | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
          do t <- gensym ty;
          ret (finish dst (sl ++ T.Sbuiltin (Some t) ef tyargs al :: nil)
                          (T.Etempvar t ty))
      | self__SimplExpr.For_effects =>
          ret (sl ++ T.Sbuiltin None ef tyargs al :: nil, dummy_expr)
      end).
FEnd transl_expr with transl_exprlist.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_builtin_effects: forall ce le ef tyargs el ty sl al tmp1 any tmp,
    tr_exprlist ce le el sl al tmp1 ->
    incl tmp1 tmp ->
    tr_expr ce le For_effects (S.Ebuiltin ef tyargs el ty)
                (sl ++ T.Sbuiltin None ef tyargs al :: nil)
                any tmp
| tr_builtin_val: forall ce le dst ef tyargs el ty sl al tmp1 t tmp,
    dst <> For_effects ->
    tr_exprlist ce le el sl al tmp1 ->
    In t tmp -> incl tmp1 tmp ->
    tr_expr ce le dst (S.Ebuiltin ef tyargs el ty)
                (sl ++ T.Sbuiltin (Some t) ef tyargs al :: final dst (T.Etempvar t ty))
                (T.Etempvar t ty) tmp.

Closing Fact tr_builtin_inv :
  forall ce le dst ef tyargs el ty sl a tmp,
  tr_expr ce le dst (S.Ebuiltin ef tyargs el ty) sl a tmp ->
  (exists sl' al tmp1, dst = For_effects /\ sl = sl' ++ T.Sbuiltin None ef tyargs al :: nil
    /\ tr_exprlist ce le el sl' al tmp1 /\ incl tmp1 tmp)
  \/ (exists sl' al tmp1 t, dst <> For_effects /\ sl = sl' ++ T.Sbuiltin (Some t) ef tyargs al :: final dst (T.Etempvar t ty)
    /\ a = T.Etempvar t ty /\ tr_exprlist ce le el sl' al tmp1 /\ In t tmp /\ incl tmp1 tmp)
  by plain {intros *; intros H; inv H;
            [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
all: intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
all: intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

Inherit comp_env_preserved.
FLemma senv_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  Senv.equiv (S.genv_genv ge) (T.genv_genv tge).
FProofLemma.
intros. subst. simpl. apply (Genv.senv_match (proj1 H)).
Qed. CloseFLemma.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
all: intros; fsimpl in *; discriminate.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

Inherit tr_simple_rvalue.

FInduction tr_simple_exprlist
  about tr_exprlist
  motive (fun ce le rl sl al tmps (_ : tr_exprlist ce le rl sl al tmps) =>
    forall ge prog tprog tge, match_prog prog tprog ->
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall e m tyl vl,
    S.eval_simple_list ge e m rl tyl vl ->
    sl = nil /\ T.eval_exprlist tge e le m al tyl vl).
FProof.
- intros. split. auto. inv H2.
  + constructor.
  + (* fdiscriminate. *) apply cheat.
- intros. inv H3.
  + (* fdiscriminate. *) apply cheat.
  + (* finjection H4. *) assert (r = e1 /\ rl = el2) as [] by apply cheat; clear H4; subst.
    exploit tr_simple_rvalue; eauto. intros [A [B C]].
    exploit H; eauto. intros [D E].
    split. subst; auto. econstructor; eauto. congruence.
Qed. FEnd tr_simple_exprlist.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
(* builtin *)
intros. apply tr_builtin_inv in H0 as [H0|H0]; unpack H0; subst.
(* for effects *)
- exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + rewrite Q, app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2').
    rewrite app_assoc. fconstructor.
(* for val *)
- exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + rewrite Q, app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2').
    rewrite app_assoc. fconstructor.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
all: intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Ebuiltin ef ts rl ty := (Datatypes.S(esizelist rl)).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FInduction estep_simulation.
FProof.
(* builtin *)
intros; inv MS.
exploit tr_top_leftcontext; eauto. clear TR.
intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
inv P.
- (* fdiscriminate. *) apply cheat.
- apply tr_builtin_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_exprlist; eauto. intros [SL EV].
    subst. simpl Kseqlist.
    eexists. split.
    * left. eapply plus_left. fconstructor.
      apply star_one. fconstructor.
      eapply external_call_symbols_preserved; eauto. apply (Genv.senv_match (proj1 H)).
      reflexivity.
    * econstructor; eauto.
      change sl2 with (nil ++ sl2). apply S. fconstructor. simpl; auto. do 2 fsimpl; auto.
  (* for val *)
  + exploit tr_simple_exprlist; eauto. intros [SL EV].
    subst. simpl Kseqlist.
    eexists. split.
    * left. eapply plus_left. fconstructor.
      apply star_one. fconstructor.
      eapply external_call_symbols_preserved; eauto. apply (Genv.senv_match (proj1 H)).
      reflexivity.
    * econstructor; eauto.
      change sl2 with (nil ++ sl2). apply S.
      apply tr_val_gen.
      -- fsimpl. auto.
      -- intros. fconstructor. rewrite H0 by auto. simpl. apply PTree.gss.
      -- intros. simpl. apply PTree.gso. congruence.
      -- do 2 fsimpl; auto.
Qed. FEnd estep_simulation.
FEnd SimplExpr.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Trait C_Ederef extends C.
FInductive expr : Type :=
| Ederef : expr -> type -> expr
| Eloc : block -> ptrofs -> bitfield -> type -> expr.

FRecursion typeof.
Case Ederef e ty := ty.
Case Eloc a b c ty := ty.
FEnd typeof.

Inherit blocks_of_env.
MetaData deref_loc.
Inductive deref_loc (ge: genv) (ty: type) (m: mem) (b: block) (ofs: ptrofs) :
                                       bitfield -> trace -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ge ty m b ofs Full E0 v
  | deref_loc_volatile: forall chunk t v,
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_load ge chunk m b ofs t v ->
      deref_loc ge ty m b ofs Full t v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ge ty m b ofs Full E0 (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ge ty m b ofs Full E0 (Vptr b ofs)
  | deref_loc_bitfield: forall sz sg pos width v,
      load_bitfield ty sz sg pos width m (Vptr b ofs) v ->
      deref_loc ge ty m b ofs (Bits sz sg pos width) E0 v.
FEnd deref_loc.

FRecursion simple.
Case Ederef e ty := (simple e).
Case Eloc a b c ty := true.
FEnd simple.

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
with eval_simple_lvalue: genv -> env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| esl_loc: forall ge e m b ofs ty bf,
    eval_simple_lvalue ge e m (Eloc b ofs bf ty) b ofs bf
| esl_deref: forall ge e m r ty b ofs,
    eval_simple_rvalue ge e m r (Vptr b ofs) ->
    eval_simple_lvalue ge e m (Ederef r ty) b ofs Full.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_deref: forall k C ty,
    leftcontext k RV C -> leftcontext k LV (fun x => Ederef (C x) ty).
FEnd C_Ederef.

Trait C_Evar extends C_Ederef.
(* Evar defined in Base *)

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
with eval_simple_lvalue: genv -> env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| esl_var_local: forall ge e m x ty b,
    e!x = Some(b, ty) ->
    eval_simple_lvalue ge e m (Evar x ty) b Ptrofs.zero Full
| esl_var_global: forall ge e m x ty b,
    e!x = None ->
    Genv.find_symbol (genv_genv ge) x = Some b ->
    eval_simple_lvalue ge e m (Evar x ty) b Ptrofs.zero Full.
FEnd C_Evar.

Trait C_Eassignop extends C_Ederef.
FInductive expr : Type :=
| Eassignop : Cop.binary_operation -> expr -> expr -> type -> type -> expr.

FRecursion typeof.
Case Eassignop op e0 e1 ty' ty := ty.
FEnd typeof.

FRecursion simple.
Case _ := false.
FEnd simple.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_assignop_left: forall k C op e2 tyres ty,
    leftcontext k LV C -> leftcontext k RV (fun x => Eassignop op (C x) e2 tyres ty)
| lctx_assignop_right: forall k C op e1 tyres ty,
    simple e1 = true -> leftcontext k RV C ->
    leftcontext k RV (fun x => Eassignop op e1 (C x) tyres ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_assignop: forall ge f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t,
    leftcontext RV RV C ->
    eval_simple_lvalue ge e m l b ofs bf ->
    deref_loc ge (typeof l) m b ofs bf t1 v1 ->
    eval_simple_rvalue ge e m r v2 ->
    sem_binary_operation (genv_cenv ge) op v1 (typeof l) v2 (typeof r) m = Some v3 ->
    sem_cast v3 tyres (typeof l) m = Some v4 ->
    assign_loc ge (typeof l) m b ofs bf v4 t2 m' v' ->
    ty = typeof l ->
    t = t1 ** t2 ->
    estep ge (ExprState f (C (Eassignop op l r tyres ty)) k e m)
        t (ExprState f (C (Eval v' ty)) k e m')
| step_assignop_stuck: forall ge f C op l r tyres ty k e m b ofs bf v1 v2 t,
    leftcontext RV RV C ->
    eval_simple_lvalue ge e m l b ofs bf ->
    deref_loc ge (typeof l) m b ofs bf t v1 ->
    eval_simple_rvalue ge e m r v2 ->
    match sem_binary_operation (genv_cenv ge) op v1 (typeof l) v2 (typeof r) m with
    | None => True
    | Some v3 =>
        match sem_cast v3 tyres (typeof l) m with
        | None => True
        | Some v4 => forall t2 m' v', ~(assign_loc ge (typeof l) m b ofs bf v4 t2 m' v')
        end
    end ->
    ty = typeof l ->
    estep ge (ExprState f (C (Eassignop op l r tyres ty)) k e m)
        t Stuckstate.
FEnd C_Eassignop.

Trait C_Epostincr extends C_Ederef.
FInductive expr : Type :=
  | Epostincr : incr_or_decr -> expr -> type -> expr.

FRecursion typeof.
Case Epostincr a b ty := ty.
FEnd typeof.

FRecursion simple.
Case _ := false.
FEnd simple.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_postincr: forall k C id ty,
    leftcontext k LV C -> leftcontext k RV (fun x => Epostincr id (C x) ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_postincr: forall ge f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t,
      leftcontext RV RV C ->
      eval_simple_lvalue ge e m l b ofs bf ->
      deref_loc ge ty m b ofs bf t1 v1 ->
      sem_incrdecr (genv_cenv ge) id v1 ty m = Some v2 ->
      sem_cast v2 (incrdecr_type ty) ty m = Some v3 ->
      assign_loc ge ty m b ofs bf v3 t2 m' v' ->
      ty = typeof l ->
      t = t1 ** t2 ->
      estep ge (ExprState f (C (Epostincr id l ty)) k e m)
          t (ExprState f (C (Eval v1 ty)) k e m')
| step_postincr_stuck: forall ge f C id l ty k e m b ofs bf v1 t,
    leftcontext RV RV C ->
    eval_simple_lvalue ge e m l b ofs bf ->
    deref_loc ge ty m b ofs bf t v1 ->
    match sem_incrdecr (genv_cenv ge) id v1 ty m with
    | None => True
    | Some v2 =>
        match sem_cast v2 (incrdecr_type ty) ty m with
        | None => True
        | Some v3 => forall t2 m' v', ~(assign_loc ge (typeof l) m b ofs bf v3 t2 m' v')
        end
    end ->
    ty = typeof l ->
    estep ge (ExprState f (C (Epostincr id l ty)) k e m)
        t Stuckstate.
FEnd C_Epostincr.

Trait C_Eaddrof extends C_Ederef.
FInductive expr : Type :=
| Eaddrof : expr -> type -> expr.

FRecursion typeof.
Case Eaddrof e ty := ty.
FEnd typeof.

FRecursion simple.
Case Eaddrof e ty := (simple e).
FEnd simple.

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
| esr_addrof: forall ge e m b ofs l ty,
    eval_simple_lvalue ge e m l b ofs Full ->
    eval_simple_rvalue ge e m (Eaddrof l ty) (Vptr b ofs).

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_addrof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eaddrof (C x) ty).
FEnd C_Eaddrof.

Trait C_Evalof extends C_Ederef.
FInductive expr : Type :=
| Evalof : expr -> type -> expr. (* l-value used as a r-value *)

FRecursion typeof.
Case Evalof e ty := ty.
FEnd typeof.

FRecursion simple.
Case Evalof e ty := (simple e && negb(type_is_volatile (typeof e))).
FEnd simple.

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
| esr_rvalof: forall ge e m b ofs bf l ty v,
    eval_simple_lvalue ge e m l b ofs bf ->
    ty = typeof l -> type_is_volatile ty = false ->
    deref_loc ge ty m b ofs bf E0 v ->
    eval_simple_rvalue ge e m (Evalof l ty) v.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_rvalof: forall k C ty,
    leftcontext k LV C -> leftcontext k RV (fun x => Evalof (C x) ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_rvalof_volatile: forall ge f C l ty k e m b ofs bf t v,
    leftcontext RV RV C ->
    eval_simple_lvalue ge e m l b ofs bf ->
    deref_loc ge ty m b ofs bf t v ->
    ty = typeof l -> type_is_volatile ty = true ->
    estep ge (ExprState f (C (Evalof l ty)) k e m)
        t (ExprState f (C (Eval v ty)) k e m).
FEnd C_Evalof.

Trait C_Eassign extends C_Ederef.
FInductive expr : Type :=
| Eassign : expr -> expr -> type -> expr. (* assignment l = r *)

FRecursion typeof.
Case Eassign e1 e2 ty := ty.
FEnd typeof.

FRecursion simple.
Case _ := false.
FEnd simple.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_assign_left: forall k C e2 ty,
    leftcontext k LV C -> leftcontext k RV (fun x => Eassign (C x) e2 ty)
| lctx_assign_right: forall k C e1 ty,
    simple e1 = true -> leftcontext k RV C ->
    leftcontext k RV (fun x => Eassign e1 (C x) ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_assign: forall ge f C l r ty k e m b ofs bf v v1 t m' v',
    leftcontext RV RV C ->
    eval_simple_lvalue ge e m l b ofs bf ->
    eval_simple_rvalue ge e m r v ->
    sem_cast v (typeof r) (typeof l) m = Some v1 ->
    assign_loc ge (typeof l) m b ofs bf v1 t m' v' ->
    ty = typeof l ->
    estep ge (ExprState f (C (Eassign l r ty)) k e m)
        t (ExprState f (C (Eval v' ty)) k e m').
FEnd C_Eassign.

Family C extends
  C_Eassign,
  C_Evalof,
  C_Ederef,
  C_Eaddrof,
  C_Eassignop,
  C_Epostincr.
FEnd C.

Trait Clight_Ederef extends Clight.
FInductive expr : Type :=
| Ederef: expr -> type -> expr. (* pointer dereference (unary *)

FRecursion typeof.
Case Ederef i t := t.
FEnd typeof.

Inherit temp_env.
MetaData deref_loc.
Inductive deref_loc (ge: genv) (ty: type) (m: mem) (b: block) (ofs: ptrofs) :
                                             bitfield -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ge ty m b ofs Full v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ge ty m b ofs Full (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ge ty m b ofs Full (Vptr b ofs)
  | deref_loc_bitfield: forall sz sg pos width v,
      load_bitfield ty sz sg pos width m (Vptr b ofs) v ->
      deref_loc ge ty m b ofs (Bits sz sg pos width) v.
FEnd deref_loc.

FInductive eval_expr: genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Elvalue: forall ge e le m a loc ofs bf v,
    eval_lvalue ge e le m a loc ofs bf ->
    deref_loc ge (typeof a) m loc ofs bf v ->
    eval_expr ge e le m a v
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| eval_Ederef: forall ge e le m a ty l ofs,
    eval_expr ge e le m a (Vptr l ofs) ->
    eval_lvalue ge e le m (Ederef a ty) l ofs Full.

Closing Fact eval_lvalue_deref_inv :
  forall ge e le m a ty l ofs bf,
  eval_lvalue ge e le m (Ederef a ty) l ofs bf ->
  bf = Full /\ eval_expr ge e le m a (Vptr l ofs)
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.
FEnd Clight_Ederef.

Trait Clight_Evar extends Clight_Ederef.
FInductive expr : Type :=
| Evar: ident -> type -> expr. (* variable *)

FRecursion typeof.
Case Evar i t := t.
FEnd typeof.

FInductive eval_expr: genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| eval_Evar_local: forall ge e le m id l ty,
    e!id = Some(l, ty) ->
    eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Full
| eval_Evar_global: forall ge e le m id l ty,
    e!id = None ->
    Genv.find_symbol (genv_genv ge) id = Some l ->
    eval_lvalue ge e le m (Evar id ty) l Ptrofs.zero Full.
FEnd Clight_Evar.

Trait Clight_Eaddrof extends Clight_Ederef.
FInductive expr : Type :=
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Eaddrof e t := t.
FEnd typeof.

FInductive eval_expr: genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
| eval_Eaddrof: forall ge e le m a ty loc ofs,
    eval_lvalue ge e le m a loc ofs Full ->
    eval_expr ge e le m (Eaddrof a ty) (Vptr loc ofs)
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=.

Closing Fact eval_addrof_inv :
  forall ge e le m a ty v,
  eval_expr ge e le m (Eaddrof a ty) v ->
  exists loc ofs, v = Vptr loc ofs /\ eval_lvalue ge e le m a loc ofs Full
  by plain {intros *; intros H; inv H; [ eauto | inv H0 ]}.
FEnd Clight_Eaddrof.

Trait Clight_Sassign extends Clight, Clight_Ederef.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)

FRecursion find_label with find_label_ls.
Case _ := (fun lbl k => None).
FEnd find_label with find_label_ls.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_assign: forall ge f a1 a2 k e le m loc ofs bf v2 v m',
    eval_lvalue ge e le m a1 loc ofs bf ->
    eval_expr ge e le m a2 v2 ->
    sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
    assign_loc (genv_cenv ge) (typeof a1) m loc ofs bf v m' ->
    step ge (State f (Sassign a1 a2) k e le m)
      E0 (State f Sskip k e le m').
FEnd Clight_Sassign.

Family Clight extends
  Clight_Ederef,
  Clight_Evar,
  Clight_Sassign,
  Clight_Eaddrof.
FEnd Clight.

Trait SimplExpr_Ederef extends SimplExpr.
Family S extends C_Ederef. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

Closing Fact eval_simpl_lvalue_none :
  forall ge e le m a loc ofs bf,
  T.eval_lvalue ge e le m a loc ofs bf -> eval_simpl_expr a = None
  by {intros *; intros H; inv H; reflexivity}.

FRecursion Ederef'
  about T.expr
  motive (fun (_ : T.expr) => type -> T.expr)
  by _rect.
Case Econst_int i ty := (fun t => T.Ederef (T.Econst_int i ty) t).
Case Econst_float f ty := (fun t => T.Ederef (T.Econst_float f ty) t).
Case Econst_single s ty := (fun t => T.Ederef (T.Econst_single s ty) t).
Case Econst_long l ty := (fun t => T.Ederef (T.Econst_long l ty) t).
Case Etempvar v ty := (fun t => T.Ederef (T.Etempvar v ty) t).
Case Esizeof ty' ty := (fun t => T.Ederef (T.Esizeof ty' ty) t).
Case Ealignof ty' ty := (fun t => T.Ederef (T.Ealignof ty' ty) t).
Case Ecast e ty := (fun t => T.Ederef (T.Ecast e ty) t).
Case Eunop op e ty := (fun t => T.Ederef (T.Eunop op e ty) t).
Case Ebinop op e0 e1 ty := (fun t => T.Ederef (T.Ebinop op e0 e1 ty) t).
Case Ederef i ty := (fun t => T.Ederef (T.Ederef i ty) t).
Case Eaddrof a ty := (fun t => if type_eq t (T.typeof a) then a else T.Ederef (T.Eaddrof a ty) t).
Case Evar i ty := (fun t => T.Ederef (T.Evar i ty) t).
FEnd Ederef'.

FRecursion transl_expr with transl_exprlist.
Case Eloc b ofs bf ty :=
  (fun ce dst => error (msg "SimplExpr.transl_expr: Eloc")).
Case Ederef r ty :=
  (fun ce dst => do (sl, a) <- transl_expr r ce For_val;
    ret (finish dst sl (Ederef' a ty))).
FEnd transl_expr with transl_exprlist.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_deref: forall ce le dst e1 ty sl1 a1 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Ederef e1 ty)
            (sl1 ++ final dst (Ederef' a1 ty)) (Ederef' a1 ty) tmp.

Closing Fact tr_loc_inv :
  forall ce le dst b ofs bf ty sl a tmp,
  ~ tr_expr ce le dst (S.Eloc b ofs bf ty) sl a tmp
  by plain {intros *; intros H; inv H}.

Closing Fact tr_deref_inv :
  forall ce le dst e1 ty sl a tmp,
  tr_expr ce le dst (S.Ederef e1 ty) sl a tmp ->
  exists sl1 a1, sl = sl1 ++ final dst (Ederef' a1 ty) /\ a = Ederef' a1 ty
    /\ tr_expr ce le For_val e1 sl1 a1 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInduction eval_Ederef'
  about T.expr
  motive (fun (a : T.expr) =>
    forall ge e le m t l ofs,
    T.eval_expr ge e le m a (Vptr l ofs) ->
    T.eval_lvalue ge e le m (Ederef' a t) l ofs Full).
FProof.
all: intros; fsimpl; auto using T.eval_Ederef.
destruct (type_eq t0 (T.typeof __i)); auto using T.eval_Ederef.
apply T.eval_addrof_inv in H0; unpack H0. injection TEMP; intros; subst; auto.
Qed. FEnd eval_Ederef'.

FInduction typeof_Ederef'
  about T.expr
  motive (fun (a : T.expr) =>
    forall t, T.typeof (Ederef' a t) = t).
FProof.
all: intros; fsimpl; fsimpl; auto.
destruct (type_eq t0 (T.typeof __i)); fsimpl; auto.
Qed. FEnd typeof_Ederef'.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil)
  by (intros; destruct H; subst dst; auto).
intros; fsimpl in *. rewrite H; auto. simpl; auto.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction tr_simple_rvalue
  about S.eval_simple_rvalue
  motive (fun ge e m r v (_ : S.eval_simple_rvalue ge e m r v) =>
    forall prog tprog tge, match_prog prog tprog ->
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall ce le dst sl a tmps,
    tr_expr ce le dst r sl a tmps ->
    match dst with
    | self__SimplExpr_Ederef.For_val => sl = nil /\ S.typeof r = T.typeof a /\ T.eval_expr tge e le m a v
    | self__SimplExpr_Ederef.For_effects => sl = nil
    | self__SimplExpr_Ederef.For_set sd =>
        exists b, sl = do_set sd b
               /\ S.typeof r = T.typeof b
               /\ T.eval_expr tge e le m b v
    end)
with tr_simple_lvalue
  about S.eval_simple_lvalue
  motive (fun ge e m l b ofs bf (_ : S.eval_simple_lvalue ge e m l b ofs bf) =>
    forall prog tprog tge, match_prog prog tprog ->
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall ce le sl a tmps,
    tr_expr ce le For_val l sl a tmps ->
    sl = nil /\ S.typeof l = T.typeof a /\ T.eval_lvalue tge e le m a b ofs bf).
FProof.
(* loc *)
- intros. fsimpl. apply tr_loc_inv in H2 as [].
(* deref *)
- intros. fsimpl.
  apply tr_deref_inv in H3; unpack H3; subst sl a; simpl.
  exploit H; eauto. intros [A [B C]]. subst sl1.
  split; auto. split. rewrite typeof_Ederef'; auto. apply eval_Ederef'; auto.
Qed. FEnd tr_simple_rvalue with tr_simple_lvalue.

FInduction typeof_context
  about S.leftcontext
  motive (fun k1 k2 C (_ : S.leftcontext k1 k2 C) =>
    forall e1 e2, S.typeof e1 = S.typeof e2 ->
    S.typeof (C e1) = S.typeof (C e2)).
FProof.
all: intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
intros. apply tr_deref_inv in H0; unpack H0; subst.
exploit H; eauto.
intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
- rewrite Q, app_assoc. eauto.
- auto.
- intros. rewrite app_assoc. fconstructor.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInduction eval_simpl_expr_sound.
FProof.
all: intros; fsimpl; auto.
- apply eval_simpl_lvalue_none in __i as ->. auto.
Qed. FEnd eval_simpl_expr_sound.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Eloc a b c ty := 1%nat.
Case Ederef e ty := (Datatypes.S(esize e)).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.
FEnd SimplExpr_Ederef.

Trait SimplExpr_Evar extends SimplExpr, SimplExpr_Ederef.
Family S extends C_Evar. FEnd S.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_var: forall ce le dst id ty tmp,
    tr_expr ce le dst (S.Evar id ty)
            (final dst (T.Evar id ty)) (T.Evar id ty) tmp.

Closing Fact tr_var_inv :
  forall ce le dst id ty sl a tmp,
  tr_expr ce le dst (S.Evar id ty) sl a tmp ->
  sl = final dst (T.Evar id ty) /\ a = T.Evar id ty
  by plain {intros *; intros H; inv H; auto}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

Inherit comp_env_preserved.
FLemma symbols_preserved:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall (s: ident), Genv.find_symbol (T.genv_genv tge) s = Genv.find_symbol (S.genv_genv ge) s.
FProofLemma.
intros. subst. simpl. apply (Genv.find_symbol_match (proj1 H)).
Qed. CloseFLemma.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil)
  by (intros; destruct H; subst dst; auto).
intros; fsimpl in *; auto.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction tr_simple_rvalue with tr_simple_lvalue.
FProof.
(* var local *)
- intros. apply tr_var_inv in H2; unpack H2; subst sl a.
  repeat split. do 2 fsimpl; auto. apply T.eval_Evar_local; auto.
(* var global *)
- intros. apply tr_var_inv in H2; unpack H2; subst sl a.
  repeat split. do 2 fsimpl; auto. apply T.eval_Evar_global; auto.
  erewrite symbols_preserved; eauto.
Qed. FEnd tr_simple_rvalue with tr_simple_lvalue.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.
FEnd SimplExpr_Evar.

Trait SimplExpr_Eassign extends SimplExpr, SimplExpr_Ederef.
Family S extends C_Eassign. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

FRecursion is_bitfield_access about T.expr motive (fun (_ : T.expr) => composite_env -> mon bitfield) by _rect.
Case _ := (fun ce => ret Full).
FEnd is_bitfield_access.

FDefinition chunk_for_volatile_type : type -> bitfield -> option memory_chunk := fun ty bf =>
  if type_is_volatile ty then
    match access_mode ty with
    | By_value chunk =>
        match bf with
        | Full => Some chunk
        | Bits _ _ _ _ => None
        end
    | _ => None
    end
  else None.

FDefinition make_assign : bitfield -> T.expr -> T.expr -> T.stmt := fun bf l r =>
  match chunk_for_volatile_type (T.typeof l) bf with
  | None =>
      T.Sassign l r
  | Some chunk =>
      let ty := T.typeof l in
      let typtr := Tpointer ty noattr in
      T.Sbuiltin None (EF_vstore chunk) (typtr :: (ty :: nil))
                    (T.Eaddrof l typtr :: r :: nil)
  end.

FDefinition make_normalize := fun (sz: intsize) (sg: signedness) (width: Z) (r: T.expr) =>
  let intconst (n: Z) := T.Econst_int (Int.repr n) type_int32s in
  if intsize_eq sz IBool || signedness_eq sg Unsigned then
    let mask := two_p width - 1 in
    T.Ebinop Cop.Oand r (intconst mask) (T.typeof r)
  else
    let amount := Int.zwordsize - width in
    T.Ebinop Cop.Oshr
           (T.Ebinop Cop.Oshl r (intconst amount) type_int32s)
           (intconst amount)
           (T.typeof r).

FDefinition make_assign_value := fun (bf: bitfield) (r: T.expr) =>
  match bf with
  | Full => r
  | Bits sz sg pos width => make_normalize sz sg width r
  end.

FRecursion transl_expr with transl_exprlist.
Case Eassign l1 r2 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr l1 ce For_val;
    do (sl2, a2) <- transl_expr r2 ce For_val;
    do bf <- is_bitfield_access a1 ce;
    let ty1 := S.typeof l1 in
    let ty2 := S.typeof r2 in
    match dst with
    | self__SimplExpr_Eassign.For_val | self__SimplExpr_Eassign.For_set _ =>
        do t <- gensym ty1;
        ret (finish dst
                (sl1 ++ sl2 ++ T.Sset t (T.Ecast a2 ty1) :: make_assign bf a1 (T.Etempvar t ty1) :: nil)
                (make_assign_value bf (T.Etempvar t ty1)))
    | self__SimplExpr_Eassign.For_effects =>
        ret (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil,
              dummy_expr)
    end).
FEnd transl_expr with transl_exprlist.

FRecursion tr_is_bitfield_access
  about T.expr
  motive (fun (_ : T.expr) => composite_env -> bitfield -> Prop) by _rect.
Case _ := (fun ce bf => bf = Full).
FEnd tr_is_bitfield_access.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_assign_effects: forall ce le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_val e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_is_bitfield_access a1 ce bf ->
    tr_expr ce le For_effects (S.Eassign e1 e2 ty)
                    (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil)
                    any tmp
| tr_assign_val: forall ce le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2 bf,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_val e2 sl2 a2 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    list_disjoint tmp1 tmp2 ->
    In t tmp -> ~In t tmp1 -> ~In t tmp2 ->
    ty1 = S.typeof e1 ->
    ty2 = S.typeof e2 ->
    tr_is_bitfield_access a1 ce bf ->
    tr_expr ce le dst (S.Eassign e1 e2 ty)
                  (sl1 ++ sl2 ++
                  T.Sset t (T.Ecast a2 ty1) ::
                  make_assign bf a1 (T.Etempvar t ty1) ::
                  final dst (make_assign_value bf (T.Etempvar t ty1)))
                  (make_assign_value bf (T.Etempvar t ty1)) tmp.

Closing Fact tr_assign_inv :
  forall ce le dst e1 e2 ty sl a tmp,
  tr_expr ce le dst (S.Eassign e1 e2 ty) sl a tmp ->
  (exists sl1 a1 tmp1 sl2 a2 tmp2 bf, dst = For_effects /\ sl = sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_expr ce le For_val e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp /\ tr_is_bitfield_access a1 ce bf)
  \/ (exists sl1 a1 tmp1 sl2 a2 tmp2 t ty1 ty2 bf, a = make_assign_value bf (T.Etempvar t ty1)
    /\ sl = sl1 ++ sl2 ++ T.Sset t (T.Ecast a2 ty1) :: make_assign bf a1 (T.Etempvar t ty1) :: final dst (make_assign_value bf (T.Etempvar t ty1))
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_expr ce le For_val e2 sl2 a2 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ list_disjoint tmp1 tmp2 /\ In t tmp /\ ~In t tmp1 /\ ~In t tmp2
    /\ ty1 = S.typeof e1 /\ ty2 = S.typeof e2 /\ tr_is_bitfield_access a1 ce bf)
    by plain {intros *; intros H; inv H;
              [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
all: intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
all: intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FLemma eval_make_normalize:
  forall ge e le m a n sz sg sg1 attr width,
  0 < width -> width <= bitsize_intsize sz ->
  T.typeof a = Tint sz sg1 attr ->
  T.eval_expr ge e le m a (Vint n) ->
  T.eval_expr ge e le m (make_normalize sz sg width a) (Vint (bitfield_normalize sz sg width n)).
FProofLemma.
  intros. unfold make_normalize, bitfield_normalize.
  assert (bitsize_intsize sz <= Int.zwordsize) by (destruct sz; compute; congruence).
  destruct (intsize_eq sz IBool || signedness_eq sg Unsigned).
- rewrite Int.zero_ext_and by lia. fconstructor. fconstructor.
  rewrite H1; simpl. unfold sem_and, sem_binarith.
  assert (A: exists sg2, classify_binarith (Tint sz sg1 attr) type_int32s = bin_case_i sg2).
  { unfold classify_binarith. unfold type_int32s. destruct sz, sg1; econstructor; eauto. }
  fsimpl.  destruct A as (sg2 & A); rewrite A.
  unfold binarith_type.
  assert (B: forall i sz0 sg0 attr0,
             sem_cast (Vint i) (Tint sz0 sg0 attr0) (Tint I32 sg2 noattr) m = Some (Vint i)).
  { intros. unfold sem_cast, classify_cast. destruct Archi.ptr64; reflexivity. }
  unfold type_int32s; rewrite ! B. auto.
- rewrite Int.sign_ext_shr_shl by lia.
  set (amount := Int.repr (Int.zwordsize - width)).
  assert (LT: Int.ltu amount Int.iwordsize = true).
  { unfold Int.ltu. rewrite Int.unsigned_repr_wordsize. apply zlt_true.
    unfold amount; rewrite Int.unsigned_repr. lia.
    assert (Int.zwordsize < Int.max_unsigned) by reflexivity. lia. }
  fconstructor. fconstructor. fconstructor.
  rewrite H1. unfold sem_binary_operation, sem_shl, sem_shift. rewrite LT.
  fsimpl. destruct sz, sg1; reflexivity.
  fconstructor.
  unfold sem_binary_operation, sem_shr, sem_shift. rewrite LT. do 2 fsimpl. reflexivity.
Qed. CloseFLemma.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
all: intros; fsimpl in *; discriminate.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FLemma deref_loc_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall ty m b ofs bf t v,
  S.deref_loc ge ty m b ofs bf t v ->
  match chunk_for_volatile_type ty bf with
  | None => t = E0 /\ T.deref_loc tge ty m b ofs bf v
  | Some chunk => bf = Full /\ volatile_load (T.genv_genv tge) chunk m b ofs t v
  end.
FProofLemma.
  intros. unfold chunk_for_volatile_type. revert H0 H1; inv H2; intros.
- (* By_value, not volatile *)
  rewrite H1. split; auto. eapply T.deref_loc_value; eauto.
- (* By_value, volatile *)
  rewrite H0, H1. split; auto.
  eapply volatile_load_preserved with (ge1 := S.genv_genv ge); auto.
  eapply senv_preserved; eauto.
- (* By reference *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply T.deref_loc_reference; eauto.
- (* By copy *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply T.deref_loc_copy; eauto.
- (* Bitfield *)
  destruct (type_is_volatile ty); [destruct (access_mode ty)|]; auto using T.deref_loc_bitfield.
Qed. CloseFLemma.

FLemma assign_loc_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall ty m b ofs bf v t m' v',
  S.assign_loc ge ty m b ofs bf v t m' v' ->
  match chunk_for_volatile_type ty bf with
  | None => t = E0 /\ T.assign_loc (T.genv_cenv tge) ty m b ofs bf v m'
  | Some chunk => bf = Full /\ volatile_store (T.genv_genv tge) chunk m b ofs v t m'
  end.
FProofLemma.
  intros. unfold chunk_for_volatile_type. revert H0 H1; inv H2; intros.
- (* By_value, not volatile *)
  rewrite H1. split; auto. eapply T.assign_loc_value; eauto.
- (* By_value, volatile *)
  rewrite H0, H1. split; auto.
  eapply volatile_store_preserved with (ge1 := S.genv_genv ge); auto.
  eapply senv_preserved; eauto.
- (* By copy *)
  rewrite H0. erewrite <- comp_env_preserved in *; eauto.
  destruct (type_is_volatile ty); split; auto; eapply T.assign_loc_copy; eauto.
- (* Bitfield *)
  destruct (type_is_volatile ty); [destruct (access_mode ty)|]; eauto using T.assign_loc_bitfield.
Qed. CloseFLemma.

FInduction is_bitfield_access_sound
  about T.eval_lvalue
  motive (fun tge e le m a b ofs bf (_ : T.eval_lvalue tge e le m a b ofs bf) =>
    forall prog tprog ge, match_prog prog tprog ->
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall bf', tr_is_bitfield_access a (T.genv_cenv tge) bf' -> bf' = bf).
FProof.
all: intros; fsimpl in *; auto.
Qed. FEnd is_bitfield_access_sound.

FLemma make_assign_value_sound:
  forall ge ty m b ofs bf v t m' v',
  S.assign_loc ge ty m b ofs bf v t m' v' ->
  forall tge e le m'' r,
  T.typeof r = ty ->
  T.eval_expr tge e le m'' r v ->
  T.eval_expr tge e le m'' (make_assign_value bf r) v'.
FProofLemma.
  unfold make_assign_value; destruct 1; intros; auto.
  inv H. eapply eval_make_normalize; eauto; lia.
Qed. CloseFLemma.

FLemma typeof_make_assign_value:
  forall bf r, T.typeof (make_assign_value bf r) = T.typeof r.
FProofLemma.
  intros. destruct bf; simpl. fsimpl; auto. unfold make_normalize.
  destruct (intsize_eq sz IBool || signedness_eq sg Unsigned); fsimpl; auto.
Qed. CloseFLemma.

FInduction typeof_context.
FProof.
all: intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
(* assign left *)
- intros. apply tr_assign_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl1. rewrite <- app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. eapply tr_assign_effects. apply S; auto.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      auto. auto. auto. auto.
  (* for val *)
  + exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl1. rewrite <- app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. eapply tr_assign_val. apply S; auto.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      auto. auto. auto. auto. auto. auto.
      eapply typeof_context with (e1 := e) (e2 := e'); eauto.
      eauto. auto.
(* assign right *)
- intros. apply tr_assign_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
    exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl2. rewrite app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite <- app_assoc.
      eapply tr_assign_effects.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      apply S; auto. auto. auto. auto. auto.
  (* for val *)
  + assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
    exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl2. rewrite app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite <- app_assoc.
      eapply tr_assign_val.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      apply S; auto. auto. auto. auto. auto. auto. auto. auto.
      eapply typeof_context with (e1 := e0) (e2 := e'); eauto.
      auto.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

Inherit step_makeif.
FLemma step_make_assign:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall a1 a2 ty m b ofs bf t v m' v' v2 e le f k,
  S.assign_loc ge ty m b ofs bf v t m' v' ->
  T.eval_lvalue tge e le m a1 b ofs bf ->
  T.eval_expr tge e le m a2 v2 ->
  sem_cast v2 (T.typeof a2) ty m = Some v ->
  T.typeof a1 = ty ->
  T.step tge (T.State f (make_assign bf a1 a2) k e le m)
          t (T.State f T.Sskip k e le m').
FProofLemma.
  intros. exploit assign_loc_translated; eauto. rewrite <- H6.
  unfold make_assign. destruct (chunk_for_volatile_type (T.typeof a1) bf) as [chunk|].
(* volatile case *)
- intros [A B]. subst bf. change le with (T.set_opttemp None Vundef le) at 2. fconstructor.
  econstructor. apply T.eval_Eaddrof. eauto.
  fsimpl. unfold sem_cast. simpl. eauto.
  econstructor; eauto. rewrite H6; eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
- intros [A B]. subst t. fconstructor. congruence.
Qed. CloseFLemma.

Inherit makeif_nolabel.
FLemma make_assign_nolabel:
  forall lbl bf l r, nolabel lbl (make_assign bf l r).
FProofLemma.
  unfold make_assign; intros; red; intros.
  destruct (chunk_for_volatile_type (T.typeof l) bf); fsimpl; auto.
Qed. CloseFLemma.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
all: intros; simpl; NoLabelTac; apply make_assign_nolabel.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Eassign e1 e2 ty := (Datatypes.S(esize e1 + esize e2)%nat).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
all: intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FInduction estep_simulation.
FProof.
intros; inv MS.
exploit tr_top_leftcontext; eauto. clear TR.
intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
inv P.
- (* fdiscriminate. *) apply cheat.
- apply tr_assign_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
    exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. simpl; assumption. }
    subst; simpl Kseqlist.
    eexists; split.
    left. eapply plus_left. fconstructor.
    apply star_one. eapply step_make_assign; eauto. rewrite <- TY2; eauto.
    reflexivity.
    econstructor; eauto. change sl2 with (nil ++ sl2). apply S.
    fconstructor. auto. do 2 fsimpl; auto.
  (* for value *)
  + exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
    exploit tr_simple_lvalue. 1-4: eauto.
      eapply tr_expr_invariant. eauto.
      instantiate (1 := PTree.set t0 v1 le).
      intros. apply PTree.gso. intuition congruence.
    intros [SL1 [TY1 EV1]].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. simpl; assumption. }
    subst; simpl Kseqlist.
    econstructor; split.
    left. eapply plus_left. fconstructor.
    eapply star_left. fconstructor. fconstructor. rewrite <- TY2; eauto.
    eapply star_left. fconstructor.
    apply star_one. eapply step_make_assign; eauto.
    fconstructor. apply PTree.gss. fsimpl. eapply cast_idempotent; eauto.
    reflexivity. reflexivity. traceEq.
    econstructor; eauto. apply S.
    apply tr_val_gen. rewrite typeof_make_assign_value.
      (* fsimpl not working *)
      rewrite T.typeof_Etempvar_eq. unfold T.typeofEtempvar. reflexivity.
    intros. eapply make_assign_value_sound; eauto.
      rewrite T.typeof_Etempvar_eq. unfold T.typeofEtempvar. reflexivity.
    fconstructor. rewrite H0; auto. apply PTree.gss.
    intros. apply PTree.gso. intuition congruence.
    do 2 fsimpl. reflexivity.
Qed. FEnd estep_simulation.
FEnd SimplExpr_Eassign.

Trait SimplExpr_Evalof extends SimplExpr, SimplExpr_Ederef, SimplExpr_Eassign.
Family S extends C_Evalof. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

Inherit chunk_for_volatile_type.

FDefinition make_set := fun (bf: bitfield) (id: ident) (l: T.expr) =>
 match chunk_for_volatile_type (T.typeof l) bf with
  | None => T.Sset id l
  | Some chunk =>
      let typtr := Tpointer (T.typeof l) noattr in
      T.Sbuiltin (Some id) (EF_vload chunk) (typtr :: nil) ((T.Eaddrof l typtr):: nil)
  end.

FDefinition transl_valof : composite_env -> type -> T.expr -> mon (list T.stmt * T.expr) := fun ce ty l =>
  if type_is_volatile ty
  then do t <- gensym ty;
       do bf <- is_bitfield_access l ce;
       ret (make_set bf t l :: nil, T.Etempvar t ty)
  else ret (nil, l).

FRecursion transl_expr with transl_exprlist.
Case Evalof l ty :=
(fun ce dst =>
   do (sl1, a1) <- transl_expr l ce For_val;
   do (sl2, a2) <- transl_valof ce (S.typeof l) a1;
   ret (finish dst (sl1 ++ sl2) a2)).
FEnd transl_expr with transl_exprlist.

Inherit tr_is_bitfield_access.

MetaData tr_rvalof.
Inductive tr_rvalof: composite_env -> type -> T.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
  | tr_rvalof_nonvol: forall ce ty a tmp,
      type_is_volatile ty = false ->
      tr_rvalof ce ty a nil a tmp
  | tr_rvalof_vol: forall ce ty a t bf tmp,
      type_is_volatile ty = true -> In t tmp ->
      tr_is_bitfield_access a ce bf ->
      tr_rvalof ce ty a (make_set bf t a :: nil) (T.Etempvar t ty) tmp.
FEnd tr_rvalof.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_valof: forall ce le dst e1 ty tmp sl1 a1 tmp1 sl2 a2 tmp2,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_rvalof ce (S.typeof e1) a1 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le dst (S.Evalof e1 ty)
                  (sl1 ++ sl2 ++ final dst a2)
                  a2 tmp.

Closing Fact tr_valof_inv :
  forall ce le dst e1 ty sl a tmp,
  tr_expr ce le dst (S.Evalof e1 ty) sl a tmp ->
  exists sl1 a1 tmp1 sl2 tmp2, sl = sl1 ++ sl2 ++ final dst a
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_rvalof ce (S.typeof e1) a1 sl2 a tmp2
    /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil)
  by (intros; destruct H; subst dst; auto).
intros; fsimpl in *.
destruct (andb_prop _ _ H1). inv t.
rewrite H; eauto.
simpl. destruct (type_is_volatile (S.typeof e1)); simpl in H3; congruence.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction tr_simple_rvalue with tr_simple_lvalue.
FProof.
intros. apply tr_valof_inv in H3; unpack H3; subst sl.
inv TEMP1; try congruence.
exploit H; eauto. intros [A [B C]].
subst sl1; simpl.
assert (T.eval_expr (T.globalenv tprog) e le m a v).
{ eapply T.eval_Elvalue. eauto.
  rewrite <- B.
  exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite e1. tauto. }
destruct dst.
- fsimpl. auto.
- auto.
- eexists. split. simpl; eauto. fsimpl; auto.
Qed. FEnd tr_simple_rvalue with tr_simple_lvalue.

FInduction typeof_context.
FProof.
intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
intros. apply tr_valof_inv in H0; unpack H0; subst.
exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
TR. subst sl1; rewrite <- app_assoc; eauto. red; eauto.
intros. rewrite app_assoc; fconstructor.
exploit typeof_context; eauto. congruence.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

Inherit step_makeif.
FLemma step_make_set:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall id a ty m b ofs bf t v e le f k,
  S.deref_loc ge ty m b ofs bf t v ->
  T.eval_lvalue tge e le m a b ofs bf ->
  T.typeof a = ty ->
  T.step tge (T.State f (make_set bf id a) k e le m)
           t (T.State f T.Sskip k e (PTree.set id v le) m).
FProofLemma.
intros. exploit deref_loc_translated; eauto. rewrite <- H4.
unfold make_set. destruct (chunk_for_volatile_type (T.typeof a) bf) as [chunk|].
(* volatile case *)
- intros [A B]. subst bf.
  change (PTree.set id v le) with (T.set_opttemp (Some id) v le). fconstructor.
  econstructor. apply T.eval_Eaddrof. eauto.
  fsimpl. unfold sem_cast. simpl. eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
- intros [A B]. subst t. fconstructor. eapply T.eval_Elvalue; eauto.
Qed. CloseFLemma.

Inherit push_seq.
FLemma step_tr_rvalof:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall ty m b ofs bf t v e le a sl a' tmp f k,
  S.deref_loc ge ty m b ofs bf t v ->
  T.eval_lvalue tge e le m a b ofs bf ->
  tr_rvalof (T.genv_cenv tge) ty a sl a' tmp ->
  T.typeof a = ty ->
  exists le',
    star T.step tge (T.State f T.Sskip (Kseqlist sl k) e le m)
               t (T.State f T.Sskip k e le' m)
  /\ T.eval_expr tge e le' m a' v
  /\ T.typeof a' = T.typeof a
  /\ forall x, ~In x tmp -> le'!x = le!x.
FProofLemma.
intros. inv H4.
(* not volatile *)
- exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H6.
  intros [A B]. subst t.
  exists le; split. apply star_refl.
  split. eapply T.eval_Elvalue; eauto.
  auto.
(* volatile *)
- intros.
  exploit is_bitfield_access_sound; eauto. intros EQ; subst bf0.
  exists (PTree.set t0 v le); split.
  simpl. eapply star_two. fconstructor. eapply step_make_set; eauto. traceEq.
  split. fconstructor. apply PTree.gss.
  split. fsimpl; auto.
  intros. apply PTree.gso. congruence.
Qed. CloseFLemma.

Inherit makeif_nolabel.
FLemma make_set_nolabel:
  forall lbl bf t a, nolabel lbl (make_set bf t a).
FProofLemma.
  unfold make_set; intros; red; intros.
  destruct (chunk_for_volatile_type (T.typeof a) bf); fsimpl; auto.
Qed. CloseFLemma.

FLemma tr_rvalof_nolabel:
  forall ce ty a sl a' tmp, tr_rvalof ce ty a sl a' tmp -> forall lbl, nolabel_list lbl sl.
FProofLemma.
  destruct 1; simpl; intuition. apply make_set_nolabel.
Qed. CloseFLemma.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
intros; NoLabelTac. eapply tr_rvalof_nolabel; eauto.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Evalof e ty := (Datatypes.S(esize e)%nat).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
all: intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FInduction estep_simulation.
FProof.
intros; inv MS.
exploit tr_top_leftcontext; eauto. clear TR.
intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
inv P.
- (* fdiscriminate. *) apply cheat.
- apply tr_valof_inv in H0; unpack H0; subst. inv TEMP1; try congruence.
  exploit tr_simple_lvalue; eauto. intros [SL [TY EV]]. subst sl0; simpl.
  assert (bf0 = bf).
  { eapply is_bitfield_access_sound; eauto.
    erewrite comp_env_preserved; eauto. simpl; assumption. }
  subst bf0.
  econstructor; split.
  left. eapply plus_two. fconstructor. eapply step_make_set; eauto. traceEq.
  econstructor; eauto.
  change (final dst' (T.Etempvar t0 (S.typeof l)) ++ sl2) with (nil ++ (final dst' (T.Etempvar t0 (S.typeof l)) ++ sl2)).
  apply S. apply tr_val_gen. rewrite T.typeof_Etempvar_eq. auto.
  intros. fconstructor. rewrite H3; auto. apply PTree.gss.
  intros. apply PTree.gso. red; intros; subst; elim H3; auto.
  do 2 fsimpl. auto.
Qed. FEnd estep_simulation.
FEnd SimplExpr_Evalof.

Trait SimplExpr_Eaddrof extends SimplExpr, SimplExpr_Ederef.
Family S extends C_Eaddrof. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion Eaddrof'
  about T.expr
  motive (fun (_ : T.expr) => type -> T.expr)
  by _rect.
Case Econst_int i ty := (fun t => T.Eaddrof (T.Econst_int i ty) t).
Case Econst_float f ty := (fun t => T.Eaddrof (T.Econst_float f ty) t).
Case Econst_single s ty := (fun t => T.Eaddrof (T.Econst_single s ty) t).
Case Econst_long l ty := (fun t => T.Eaddrof (T.Econst_long l ty) t).
Case Etempvar v ty := (fun t => T.Eaddrof (T.Etempvar v ty) t).
Case Esizeof ty' ty := (fun t => T.Eaddrof (T.Esizeof ty' ty) t).
Case Ealignof ty' ty := (fun t => T.Eaddrof (T.Ealignof ty' ty) t).
Case Ecast e ty := (fun t => T.Eaddrof (T.Ecast e ty) t).
Case Eunop op e ty := (fun t => T.Eaddrof (T.Eunop op e ty) t).
Case Ebinop op e0 e1 ty := (fun t => T.Eaddrof (T.Ebinop op e0 e1 ty) t).
Case Ederef i ty := (fun t => if type_eq t (T.typeof i) then i else T.Eaddrof (T.Ederef i ty) t).
Case Eaddrof a ty := (fun t => T.Eaddrof (T.Eaddrof a ty) t).
Case Evar i ty := (fun t => T.Eaddrof (T.Evar i ty) t).
FEnd Eaddrof'.

FRecursion transl_expr with transl_exprlist.
Case Eaddrof l ty :=
   (fun ce dst => do (sl, a) <- transl_expr l ce For_val;
      ret (finish dst sl (Eaddrof' a ty))).
FEnd transl_expr with transl_exprlist.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_addrof: forall ce le dst e1 ty tmp sl1 a1,
    tr_expr ce le For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Eaddrof e1 ty)
                 (sl1 ++ final dst (Eaddrof' a1 ty))
                 (Eaddrof' a1 ty) tmp.

Closing Fact tr_addrof_inv :
  forall ce le dst e1 ty sl a tmp,
  tr_expr ce le dst (S.Eaddrof e1 ty) sl a tmp ->
  exists sl1 a1, sl = sl1 ++ final dst (Eaddrof' a1 ty) /\ a = Eaddrof' a1 ty
    /\ tr_expr ce le For_val e1 sl1 a1 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInduction eval_Eaddrof'
  about T.expr
  motive (fun (a : T.expr) =>
    forall ge e le m t l ofs,
    T.eval_lvalue ge e le m a l ofs Full ->
    T.eval_expr ge e le m (Eaddrof' a t) (Vptr l ofs)).
FProof.
all: intros; fsimpl; auto using T.eval_Eaddrof.
destruct (type_eq t0 (T.typeof __i)); auto using T.eval_Eaddrof.
apply T.eval_lvalue_deref_inv in H0 as []; auto.
Qed. FEnd eval_Eaddrof'.

FInduction typeof_Eaddrof'
  about T.expr
  motive (fun (a : T.expr) =>
    forall t, T.typeof (Eaddrof' a t) = t).
FProof.
all: intros; fsimpl; fsimpl; auto.
destruct (type_eq t0 (T.typeof __i)); fsimpl; auto.
Qed. FEnd typeof_Eaddrof'.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil)
  by (intros; destruct H; subst dst; auto).
intros; fsimpl in *. rewrite H; auto. simpl; auto.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction tr_simple_rvalue with tr_simple_lvalue.
FProof.
intros. fsimpl.
apply tr_addrof_inv in H3; unpack H3; subst sl a; simpl.
exploit H; eauto. intros [A [B C]]. subst sl1; simpl.
assert (T.eval_expr tge e le m (Eaddrof' a1 ty) (Vptr b ofs)) by (apply eval_Eaddrof'; auto).
assert (T.typeof (Eaddrof' a1 ty) = ty) by (apply typeof_Eaddrof').
destruct dst; auto. simpl; eexists; eauto.
Qed. FEnd tr_simple_rvalue with tr_simple_lvalue.

FInduction typeof_context.
FProof.
intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
intros. apply tr_addrof_inv in H0; unpack H0; subst.
exploit H; eauto.
intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
- rewrite Q, app_assoc. eauto.
- auto.
- intros. rewrite app_assoc. fconstructor.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Eaddrof l ty := (Datatypes.S(esize l)).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.
FEnd SimplExpr_Eaddrof.

Trait SimplExpr_Eassignop extends SimplExpr, SimplExpr_Ederef, SimplExpr_Eassign, SimplExpr_Evalof.
Family S extends C_Eassignop. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist.
Case Eassignop op l1 r2 tyres ty :=
  (fun ce dst =>
     let ty1 := S.typeof l1 in
      do (sl1, a1) <- transl_expr l1 ce For_val;
      do (sl2, a2) <- transl_expr r2 ce For_val;
      do (sl3, a3) <- transl_valof ce ty1 a1;
      do bf <- is_bitfield_access a1 ce;
      match dst with
      | self__SimplExpr_Eassignop.For_val | self__SimplExpr_Eassignop.For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ sl2 ++ sl3 ++
                  T.Sset t (T.Ecast (T.Ebinop op a3 a2 tyres) ty1) ::
                  make_assign bf a1 (T.Etempvar t ty1) :: nil)
                 (make_assign_value bf (T.Etempvar t ty1)))
      | self__SimplExpr_Eassignop.For_effects =>
          ret (sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (T.Ebinop op a3 a2 tyres) :: nil,
              dummy_expr)
     end).
FEnd transl_expr with transl_exprlist.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_assignop_effects: forall ce le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_val e2 sl2 a2 tmp2 ->
    ty1 = S.typeof e1 ->
    tr_rvalof ce ty1 a1 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
    tr_is_bitfield_access a1 ce bf ->
    tr_expr ce le For_effects (S.Eassignop op e1 e2 tyres ty)
                    (sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (T.Ebinop op a3 a2 tyres) :: nil)
                    any tmp
| tr_assignop_val: forall ce le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf tmp ty1,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le For_val e2 sl2 a2 tmp2 ->
    tr_rvalof ce ty1 a1 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
    In t tmp -> ~In t tmp1 -> ~In t tmp2 -> ~In t tmp3 ->
    ty1 = S.typeof e1 ->
    tr_is_bitfield_access a1 ce bf ->
    tr_expr ce le dst (S.Eassignop op e1 e2 tyres ty)
                 (sl1 ++ sl2 ++ sl3 ++
                  T.Sset t (T.Ecast (T.Ebinop op a3 a2 tyres) ty1) ::
                  make_assign bf a1 (T.Etempvar t ty1) ::
                  final dst (make_assign_value bf (T.Etempvar t ty1)))
                 (make_assign_value bf (T.Etempvar t ty1)) tmp.

Closing Fact tr_assignop_inv :
  forall ce le dst op e1 e2 tyres ty sl a tmp,
  tr_expr ce le dst (S.Eassignop op e1 e2 tyres ty) sl a tmp ->
  (exists ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3, dst = For_effects /\ sl = sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (T.Ebinop op a3 a2 tyres) :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_expr ce le For_val e2 sl2 a2 tmp2
    /\ ty1 = S.typeof e1 /\ tr_rvalof ce ty1 a1 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3 /\ list_disjoint tmp2 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp /\ tr_is_bitfield_access a1 ce bf)
  \/ (exists sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf ty1, a = make_assign_value bf (T.Etempvar t ty1)
    /\ sl = sl1 ++ sl2 ++ sl3 ++ T.Sset t (T.Ecast (T.Ebinop op a3 a2 tyres) ty1) :: make_assign bf a1 (T.Etempvar t ty1) :: final dst (make_assign_value bf (T.Etempvar t ty1))
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_expr ce le For_val e2 sl2 a2 tmp2
    /\ ty1 = S.typeof e1 /\ tr_rvalof ce ty1 a1 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3 /\ list_disjoint tmp2 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp /\ In t tmp /\ ~In t tmp1 /\ ~In t tmp2 /\ ~In t tmp3 /\ tr_is_bitfield_access a1 ce bf)
    by plain {intros *; intros H; inv H;
              [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
all: intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
all: intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
all: intros; fsimpl in *; discriminate.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction typeof_context.
FProof.
all: intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
(* assignop left *)
- intros. apply tr_assignop_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl1. rewrite <- app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. eapply tr_assignop_effects. apply S; auto.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      symmetry; eapply typeof_context with (e2 := e); eauto. eauto.
      auto. auto. auto. auto. auto. auto. auto.
  (* for val *)
  + exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl1. rewrite <- app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. eapply tr_assignop_val. apply S; auto.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
      eapply typeof_context with (e1 := e) (e2 := e'); eauto. auto.
(* assignop right *)
- intros. apply tr_assignop_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
    exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl2. rewrite <- app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite <- app_assoc.
      eapply tr_assignop_effects.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      apply S; auto. auto. eauto. auto. auto. auto. auto. auto. auto. auto.
  (* for val *)
  + assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
    exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl2. rewrite <- app_assoc. eauto.
    * red; auto.
    * intros. rewrite app_assoc. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite <- app_assoc.
      eapply tr_assignop_val.
      eapply tr_expr_invariant; eauto. UNCHANGED.
      apply S; auto. eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
all: intros; simpl; NoLabelTac;
  try apply make_assign_nolabel;
  eapply tr_rvalof_nolabel; eauto.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Eassignop op e1 e2 tyres ty := (Datatypes.S(esize e1 + esize e2)%nat).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
all: intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FInduction estep_simulation.
FProof.
all: intros; inv MS;
  exploit tr_top_leftcontext; eauto; clear TR;
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]];
  inv P.
(* assignop *)
- (* fdiscriminate. *) apply cheat.
- apply tr_assignop_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit step_tr_rvalof; eauto. erewrite comp_env_preserved; eauto. eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
    exploit tr_simple_lvalue. 1-4: eauto. eapply tr_expr_invariant. eauto.
    intros. apply INV. NOTIN. intros [? [? EV1']].
    exploit tr_simple_rvalue. 1-4: eauto. eapply tr_expr_invariant. eauto.
    intros. apply INV. NOTIN. simpl. intros [SL2 [TY2 EV2]].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. assumption. }
    subst; simpl Kseqlist.
    econstructor; split.
    left. eapply star_plus_trans. rewrite <- app_assoc. rewrite Kseqlist_app. eexact EXEC.
    eapply plus_two. simpl. fconstructor. eapply step_make_assign; eauto.
      fconstructor. erewrite TY3, <- TY1, <- TY2, comp_env_preserved; eauto.
      fsimpl; eassumption.
    reflexivity. traceEq.
    econstructor; eauto. change sl2 with (nil ++ sl2). apply S.
    fconstructor. auto. do 2 fsimpl; auto.
  (* for value *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit step_tr_rvalof; eauto. erewrite comp_env_preserved; eauto. eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
    exploit tr_simple_lvalue. 1-4: eauto. eapply tr_expr_invariant. eauto.
    intros. apply INV. NOTIN. intros [? [? EV1']].
    exploit tr_simple_rvalue. 1-4: eauto. eapply tr_expr_invariant. eauto.
    intros. apply INV. NOTIN. simpl. intros [SL2 [TY2 EV2]].
    exploit tr_simple_lvalue. 1-4: eauto.
      eapply tr_expr_invariant. eauto.
      instantiate (1 := PTree.set t v4 le').
      intros. rewrite PTree.gso. apply INV. NOTIN. intuition congruence.
    intros [? [? EV1'']].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. assumption. }
    subst; simpl Kseqlist.
    econstructor; split.
    left. rewrite <- app_assoc. rewrite Kseqlist_app.
    eapply star_plus_trans. eexact EXEC.
    simpl. eapply plus_four. fconstructor. fconstructor.
      fconstructor. fconstructor. erewrite TY3, <- TY1, <- TY2, comp_env_preserved; eauto.
      fsimpl; eassumption.
    fconstructor. eapply step_make_assign; eauto.
      fconstructor. apply PTree.gss. fsimpl. eapply cast_idempotent; eauto.
      reflexivity. traceEq.
    econstructor; eauto. apply S.
    apply tr_val_gen. rewrite typeof_make_assign_value; auto.
      (* fsimpl not working *)
      rewrite T.typeof_Etempvar_eq. unfold T.typeofEtempvar. reflexivity.
    intros. eapply make_assign_value_sound; eauto.
      rewrite T.typeof_Etempvar_eq. unfold T.typeofEtempvar. reflexivity.
    fconstructor. rewrite H4; auto. apply PTree.gss.
    intros. rewrite PTree.gso. apply INV.
    red; intros; elim H4; auto.
    intuition congruence.
    do 2 fsimpl. reflexivity.
(* assignop stuck *)
- (* fdiscriminate. *) apply cheat.
- apply tr_assignop_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit tr_simple_lvalue; eauto. intros [SL2 [TY2 EV2]].
    exploit step_tr_rvalof; eauto. erewrite comp_env_preserved; eauto. eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
    subst; simpl Kseqlist.
    econstructor; split.
    right; split. rewrite <- app_assoc. rewrite Kseqlist_app. eexact EXEC.
    simpl. lia.
    constructor.
  (* for value *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
    exploit step_tr_rvalof; eauto. erewrite comp_env_preserved; eauto. eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
    subst; simpl Kseqlist.
    econstructor; split.
    right; split. rewrite <- app_assoc. rewrite Kseqlist_app. eexact EXEC.
    simpl. lia.
    constructor.
Qed. FEnd estep_simulation.
FEnd SimplExpr_Eassignop.

Trait SimplExpr_Epostincr extends SimplExpr, SimplExpr_Ederef, SimplExpr_Eassign, SimplExpr_Evalof.
Family S extends C_Epostincr. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FDefinition transl_incrdecr := fun (id: incr_or_decr) (a: T.expr) (ty: type) =>
  match id with
  | Incr => T.Ebinop Cop.Oadd a (T.Econst_int Int.one Ctypes.type_int32s) (Cop.incrdecr_type ty)
  | Decr => T.Ebinop Cop.Osub a (T.Econst_int Int.one Ctypes.type_int32s) (Cop.incrdecr_type ty)
  end.

FRecursion transl_expr with transl_exprlist.
Case Epostincr id l1 ty :=
  (fun ce dst =>
     let ty1 := S.typeof l1 in
      do (sl1, a1) <- transl_expr l1 ce For_val;
      do bf <- is_bitfield_access a1 ce;
      match dst with
      | self__SimplExpr_Epostincr.For_val | self__SimplExpr_Epostincr.For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ make_set bf t a1 ::
                  make_assign bf a1 (transl_incrdecr id (T.Etempvar t ty1) ty1) :: nil)
                 (T.Etempvar t ty1))
      | self__SimplExpr_Epostincr.For_effects =>
          do (sl2, a2) <- transl_valof ce ty1 a1;
          ret (sl1 ++ sl2 ++ make_assign bf a1 (transl_incrdecr id a2 ty1) :: nil,
               dummy_expr)
      end).
FEnd transl_expr with transl_exprlist.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_postincr_effects: forall ce le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_rvalof ce ty1 a1 sl2 a2 tmp2 ->
    ty1 = S.typeof e1 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    list_disjoint tmp1 tmp2 ->
    tr_is_bitfield_access a1 ce bf ->
    tr_expr ce le For_effects (S.Epostincr id e1 ty)
                    (sl1 ++ sl2 ++ make_assign bf a1 (transl_incrdecr id a2 ty1) :: nil)
                    any tmp
| tr_postincr_val: forall ce le dst id e1 ty sl1 a1 tmp1 bf t ty1 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    incl tmp1 tmp -> In t tmp -> ~In t tmp1 ->
    ty1 = S.typeof e1 ->
    tr_is_bitfield_access a1 ce bf ->
    tr_expr ce le dst (S.Epostincr id e1 ty)
                 (sl1 ++ make_set bf t a1 ::
                  make_assign bf a1 (transl_incrdecr id (T.Etempvar t ty1) ty1) ::
                  final dst (T.Etempvar t ty1))
                 (T.Etempvar t ty1) tmp.

Closing Fact tr_postincr_inv :
  forall ce le dst id e1 ty sl a tmp,
  tr_expr ce le dst (S.Epostincr id e1 ty) sl a tmp ->
  (exists ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf, dst = For_effects /\ sl = sl1 ++ sl2 ++ make_assign bf a1 (transl_incrdecr id a2 ty1) :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_rvalof ce ty1 a1 sl2 a2 tmp2 /\ ty1 = S.typeof e1
    /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp /\ tr_is_bitfield_access a1 ce bf)
  \/ (exists sl1 a1 tmp1 t ty1 bf, a = T.Etempvar t ty1
    /\ sl = (sl1 ++ make_set bf t a1 :: make_assign bf a1 (transl_incrdecr id (T.Etempvar t ty1) ty1) :: final dst (T.Etempvar t ty1))
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ incl tmp1 tmp /\ In t tmp /\ ~In t tmp1
    /\ ty1 = S.typeof e1 /\ tr_is_bitfield_access a1 ce bf)
  by plain {intros *; intros H; inv H;
            [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
all: intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
all: intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
all: intros; fsimpl in *; discriminate.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction typeof_context.
FProof.
all: intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
intros. apply tr_postincr_inv in H0 as [H0|H0]; unpack H0; subst.
(* for effects *)
- exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl1. rewrite <- app_assoc. eauto.
  + red; auto.
  + intros. rewrite app_assoc. eapply tr_postincr_effects; eauto.
    eapply typeof_context; eauto.
(* for val *)
- exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl1. rewrite <- app_assoc. eauto.
  + red; auto.
  + intros. rewrite app_assoc. eapply tr_postincr_val; eauto.
    eapply typeof_context with (e1 := e) (e2 := e'); eauto.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
all: intros; simpl; NoLabelTac.
- eapply tr_rvalof_nolabel; eauto.
- apply make_assign_nolabel.
- apply make_set_nolabel.
- apply make_assign_nolabel.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Epostincr id l1 ty := (Datatypes.S(esize l1)).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FInduction estep_simulation.
FProof.
all: intros; inv MS;
  exploit tr_top_leftcontext; eauto; clear TR;
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]];
  inv P.
(* postincr *)
- (* fdiscriminate. *) apply cheat.
- apply tr_postincr_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit step_tr_rvalof; eauto. erewrite comp_env_preserved; eauto. eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
    exploit tr_simple_lvalue. 1-4: eauto. eapply tr_expr_invariant. eauto.
    intros. apply INV. NOTIN. intros [? [? EV1']].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. assumption. }
    subst; simpl Kseqlist.
    econstructor; split.
    left. eapply star_plus_trans. rewrite <- app_assoc. rewrite Kseqlist_app. eexact EXEC.
    eapply plus_two. simpl. fconstructor. eapply step_make_assign; eauto.
    unfold transl_incrdecr. destruct id; simpl in e1.
      fconstructor. fconstructor. erewrite TY3, <- TY1, comp_env_preserved; eauto.
      simpl. (* fsimpl not working *) rewrite T.typeof_Econst_int_eq. eauto.
      fconstructor. fconstructor. erewrite TY3, <- TY1, comp_env_preserved; eauto.
      simpl. (* fsimpl not working *) rewrite T.typeof_Econst_int_eq. eauto.
    destruct id; unfold transl_incrdecr; fsimpl; auto.
    reflexivity. traceEq.
    econstructor; eauto. change sl2 with (nil ++ sl2). apply S.
    fconstructor. auto. do 2 fsimpl; auto.
  (* for value *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit tr_simple_lvalue. 1-4: eauto.
      eapply tr_expr_invariant. eauto.
      instantiate (1 := PTree.set t v1 le).
      intros. apply PTree.gso. intuition congruence.
    intros [SL2 [TY2 EV2]].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. assumption. }
    subst; simpl Kseqlist.
    econstructor; split.
    left. eapply plus_four. fconstructor.
    eapply step_make_set; eauto.
    fconstructor.
    eapply step_make_assign; eauto.
    unfold transl_incrdecr. destruct id; simpl in e1.
    fconstructor. fconstructor. apply PTree.gss. fconstructor.
    erewrite comp_env_preserved; eauto. simpl; do 2 fsimpl; eauto.
    fconstructor. fconstructor. apply PTree.gss. fconstructor.
    erewrite comp_env_preserved; eauto. simpl; do 2 fsimpl; eauto.
    destruct id; unfold transl_incrdecr; fsimpl; auto.
    traceEq.
    econstructor; eauto. apply S.
    apply tr_val_gen. (* fsimpl not working *) rewrite T.typeof_Etempvar_eq; auto. intros; fconstructor.
    rewrite H0; auto. apply PTree.gss.
    intros. apply PTree.gso. intuition congruence.
    do 2 fsimpl; auto.
(* postincr stuck *)
- (* fdiscriminate. *) apply cheat.
- apply tr_postincr_inv in H0 as [H0|H0]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit step_tr_rvalof; eauto. erewrite comp_env_preserved; eauto. eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
    subst. simpl Kseqlist.
    econstructor; split.
    right; split. rewrite <- app_assoc, Kseqlist_app. eexact EXEC.
    simpl; lia.
    constructor.
  (* for value *)
  + exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
    assert (bf0 = bf).
    { eapply is_bitfield_access_sound; eauto.
      erewrite comp_env_preserved; eauto. assumption. }
    subst. simpl Kseqlist.
    econstructor; split.
    left. eapply plus_two. fconstructor. eapply step_make_set; eauto.
    traceEq.
    constructor.
Qed. FEnd estep_simulation.
FEnd SimplExpr_Epostincr.

Family SimplExpr
  extends
  SimplExpr_Ederef,
  SimplExpr_Evar,
  SimplExpr_Eassign,
  SimplExpr_Evalof,
  SimplExpr_Eaddrof,
  SimplExpr_Eassignop,
  SimplExpr_Epostincr.
FEnd SimplExpr.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.
Family C.
FInductive expr : Type :=
| Efield : expr -> ident -> type -> expr.

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FRecursion simple.
Case Efield e i ty := (simple e).
FEnd simple.

FInductive eval_simple_rvalue: genv -> env -> mem -> expr -> val -> Prop :=
with eval_simple_lvalue: genv -> env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| esl_field_struct: forall ge e m r f ty b ofs id co a delta bf,
    eval_simple_rvalue ge e m r (Vptr b ofs) ->
    typeof r = Tstruct id a ->
    (genv_cenv ge)!id = Some co ->
    field_offset (genv_cenv ge) f (co_members co) = OK (delta, bf) ->
    eval_simple_lvalue ge e m (Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf
| esl_field_union: forall ge e m r f ty b ofs id co a delta bf,
    eval_simple_rvalue ge e m r (Vptr b ofs) ->
    typeof r = Tunion id a ->
    union_field_offset (genv_cenv ge) f (co_members co) = OK (delta, bf) ->
    (genv_cenv ge)!id = Some co ->
    eval_simple_lvalue ge e m (Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_field: forall k C f ty,
    leftcontext k RV C -> leftcontext k LV (fun x => Efield (C x) f ty).
FEnd C.

Family Clight.
FInductive expr : Type :=
| Efield: expr -> ident -> type -> expr. (* access to a member of a struct or union *)

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FInductive eval_expr: genv -> env -> temp_env -> mem -> expr -> val -> Prop :=
with eval_lvalue: genv -> env -> temp_env -> mem -> expr -> block -> ptrofs -> bitfield -> Prop :=
| eval_Efield_struct: forall ge e le m a i ty l ofs id co att delta bf,
    eval_expr ge e le m a (Vptr l ofs) ->
    typeof a = Tstruct id att ->
    (genv_cenv ge)!id = Some co ->
    field_offset (genv_cenv ge) i (co_members co) = OK (delta, bf) ->
    eval_lvalue ge e le m (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
| eval_Efield_union: forall ge e le m a i ty l ofs id co att delta bf,
    eval_expr ge e le m a (Vptr l ofs) ->
    typeof a = Tunion id att ->
    (genv_cenv ge)!id = Some co ->
    union_field_offset (genv_cenv ge) i (co_members co) = OK (delta, bf) ->
    eval_lvalue ge e le m (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.
FEnd Clight.

Family SimplExpr.

FRecursion eval_simpl_expr.
Case Efield e i ty := None.
FEnd eval_simpl_expr.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

FDefinition is_bitfield_access_aux := fun
              (ce : composite_env) (fn: composite_env -> ident -> members -> res (Z * bitfield))
              (id: ident) (fld: ident) => (* : mon bitfield :=*)
  match ce!id with
  | None => error (MSG "unknown composite " :: CTX id :: nil)
  | Some co =>
      match fn ce fld (co_members co) with
      | OK (_, bf) => ret bf
      | Error _ => error (MSG "unknown field " :: CTX fld :: nil)
      end
  end.

FRecursion is_bitfield_access.
Case Efield r f x :=
 (fun cenv =>
  match T.typeof r with
  | Tstruct id _ => is_bitfield_access_aux cenv field_offset id f
  | Tunion id _ => is_bitfield_access_aux cenv union_field_offset id f
  | _ => error (msg "is_bitfield_access")
  end).
FEnd is_bitfield_access.

FRecursion Eaddrof'.
Case Efield r f ty := (fun t => T.Eaddrof (T.Efield r f ty) t).
FEnd Eaddrof'.

FRecursion Ederef'.
Case Efield r f ty := (fun t => T.Ederef (T.Efield r f ty) t).
FEnd Ederef'.

FRecursion transl_expr with transl_exprlist.
Case Efield r f ty :=
  (fun ce dst =>
    do (sl, a) <- transl_expr r ce For_val;
    ret (finish dst sl (T.Efield a f ty))).
FEnd transl_expr with transl_exprlist.

FRecursion tr_is_bitfield_access.
Case Efield r f ty := (fun ce bf =>
  exists co ofs,
  match T.typeof r with
  | Tstruct id _ =>
      ce!id = Some co /\ field_offset ce f (co_members co) = OK (ofs, bf)
  | Tunion id _ =>
      ce!id = Some co /\ union_field_offset ce f (co_members co) = OK (ofs, bf)
  | _ => False
  end).
FEnd tr_is_bitfield_access.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_field: forall ce le dst e1 f ty sl1 a1 tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Efield e1 f ty)
            (sl1 ++ final dst (T.Efield a1 f ty)) (T.Efield a1 f ty) tmp.

Closing Fact tr_field_inv :
  forall ce le dst e1 f ty sl a tmp,
  tr_expr ce le dst (S.Efield e1 f ty) sl a tmp ->
  exists sl1 a1, sl = sl1 ++ final dst (T.Efield a1 f ty) /\ a = T.Efield a1 f ty
    /\ tr_expr ce le For_val e1 sl1 a1 tmp
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInduction eval_Eaddrof'.
FProof.
intros; fsimpl; auto using T.eval_Eaddrof.
Qed. FEnd eval_Eaddrof'.

FInduction typeof_Eaddrof'.
FProof.
intros; do 2 fsimpl; auto.
Qed. FEnd typeof_Eaddrof'.

FInduction eval_Ederef'.
FProof.
intros; fsimpl; auto using T.eval_Ederef.
Qed. FEnd eval_Ederef'.

FInduction typeof_Ederef'.
FProof.
intros; do 2 fsimpl; auto.
Qed. FEnd typeof_Ederef'.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil)
  by (intros; destruct H; subst dst; auto).
intros; fsimpl in *. rewrite H; auto. simpl; auto.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction is_bitfield_access_sound.
FProof.
- intros. fsimpl in *. rewrite e0 in H2. destruct H2 as (co' & delta' & E1 & E2). erewrite comp_env_preserved in e2; eauto.
  assert (A: forall id co co',
    (T.genv_cenv ge)!id = Some co -> (T.genv_cenv ge)!id = Some co' ->
    co' = co /\ complete_members (T.genv_cenv ge) (co_members co) = true).
  { intros. replace co'0 with co0 in * by congruence. split; auto.
    apply co_consistent_complete. eapply build_composite_env_consistent.
    subst ge; simpl. eapply prog_comp_env_eq. eauto. }
  exploit A. apply e1. apply E1. intros (E3 & E4). subst co'.
  assert (field_offset (S.genv_cenv ge0) i (co_members co) = field_offset (T.genv_cenv ge) i (co_members co)).
  { apply field_offset_stable. erewrite comp_env_preserved; eauto. auto. }
  congruence.
- intros. fsimpl in *. rewrite e0 in H2. destruct H2 as (co' & delta' & E1 & E2). erewrite comp_env_preserved in e2; eauto.
  assert (A: forall id co co',
    (T.genv_cenv ge)!id = Some co -> (T.genv_cenv ge)!id = Some co' ->
    co' = co /\ complete_members (T.genv_cenv ge) (co_members co) = true).
  { intros. replace co'0 with co0 in * by congruence. split; auto.
    apply co_consistent_complete. eapply build_composite_env_consistent.
    subst ge; simpl. eapply prog_comp_env_eq. eauto. }
  exploit A. apply e1. apply E1. intros (E3 & E4). subst co'.
  assert (union_field_offset (S.genv_cenv ge0) i (co_members co) = union_field_offset (T.genv_cenv ge) i (co_members co)).
  { apply union_field_offset_stable. erewrite comp_env_preserved; eauto. auto. }
  congruence.
Qed. FEnd is_bitfield_access_sound.

FInduction tr_simple_rvalue with tr_simple_lvalue.
FProof.
all: intros; apply tr_field_inv in H3; unpack H3; subst sl a0.
(* field struct *)
- rewrite <- (comp_env_preserved prog tprog ge tge) in * by auto.
  exploit H; eauto. intros [A [B C]]. subst sl1.
  split; auto. split. do 2 fsimpl; auto. rewrite B in e0. eapply T.eval_Efield_struct; eauto.
(* field union *)
- rewrite <- (comp_env_preserved prog tprog ge tge) in * by auto.
  exploit H; eauto. intros [A [B C]]. subst sl1.
  split; auto. split. do 2 fsimpl; auto. rewrite B in e0. eapply T.eval_Efield_union; eauto.
Qed. FEnd tr_simple_rvalue with tr_simple_lvalue.

FInduction typeof_context.
FProof.
all: intros; do 2 fsimpl; auto.
Qed. FEnd typeof_context.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
intros. apply tr_field_inv in H0; unpack H0; subst.
exploit H; eauto.
intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
- rewrite Q, app_assoc. eauto.
- auto.
- intros. rewrite app_assoc. fconstructor.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Efield l1 f ty := (Datatypes.S(esize l1)).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.
FEnd SimplExpr.

FEnd Comp_Field.


Trait Comp_Call extends Base, Comp_Builtin.

Family C.
FInductive expr : Type :=
| Ecall : expr -> exprlist -> type -> expr.

FRecursion typeof.
Case Ecall e args t := t.
FEnd typeof.

FInductive cont: Type :=
| Kcall: function ->           (* calling function *)
         env ->                (* local env of calling function *)
         (expr -> expr) ->     (* context of the call *)
         type ->               (* type of call expression *)
         cont -> cont.

FRecursion call_cont.
Case Kcall f e c ty k := (Kcall f e c ty k).
FEnd call_cont.

FRecursion is_call_cont.
Case Kcall f e c ty k := True.
FEnd is_call_cont.

FRecursion simple.
Case _ := false.
FEnd simple.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_call_left: forall k C el ty,
    leftcontext k RV C -> leftcontext k RV (fun x => Ecall (C x) el ty)
| lctx_call_right: forall k C e1 ty,
    simple e1 = true -> leftcontextlist k C ->
    leftcontext k RV (fun x => Ecall e1 (C x) ty).

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_call: forall ge f C rf rargs ty k e m targs tres cconv vf vargs fd,
    leftcontext RV RV C ->
    classify_fun (typeof rf) = fun_case_f targs tres cconv ->
    eval_simple_rvalue ge e m rf vf ->
    eval_simple_list ge e m rargs targs vargs ->
    Genv.find_funct (genv_genv ge) vf = Some fd ->
    type_of_fundef fd = Tfunction targs tres cconv ->
    estep ge (ExprState f (C (Ecall rf rargs ty)) k e m)
       E0 (Callstate fd vargs (Kcall f e C ty k) m).

FInductive sstep: genv -> state -> trace -> state -> Prop :=
| step_external_function: forall ge ef targs tres cc vargs k m vres t m',
    external_call ef (Genv.to_senv (genv_genv ge)) vargs m t vres m' ->
    sstep ge (Callstate (External ef targs tres cc) vargs k m)
        t (Returnstate vres k m').
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Scall: option ident -> expr -> list expr -> stmt. (* function call *)

FInductive cont: Type :=
| Kcall: option ident ->       (* where to store result *)
         function ->           (* calling function *)
         env ->                (* local env of calling function *)
         temp_env ->     (* temporary env of calling function *)
         cont -> cont.

FRecursion call_cont.
Case Kcall optid f e le k := (Kcall optid f e le k).
FEnd call_cont.

FRecursion is_call_cont.
Case Kcall optid f e le k := True.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case _ := (fun lbl k => None).
FEnd find_label with find_label_ls.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_call: forall ge f optid a al k e le m tyargs tyres cconv vf vargs fd,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge e le m a vf ->
    eval_exprlist ge e le m al tyargs vargs ->
    Genv.find_funct (genv_genv ge) vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    step ge (State f (Scall optid a al) k e le m)
      E0 (Callstate fd vargs (Kcall optid f e le k) m)
| step_external_function: forall ge ef targs tres cconv vargs k m vres t m',
    external_call ef (Genv.to_senv (genv_genv ge)) vargs m t vres m' ->
    step ge (Callstate (External ef targs tres cconv) vargs k m)
        t (Returnstate vres k m').
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.

FRecursion transl_expr with transl_exprlist.
Case Ecall r1 rl2 ty :=
  (fun ce dst =>
   do (sl1, a1) <- transl_expr r1 ce For_val;
   do (sl2, al2) <- transl_exprlist rl2 ce;
   match dst with
   | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
       do t <- gensym ty;
       ret (finish dst (sl1 ++ sl2 ++ T.Scall (Some t) a1 al2 :: nil)
                       (T.Etempvar t ty))
   | self__SimplExpr.For_effects =>
       ret (sl1 ++ sl2 ++ T.Scall None a1 al2 :: nil, dummy_expr)
   end).
FEnd transl_expr with transl_exprlist.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_call_effects: forall ce le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp,
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_exprlist ce le el2 sl2 al2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le For_effects (S.Ecall e1 el2 ty)
                 (sl1 ++ sl2 ++ T.Scall None a1 al2 :: nil)
                 any tmp
| tr_call_val: forall ce le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp,
    dst <> For_effects ->
    tr_expr ce le For_val e1 sl1 a1 tmp1 ->
    tr_exprlist ce le el2 sl2 al2 tmp2 ->
    list_disjoint tmp1 tmp2 -> In t tmp ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le dst (S.Ecall e1 el2 ty)
                 (sl1 ++ sl2 ++ T.Scall (Some t) a1 al2 :: final dst (T.Etempvar t ty))
                 (T.Etempvar t ty) tmp.

Closing Fact tr_call_inv :
  forall ce le dst e1 el2 ty sl a tmp,
  tr_expr ce le dst (S.Ecall e1 el2 ty) sl a tmp ->
  (exists sl1 a1 tmp1 sl2 al2 tmp2, dst = For_effects /\ sl = sl1 ++ sl2 ++ T.Scall None a1 al2 :: nil
    /\ tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_exprlist ce le el2 sl2 al2 tmp2
    /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp)
  \/ (exists sl1 a1 tmp1 sl2 al2 tmp2 t, dst <> For_effects /\ sl = sl1 ++ sl2 ++ T.Scall (Some t) a1 al2 :: final dst (T.Etempvar t ty)
    /\ a = T.Etempvar t ty /\  tr_expr ce le For_val e1 sl1 a1 tmp1 /\ tr_exprlist ce le el2 sl2 al2 tmp2
    /\ list_disjoint tmp1 tmp2 /\ In t tmp /\ incl tmp1 tmp /\ incl tmp2 tmp)
  by plain {intros *; intros H; inv H;
            [ left; repeat eexists; eauto | right; repeat eexists; eauto ]}.

FInduction tr_expr_invariant with tr_exprlist_invariant.
FProof.
all: intros; fconstructor.
Qed. FEnd tr_expr_invariant with tr_exprlist_invariant.

FInduction tr_expr_monotone with tr_exprlist_monotone.
FProof.
all: intros; fconstructor; unfold incl in *; eauto.
Qed. FEnd tr_expr_monotone with tr_exprlist_monotone.

FInductive tr_fundef : S.program -> S.fundef -> T.fundef -> Prop :=
| tr_external: forall p ef targs tres cconv,
    tr_fundef p (External ef targs tres cconv) (External ef targs tres cconv).

Closing Fact tr_fundef_external_inv :
  forall p ef targs tres cconv tfd,
  tr_fundef p (External ef targs tres cconv) tfd ->
  tfd = External ef targs tres cconv
  by plain {intros *; intros H; inv H; auto}.

FInduction tr_simple_expr_nil with tr_simple_exprlist_nil.
FProof.
all: intros; fsimpl in *; discriminate.
Qed. FEnd tr_simple_expr_nil with tr_simple_exprlist_nil.

FInduction tr_expr_leftcontext with tr_expr_leftcontextlist.
FProof.
(* call left *)
- intros. apply tr_call_inv in H0 as [|]; unpack H0; subst.
  (* for effects *)
  + exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
    TR. rewrite Q, <- app_assoc; eauto. red; auto.
    intros. rewrite app_assoc. fconstructor.
    eapply tr_exprlist_invariant; eauto. UNCHANGED.
  (* for val *)
  + exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
    TR. rewrite Q, <- app_assoc; eauto. red; auto.
    intros. rewrite app_assoc. fconstructor.
    eapply tr_exprlist_invariant; eauto. UNCHANGED.
(* call right *)
- intros. apply tr_call_inv in H0 as [|]; unpack H0; subst.
  (* for effects *)
  + assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
    exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
    TR. rewrite Q, <- app_assoc; eauto. red; auto.
    intros. rewrite app_assoc. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite <- app_assoc. fconstructor.
    eapply tr_expr_invariant; eauto. UNCHANGED.
  (* for val *)
  + assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
    exploit H; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
    TR. rewrite Q, <- app_assoc; eauto. red; auto.
    intros. rewrite app_assoc. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite <- app_assoc. fconstructor.
    eapply tr_expr_invariant; eauto. UNCHANGED.
Qed. FEnd tr_expr_leftcontext with tr_expr_leftcontextlist.

FInductive match_cont : composite_env -> S.cont -> T.cont -> Prop :=
| match_Kcall: forall prog tprog f e C ty k optid tf le sl tk a dest tmps ce,
    match_prog prog tprog ->
    tr_function prog.(prog_comp_env) f tf ->
    S.leftcontext S.RV S.RV C ->
    (forall v m, tr_top prog.(prog_comp_env) (T.globalenv tprog) e (T.set_opttemp optid v le) m dest (C (S.Eval v ty)) sl a tmps) ->
    match_cont_exp prog.(prog_comp_env) dest a k tk ->
    match_cont ce (S.Kcall f e C ty k)
    (T.Kcall optid tf e le (Kseqlist sl tk)).

FInduction match_cont_is_call_cont.
FProof.
intros. fconstructor.
Qed. FEnd match_cont_is_call_cont.

FInduction match_cont_call_cont.
FProof.
intros; do 2 fsimpl; fconstructor.
Qed. FEnd match_cont_call_cont.

FInduction tr_find_label_expr with tr_find_label_exprlist.
FProof.
all: intros; simpl; NoLabelTac.
Qed. FEnd tr_find_label_expr with tr_find_label_exprlist.

FRecursion esize with esizelist.
Case Ecall r1 rl2 ty := (Datatypes.S(esize r1 + esizelist rl2)%nat).
FEnd esize with esizelist.

FInduction leftcontext_size with leftcontextlist_size.
FProof.
all: intros; do 2 fsimpl; auto with arith.
Qed. FEnd leftcontext_size with leftcontextlist_size.

FLemma functions_translated:
  forall prog tprog ge tge, match_prog prog tprog ->
  S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall v f,
  Genv.find_funct (S.genv_genv ge) v = Some f ->
  exists tf,
  Genv.find_funct (T.genv_genv tge) v = Some tf /\ tr_fundef prog f tf.
  (* Linking is unsupported
  exists cu tf,
  Genv.find_funct (T.genv_genv tge) v = Some tf /\ tr_fundef cu f tf /\ linkorder cu prog. *)
FProofLemma.
intros. subst. simpl. (* apply (Genv.find_funct_match (proj1 H)). assumption. *) apply cheat.
Qed. CloseFLemma.

FLemma type_of_fundef_preserved:
  forall cu f tf, tr_fundef cu f tf ->
  T.type_of_fundef tf = S.type_of_fundef f.
FProofLemma.
intros. destruct f.
- apply tr_fundef_internal_inv in H; unpack H; subst. inv TEMP1; simpl.
  unfold T.type_of_function, S.type_of_function. congruence.
- apply tr_fundef_external_inv in H; unpack H; subst. reflexivity.
Qed. CloseFLemma.

FInduction estep_simulation.
FProof.
intros. inv MS.
exploit tr_top_leftcontext; eauto. clear TR.
intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
inv P.
- (* fdiscriminate. *) apply cheat.
- apply tr_call_inv in H0 as [|]; unpack H0; subst.
  (* for effects *)
  + exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit tr_simple_exprlist; eauto. intros [SL2 EV2].
    subst. simpl Kseqlist.
    exploit functions_translated; eauto. intros (tfd & J & K).
    eexists; split.
    left. eapply plus_left. fconstructor. apply star_one.
    fconstructor. rewrite <- TY1; eauto.
    exploit type_of_fundef_preserved; eauto. congruence.
    traceEq.
    econstructor. exact K. intros. fconstructor.
    intros. change sl2 with (nil ++ sl2). apply S.
    fconstructor. auto. do 2 fsimpl; auto.
  (* for value *)
  + exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
    exploit tr_simple_exprlist; eauto. intros [SL2 EV2].
    subst. simpl Kseqlist.
    exploit functions_translated; eauto. intros (tfd & J & K).
    eexists; split.
    left. eapply plus_left. fconstructor. apply star_one.
    fconstructor. rewrite <- TY1; eauto.
    exploit type_of_fundef_preserved; eauto. congruence.
    traceEq.
    econstructor. exact K. intros. fconstructor.
    intros. apply S.
    destruct dst'; fconstructor.
    fsimpl; auto. intros. fconstructor. rewrite H0; auto. apply PTree.gss.
    fsimpl; auto. intros. fconstructor. rewrite H0; auto. apply PTree.gss.
    intros. apply PTree.gso. intuition congruence.
    do 2 fsimpl; auto.
Qed. FEnd estep_simulation.

FInduction sstep_simulation.
FProof.
intros.
intros; inv MS.
(* external function *)
apply tr_fundef_external_inv in TR; subst.
econstructor; split.
left; apply plus_one. fconstructor.
eapply external_call_symbols_preserved; eauto. eapply senv_preserved; eauto.
econstructor; eauto.
Qed. FEnd sstep_simulation.
FEnd SimplExpr.

FEnd Comp_Call.


Trait Comp_Switch extends Base, Comp_break_continue.

Family C.
FInductive stmt : Type :=
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)

FInductive cont : Type :=
| Kswitch1: lbl_stmts -> cont -> cont
| Kswitch2: cont -> cont.

FRecursion call_cont.
Case Kswitch1 ls k := (call_cont k).
Case Kswitch2 k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case Sswitch e sl := (fun lbl k => find_label_ls sl lbl (Kswitch2 k)).
FEnd find_label with find_label_ls.

FRecursion select_switch_default about lbl_stmts
  motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons i s sl' := (match i with
  | None => LScons i s sl'
  | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts
  motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons i s sl' := (fun n => match i with
  | None => select_switch_case sl' n
  | Some c => if zeq c n then Some (LScons i s sl') else select_switch_case sl' n
  end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FInductive sstep : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f x sl k e m,
    sstep ge (State f (Sswitch x sl) k e m)
      E0 (ExprState f x (Kswitch1 sl k) e m)
| step_expr_switch: forall ge f ty sl k e m v n,
    sem_switch_arg v ty = Some n ->
    sstep ge (ExprState f (Eval v ty) (Kswitch1 sl k) e m)
      E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
| step_skip_break_switch: forall ge f x k e m,
    x = Sskip \/ x = Sbreak ->
    sstep ge (State f x (Kswitch2 k) e m)
      E0 (State f Sskip k e m)
| step_continue_switch: forall ge f k e m,
    sstep ge (State f Scontinue (Kswitch2 k) e m)
      E0 (State f Scontinue k e m).
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)

FInductive cont : Type :=
| Kswitch: cont -> cont.

FRecursion call_cont.
Case Kswitch k := (call_cont k).
FEnd call_cont.

FRecursion is_call_cont.
Case _ := False.
FEnd is_call_cont.

FRecursion find_label with find_label_ls.
Case Sswitch e sl := (fun lbl k => find_label_ls sl lbl (Kswitch k)).
FEnd find_label with find_label_ls.

FRecursion select_switch_default about lbl_stmts
  motive (fun (_ : lbl_stmts) => lbl_stmts) by _rect.
Case LSnil := LSnil.
Case LScons i s sl' := (match i with
  | None => LScons i s sl'
  | Some i => select_switch_default sl'
  end).
FEnd select_switch_default.

FRecursion select_switch_case about lbl_stmts
  motive (fun (_ : lbl_stmts) => Z -> option lbl_stmts) by _rect.
Case LSnil := (fun n => None).
Case LScons i s sl' := (fun n => match i with
  | None => select_switch_case sl' n
  | Some c => if zeq c n then Some (LScons i s sl') else select_switch_case sl' n
  end).
FEnd select_switch_case.

FDefinition select_switch := fun (n: Z) (sl: lbl_stmts) =>
  match select_switch_case sl n with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_switch: forall ge f a sl k e le m v n,
    eval_expr ge e le m a v ->
    sem_switch_arg v (typeof a) = Some n ->
    step ge (State f (Sswitch a sl) k e le m)
      E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
| step_skip_break_switch: forall ge f x k e le m,
    x = Sskip \/ x = Sbreak ->
    step ge (State f x (Kswitch k) e le m)
      E0 (State f Sskip k e le m)
| step_continue_switch: forall ge f k e le m,
    step ge (State f Scontinue (Kswitch k) e le m)
      E0 (State f Scontinue k e le m).
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.
FRecursion transl_stmt with transl_lblstmt.
Case Sswitch e ls :=
  (fun ce =>
    do (s', a) <- transl_expression e ce;
    do tls <- transl_lblstmt ls ce;
    ret (T.Sseq s' (T.Sswitch a tls))).
FEnd transl_stmt with transl_lblstmt.

FInductive tr_stmt: composite_env -> S.stmt -> T.stmt -> Prop :=
| tr_switch: forall ce r ls s' a tls,
    tr_expression ce r s' a ->
    tr_lblstmts ce ls tls ->
    tr_stmt ce (S.Sswitch r ls) (T.Sseq s' (T.Sswitch a tls)).

Closing Fact tr_switch_inv :
  forall ce r ls ts,
  tr_stmt ce (S.Sswitch r ls) ts ->
  exists s' a tls, ts = T.Sseq s' (T.Sswitch a tls) /\ tr_expression ce r s' a /\ tr_lblstmts ce ls tls
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInductive match_cont : composite_env -> S.cont -> T.cont -> Prop :=
| match_Kswitch2: forall ce k tk,
    match_cont ce k tk ->
    match_cont ce (S.Kswitch2 k) (T.Kswitch tk)
with match_cont_exp : composite_env -> destination -> T.expr -> S.cont -> T.cont -> Prop :=
| match_Kswitch1: forall ce ls k a tls tk,
    tr_lblstmts ce ls tls ->
    match_cont ce k tk ->
    match_cont_exp ce For_val a (S.Kswitch1 ls k) (T.Kseq (T.Sswitch a tls) tk).

FInduction match_cont_is_call_cont.
FProof.
intros. fsimpl in *. contradiction.
Qed. FEnd match_cont_is_call_cont.

FInduction match_cont_call_cont.
FProof.
intros; do 2 fsimpl; auto; fconstructor.
Qed. FEnd match_cont_call_cont.

Closing Fact match_cont_switch_inv :
  forall ce k tk,
  match_cont ce (S.Kswitch2 k) tk ->
  exists tk', tk = T.Kswitch tk' /\ match_cont ce k tk'
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

Closing Fact match_cont_exp_switch_inv :
  forall ce dst a ls k tk,
  match_cont_exp ce dst a (S.Kswitch1 ls k) tk ->
  exists tls tk', dst = For_val /\ tk = T.Kseq (T.Sswitch a tls) tk'
    /\ match_cont ce k tk' /\ tr_lblstmts ce ls tls
  by plain {intros *; intros H; inv H; repeat eexists; eauto}.

FInduction tr_select_switch_DFL
  about tr_lblstmts
  motive (fun ce ls tls (_ : tr_lblstmts ce ls tls) =>
    tr_lblstmts ce (S.select_switch_default ls) (T.select_switch_default tls)).
FProof.
- do 2 fsimpl. fconstructor.
- intros. do 2 fsimpl. destruct c. auto. fconstructor.
Qed. FEnd tr_select_switch_DFL.

FInduction tr_select_switch_CASE
  about tr_lblstmts
    motive (fun ce ls tls (_ : tr_lblstmts ce ls tls) =>
        forall n,
        match S.select_switch_case ls n with
        | None =>
            T.select_switch_case tls n = None
        | Some ls' =>
            exists tls', T.select_switch_case tls n = Some tls' /\ tr_lblstmts ce ls' tls'
        end).
FProof.
all: intros; do 2 fsimpl.
- auto.
- destruct c.
  + destruct (zeq z n).
    * eexists. split. eauto. fconstructor.
    * apply H.
  + apply H.
Qed. FEnd tr_select_switch_CASE.

FLemma tr_select_switch :
  forall ce n ls tls,
  tr_lblstmts ce ls tls ->
  tr_lblstmts ce (S.select_switch n ls) (T.select_switch n tls).
FProofLemma.
  intros. unfold S.select_switch, T.select_switch.
  pose proof (tr_select_switch_CASE ce ls tls H n) as CASE.
  destruct (S.select_switch_case ls n) as [ls'|].
  destruct CASE as [tls' [P Q]]. rewrite P. auto.
  rewrite CASE. apply tr_select_switch_DFL; auto.
Qed. CloseFLemma.

FInduction tr_find_label with tr_find_label_ls.
FProof.
intros. apply tr_switch_inv in TR; unpack TR; subst.
fsimpl. fsimpl. rewrite (tr_find_label_expression ce tge lbl _ _ _ TEMP).
fsimpl. apply H; auto. fconstructor.
Qed. FEnd tr_find_label with tr_find_label_ls.

FRecursion measure_stmt.
Case _ := 0%nat.
FEnd measure_stmt.

FInduction sstep_simulation.
FProof.
all: intros; inv MS.
(* switch *)
- apply tr_switch_inv in TR; unpack TR; subst. inv TEMP.
  eexists. split.
  + left. eapply plus_left. fconstructor. apply push_seq. traceEq.
  + econstructor; eauto. fconstructor.
(* expr switch *)
- apply match_cont_exp_switch_inv in MK; unpack MK; subst.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. eapply plus_two. fconstructor. fconstructor. traceEq.
  + econstructor; eauto. apply tr_seq_of_labeled_statement. apply tr_select_switch. auto.
    fconstructor.
(* skip-or-break switch *)
- assert (ts = T.Sskip \/ ts = T.Sbreak).
  { destruct o; subst x; [ apply tr_skip_inv in TR | apply tr_break_inv in TR ]; auto. }
  apply match_cont_switch_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_skip_break_switch; auto.
  + econstructor; eauto. fconstructor.
(* continue switch *)
- apply tr_continue_inv in TR. apply match_cont_switch_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. apply T.step_continue_switch.
  + econstructor; eauto. fconstructor.
Qed. FEnd sstep_simulation.
FEnd SimplExpr.

FEnd Comp_Switch.

Family Comp extends
  Base,
  Comp_break_continue,
  Comp_Loops,
  Comp_Switch,
  Comp_Builtin,
  Comp_Call,
  Comp_Heap,
  Comp_Field.

Family SimplExpr.
Final Family S := C.
Final Family T := Clight.
FEnd SimplExpr.

FEnd Comp.
