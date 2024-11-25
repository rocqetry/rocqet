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

MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: self__C.stmt
}.
FEnd function.

FDefinition var_names := fun (vars: list(ident * type)) =>
  List.map (@fst ident type) vars.

FDefinition fundef := Ctypes.fundef function.

FDefinition type_of_function : function -> type := fun f =>
  Tfunction (type_of_params (self__C.fn_params f)) (self__C.fn_return f) (self__C.fn_callconv f).

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
MetaData genv.
Record genv := { genv_genv :> Genv.t self__C.fundef type; genv_cenv :> composite_env }.
FEnd genv.

FDefinition globalenv : program -> genv := fun p =>
  {| self__C.genv_genv := Genv.globalenv p; self__C.genv_cenv := p.(prog_comp_env) |}.

FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (self__C.genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z) := fun ge e =>
    List.map (block_of_binding ge) (PTree.elements e).

MetaData assign_loc.
Inductive assign_loc (ge : self__C.genv) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                              bitfield -> val -> trace -> mem -> val -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ge ty m b ofs Full v E0 m' v
  | assign_loc_volatile: forall v chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store (self__C.genv_genv ge) chunk m b ofs v t m' ->
      assign_loc ge ty m b ofs Full v t m' v
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (alignof_blockcopy (self__C.genv_cenv ge) ty | Ptrofs.unsigned ofs') ->
      (alignof_blockcopy (self__C.genv_cenv ge) ty | Ptrofs.unsigned ofs) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof (self__C.genv_cenv ge) ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof (self__C.genv_cenv ge) ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof (self__C.genv_cenv ge) ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ge ty m b ofs Full (Vptr b' ofs') E0 m' (Vptr b' ofs')
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ge ty m b ofs (Bits sz sg pos width) v E0 m' v'.
FEnd assign_loc.

MetaData alloc_variables.
Inductive alloc_variables (ge : self__C.genv) : self__C.env -> mem ->
                           list (ident * type) ->
                           self__C.env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables ge e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof (self__C.genv_cenv ge) ty) = (m1, b1) ->
      alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables ge e m ((id, ty) :: vars) e2 m2.
FEnd alloc_variables.

MetaData bind_parameters.
Inductive bind_parameters (ge : self__C.genv) (e: self__C.env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ge e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl v1' b m1 m2,
      PTree.get id e = Some(b, ty) ->
      self__C.assign_loc ge ty m b Ptrofs.zero Full v1 E0 m1 v1' ->
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

MetaData state.
Inductive state: Type :=
| State(* execution of a stmt *)
    (f: self__C.function) (s: self__C.stmt)
    (k: self__C.cont) (e: self__C.env) (m: mem) : state
| ExprState(* reduction of an expression *)
    (f: self__C.function) (r: self__C.expr)
    (k: self__C.cont) (e: self__C.env) (m: mem) : state
| Callstate(* calling a function *)
    (fd: self__C.fundef) (args: list val)
    (k: self__C.cont) (m: mem) : state
| Returnstate(* returning from a function *)
    (res: val) (k: self__C.cont) (m: mem) : state
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
    sem_binary_operation (self__C.genv_cenv ge) op v1 (typeof r1) v2 (typeof r2) m = Some v ->
    eval_simple_rvalue ge e m (Ebinop op r1 r2 ty) v
| esr_cast: forall ge e m ty r1 v1 v,
    eval_simple_rvalue ge e m r1 v1 ->
    Cop.sem_cast v1 (typeof r1) ty m = Some v ->
    eval_simple_rvalue ge e m (Ecast r1 ty) v
| esr_sizeof: forall ge e m ty1 ty,
    eval_simple_rvalue ge e m (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.sizeof (self__C.genv_cenv ge) ty1)))
| esr_alignof: forall ge e m ty1 ty,
    eval_simple_rvalue ge e m (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.alignof (self__C.genv_cenv ge) ty1))).

FDefinition is_val : expr -> Prop := fun e => exists v ty, e = Eval v ty.

MetaData kind.
Inductive kind : Type := LV | RV.
FEnd kind.

FInductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
| lctx_top: forall k,
    leftcontext k k (fun x => x)
| lctx_unop: forall k C op ty,
    leftcontext k self__C.RV C -> leftcontext k self__C.RV (fun x => Eunop op (C x) ty)
| lctx_binop_left: forall k C op e2 ty,
    leftcontext k self__C.RV C -> leftcontext k self__C.RV (fun x => Ebinop op (C x) e2 ty)
| lctx_binop_right: forall k C op e1 ty,
    simple e1 = true -> leftcontext k self__C.RV C ->
    leftcontext k self__C.RV (fun x => Ebinop op e1 (C x) ty)
| lctx_cast: forall k F ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Ecast (F x) ty)
| lctx_seqand: forall k F r2 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Eseqand (F x) r2 ty)
| lctx_seqor: forall k F r2 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Eseqor (F x) r2 ty)
| lctx_condition: forall k F r2 r3 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Econdition (F x) r2 r3 ty)
| lctx_comma: forall k F e2 ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Ecomma (F x) e2 ty)
| lctx_paren: forall k F tycast ty,
    leftcontext k self__C.RV F -> leftcontext k self__C.RV (fun x => Eparen (F x) tycast ty)

with leftcontextlist: kind -> (expr -> exprlist) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k self__C.RV C -> leftcontextlist k (fun x => Econs (C x) el)
  | lctx_list_tail: forall k C e1,
      simple e1 = true -> leftcontextlist k C ->
      leftcontextlist k (fun x => Econs e1 (C x)).

Closing Fact leftcontext_val_top :
  forall r v ty c k1 k2,
  c r = Eval v ty ->
  leftcontext k1 k2 c ->
  c = (fun x => x)
  by {intros until k2; intros H1 H2; inv H2; try discriminate; auto}.

FInductive estep: genv -> state -> trace -> state -> Prop :=
| step_expr: forall ge f r k e m v ty,
    eval_simple_rvalue ge e m r v ->
    ~ is_val r ->
    ty = typeof r ->
    estep ge (self__C.ExprState f r k e m)
      E0 (self__C.ExprState f (Eval v ty) k e m)

| step_seqand_true: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some true ->
    estep ge (self__C.ExprState f (F (Eseqand r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eparen r2 type_bool ty)) k e m)
| step_seqand_false: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some false ->
    estep ge (self__C.ExprState f (F (Eseqand r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eval (Vint Int.zero) ty)) k e m)

| step_seqor_true: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some true ->
    estep ge (self__C.ExprState f (F (Eseqor r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eval (Vint Int.one) ty)) k e m)
| step_seqor_false: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some false ->
    estep ge (self__C.ExprState f (F (Eseqor r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F (Eparen r2 type_bool ty)) k e m)

| step_condition: forall ge f F r1 r2 r3 ty k e m v b,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    Cop.bool_val v (typeof r1) m = Some b ->
    estep ge (self__C.ExprState f (F (Econdition r1 r2 r3 ty)) k e m)
      E0 (self__C.ExprState f (F (Eparen (if b then r2 else r3) ty ty)) k e m)

| step_comma: forall ge f F r1 r2 ty k e m v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r1 v ->
    ty = typeof r2 ->
    estep ge (self__C.ExprState f (F (Ecomma r1 r2 ty)) k e m)
      E0 (self__C.ExprState f (F r2) k e m)

| step_paren: forall ge f F r tycast ty k e m v1 v,
    leftcontext self__C.RV self__C.RV F ->
    eval_simple_rvalue ge e m r v1 ->
    sem_cast v1 (typeof r) tycast m = Some v ->
    estep ge (self__C.ExprState f (F (Eparen r tycast ty)) k e m)
      E0 (self__C.ExprState f (F (Eval v ty)) k e m).

FInductive sstep: genv -> state -> trace -> state -> Prop :=
| step_do_1: forall ge f x k e m,
    sstep ge (self__C.State f (Sdo x) k e m)
      E0 (self__C.ExprState f x (Kdo k) e m)
| step_do_2: forall ge f v ty k e m,
    sstep ge (self__C.ExprState f (Eval v ty) (Kdo k) e m)
      E0 (self__C.State f Sskip k e m)

| step_seq: forall ge f s1 s2 k e m,
    sstep ge (self__C.State f (Sseq s1 s2) k e m)
      E0 (self__C.State f s1 (Kseq s2 k) e m)
| step_skip_seq: forall ge f s k e m,
    sstep ge (self__C.State f Sskip (Kseq s k) e m)
      E0 (self__C.State f s k e m)

| step_ifthenelse_1: forall ge f a s1 s2 k e m,
    sstep ge (self__C.State f (Sifthenelse a s1 s2) k e m)
      E0 (self__C.ExprState f a (Kifthenelse s1 s2 k) e m)
| step_ifthenelse_2: forall ge f v ty s1 s2 k e m b,
    Cop.bool_val v ty m = Some b ->
    sstep ge (self__C.ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m)
      E0 (self__C.State f (if b then s1 else s2) k e m)

| step_return_0: forall ge f k e m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    sstep ge (self__C.State f (Sreturn None) k e m)
      E0 (self__C.Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f x k e m,
      sstep ge (self__C.State f (Sreturn (Some x)) k e m)
        E0 (self__C.ExprState f x (Kreturn k) e m)
| step_return_2: forall ge f v1 ty k e m v2 m',
      Cop.sem_cast v1 ty (self__C.fn_return f) m = Some v2 ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      sstep ge (self__C.ExprState f (Eval v1 ty) (Kreturn k) e m)
        E0 (self__C.Returnstate v2 (call_cont k) m')
| step_skip_call: forall ge f k e m m',
   is_call_cont k ->
   Mem.free_list m (blocks_of_env ge e) = Some m' ->
   sstep ge (self__C.State f Sskip k e m)
     E0 (self__C.Returnstate Vundef k m')

| step_label: forall ge f lbl s k e m,
      sstep ge (self__C.State f (Slabel lbl s) k e m)
         E0 (self__C.State f s k e m)

| step_goto: forall ge f lbl k e m s' k',
    find_label (self__C.fn_body f) lbl (call_cont k) = Some (s', k') ->
    sstep ge (self__C.State f (Sgoto lbl) k e m)
       E0 (self__C.State f s' k' e m)

| step_internal_function: forall ge f vargs k m e m1 m2,
   list_norepet (var_names (self__C.fn_params f) ++ var_names (self__C.fn_vars f)) ->
   alloc_variables ge empty_env m ((self__C.fn_params f) ++ (self__C.fn_vars f)) e m1 ->
   bind_parameters ge e m1 (self__C.fn_params f) vargs m2 ->
   sstep ge (self__C.Callstate (Internal f) vargs k m)
      E0 (self__C.State f (self__C.fn_body f) k e m2).

FDefinition step : genv -> state -> trace -> state -> Prop := fun ge S t S' =>
  estep ge S t S' \/ sstep ge S t S'.

MetaData initial_state.
Inductive initial_state (p: self__C.program): self__C.state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := self__C.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol (self__C.genv_genv ge) p.(prog_main) = Some b ->
      Genv.find_funct_ptr (self__C.genv_genv ge) b = Some f ->
      self__C.type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (self__C.Callstate f nil self__C.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__C.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__C.Returnstate (Vint r) self__C.Kstop m) r.
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

MetaData function.
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: self__Clight.stmt
}.
FEnd function.

FDefinition fundef := Ctypes.fundef function.

FDefinition type_of_function : function -> type := fun f =>
  Tfunction (type_of_params (self__Clight.fn_params f)) (self__Clight.fn_return f) (self__Clight.fn_callconv f).

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

MetaData genv.
Record genv := { genv_genv :> Genv.t self__Clight.fundef type; genv_cenv :> composite_env }.
FEnd genv.
FDefinition globalenv : program -> genv := fun p =>
  {| self__Clight.genv_genv := Genv.globalenv p; self__Clight.genv_cenv := p.(prog_comp_env) |}.


FDefinition env := PTree.t (block * type).
FDefinition empty_env: env := (PTree.empty (block * type)).
FDefinition temp_env := PTree.t val.

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
    sem_binary_operation (self__Clight.genv_cenv ge) op v1 (typeof a1) v2 (typeof a2) m = Some v ->
    eval_expr ge e le m (Ebinop op a1 a2 ty) v
| eval_Ecast: forall ge e le m a ty v1 v,
    eval_expr ge e le m a v1 ->
    Cop.sem_cast v1 (typeof a) ty m = Some v ->
    eval_expr ge e le m (Ecast a ty) v
| eval_Etempvar: forall ge e le m id ty v,
    PTree.get id le = Some v ->
    eval_expr ge e le m (Etempvar id ty) v
| eval_Esizeof: forall ge e le m ty1 ty,
    eval_expr ge e le m (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.sizeof (self__Clight.genv_cenv ge) ty1)))
| eval_Ealignof: forall ge e le m ty1 ty,
    eval_expr ge e le m (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (Ctypes.alignof (self__Clight.genv_cenv ge) ty1))).

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

MetaData state.
Inductive state: Type :=
  | State
      (f: self__Clight.function)
      (s: self__Clight.stmt)
      (k: self__Clight.cont)
      (e: self__Clight.env)
      (le: self__Clight.temp_env)
      (m: mem) : state
  | Callstate
      (fd: self__Clight.fundef)
      (args: list val)
      (k: self__Clight.cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: self__Clight.cont)
      (m: mem) : state.
FEnd state.

FDefinition block_of_binding := fun (ge: genv) (id_b_ty: ident * (block * type)) =>
  match id_b_ty with (id, (b, ty)) => (b, 0, Ctypes.sizeof (self__Clight.genv_cenv ge) ty) end.

FDefinition blocks_of_env : genv -> env -> list (block * Z * Z)  := fun ge e =>
  List.map (block_of_binding ge) (PTree.elements e).

(* To be overriden in SimplExpr & Cshmgen *)
FOpaque Definition function_entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop := cheat.

FInductive step : genv -> state -> trace -> state -> Prop :=
| step_skip_seq: forall ge f s k e le m,
  step ge (self__Clight.State f Sskip (Kseq s k) e le m)
    E0 (self__Clight.State f s k e le m)
| step_set: forall ge f id a k e le m v,
  eval_expr ge e le m a v ->
  step ge (self__Clight.State f (Sset id a) k e le m)
    E0 (self__Clight.State f Sskip k e (PTree.set id v le) m)
| step_seq: forall ge f s1 s2 k e le m,
  step ge (self__Clight.State f (Sseq s1 s2) k e le m)
    E0 (self__Clight.State f s1 (Kseq s2 k) e le m)
| step_ifthenelse: forall ge f a s1 s2 k e le m v1 b,
    eval_expr ge e le m a v1 ->
    Cop.bool_val v1 (typeof a) m = Some b ->
    step ge (self__Clight.State f (Sifthenelse a s1 s2) k e le m)
      E0 (self__Clight.State f (if b then s1 else s2) k e le m)
| step_return_0: forall ge f k e le m m',
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f (Sreturn None) k e le m)
      E0 (self__Clight.Returnstate Vundef (call_cont k) m')
| step_return_1: forall ge f a k e le m v v' m',
    eval_expr ge e le m a v ->
    Cop.sem_cast v (typeof a) (self__Clight.fn_return f) m = Some v' ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f (Sreturn (Some a)) k e le m)
      E0 (self__Clight.Returnstate v' (call_cont k) m')
| step_skip_call: forall ge f k e le m m',
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    step ge (self__Clight.State f Sskip k e le m)
      E0 (self__Clight.Returnstate Vundef k m')
| step_label: forall ge f lbl s k e le m,
  step ge (self__Clight.State f (Slabel lbl s) k e le m)
    E0 (self__Clight.State f s k e le m)
| step_goto: forall ge f lbl k e le m s' k',
  find_label (self__Clight.fn_body f) lbl (call_cont k) = Some (s', k') ->
  step ge (self__Clight.State f (Sgoto lbl) k e le m)
    E0 (self__Clight.State f s' k' e le m)
| step_internal_function: forall ge f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      step ge (self__Clight.Callstate (Internal f) vargs k m)
        E0 (self__Clight.State f (self__Clight.fn_body f) k e le m1).

MetaData initial_state.
Inductive initial_state (p: self__Clight.program): self__Clight.state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      self__Clight.type_of_fundef f = Tfunction nil type_int32s cc_default ->
      initial_state p (self__Clight.Callstate f nil self__Clight.Kstop m0).
FEnd initial_state.

MetaData final_state.
Inductive final_state: self__Clight.state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (self__Clight.Returnstate (Vint r) self__Clight.Kstop m) r.
FEnd final_state.

FEnd Clight.

(* C -> Clight *)
Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

Local Open Scope gensym_monad_scope.

MetaData makeseq_rec.
Fixpoint makeseq_rec (s: self__SimplExpr.T.stmt) (l: list self__SimplExpr.T.stmt) : self__SimplExpr.T.stmt :=
   match l with
   | nil => s
   | s' :: l' => makeseq_rec (self__SimplExpr.T.Sseq s s') l'
    end.
FEnd makeseq_rec.

FDefinition makeseq : list self__SimplExpr.T.stmt -> self__SimplExpr.T.stmt := fun l =>
  makeseq_rec self__SimplExpr.T.Sskip l.

MetaData set_destination binds SDbase, SDcons.
Inductive set_destination : Type :=
| SDbase (tycast ty: type) (tmp: ident)
| SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).
FEnd set_destination.

MetaData destination binds For_val, For_effects, For_set.
Inductive destination : Type :=
| For_val
| For_effects
| For_set (sd: self__SimplExpr.set_destination).
FEnd destination.

MetaData do_set.
Fixpoint do_set (sd: self__SimplExpr.set_destination) (a: self__SimplExpr.T.expr) : list self__SimplExpr.T.stmt :=
    match sd with
    | self__SimplExpr.SDbase tycast ty tmp => self__SimplExpr.T.Sset tmp (self__SimplExpr.T.Ecast a tycast) :: nil
    | self__SimplExpr.SDcons tycast ty tmp sd' => self__SimplExpr.T.Sset tmp (self__SimplExpr.T.Ecast a tycast) :: do_set sd' (self__SimplExpr.T.Etempvar tmp ty)
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
Function makeif (a: self__SimplExpr.T.expr) (s1 s2: self__SimplExpr.T.stmt) : self__SimplExpr.T.stmt :=
  match self__SimplExpr.eval_simpl_expr a with
  | Some v =>
      match Cop.bool_val v (self__SimplExpr.T.typeof a) Mem.empty with
      | Some b => if b then s1 else s2
      | None => self__SimplExpr.T.Sifthenelse a s1 s2
      end
  | None => self__SimplExpr.T.Sifthenelse a s1 s2
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
          do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
          ret (finish dst sl1 (T.Ecast a1 ty))
      | self__SimplExpr.For_effects =>
          transl_expr r1 ce self__SimplExpr.For_effects end).
Case Ecomma r1 r2 ty :=
   (fun ce dst =>
      do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_effects;
      do (sl2, a2) <- transl_expr r2 ce dst;
      ret (sl1 ++ sl2, a2)).
Case Econdition r1 r2 r3 ty :=
  (fun ce dst =>
      do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase ty ty t in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd);
          do (sl3, a3) <- transl_expr r3 ce (self__SimplExpr.For_set sd);
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_effects;
          do (sl3, a3) <- transl_expr r3 ce self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons ty ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd');
          do (sl3, a3) <- transl_expr r3 ce (self__SimplExpr.For_set sd');
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      end).
Case Eseqor r1 r2 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd);
          ret (sl1 ++
               makeif a1 (T.Sset t (T.Econst_int Int.one ty)) (makeseq sl2) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq (do_set sd (T.Econst_int Int.one ty))) (makeseq sl2) :: nil,
               dummy_expr)
      end).
Case Eseqand r1 r2 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
      match dst with
      | self__SimplExpr.For_val =>
          do t <- gensym ty;
          let sd := self__SimplExpr.SDbase type_bool ty t in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd);
          ret (sl1 ++
               makeif a1 (makeseq sl2) (T.Sset t (T.Econst_int Int.zero ty)) :: nil,
               T.Etempvar t ty)
      | self__SimplExpr.For_effects =>
          do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_effects;
          ret (sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil, dummy_expr)
      | self__SimplExpr.For_set sd =>
          do t <- temp_for_sd ty sd;
          let sd' := self__SimplExpr.SDcons type_bool ty t sd in
          do (sl2, a2) <- transl_expr r2 ce (self__SimplExpr.For_set sd');
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (T.Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      end).
Case Esizeof ty' ty := (fun ce dst => ret (finish dst nil (T.Esizeof ty' ty))).
Case Ealignof ty' ty := (fun ce dst => ret (finish dst nil (T.Ealignof ty' ty))).
Case Eparen e tycast ty := (fun ce dst => error (msg "SimplExpr.transl_expr: paren")).
Case Eunop op r1 ty :=
  (fun ce dst =>
    do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
    ret (finish dst sl1 (T.Eunop op a1 ty))).
Case Ebinop op r1 r2 ty :=
  (fun ce dst =>
     do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
     do (sl2, a2) <- transl_expr r2 ce self__SimplExpr.For_val;
     ret (finish dst (sl1 ++ sl2) (T.Ebinop op a1 a2 ty))).

Case Enil := (fun ce => ret (nil, nil)).
Case Econs r1 rl2 :=
  (fun ce =>
     do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
     do (sl2, al2) <- transl_exprlist rl2 ce;
      ret (sl1 ++ sl2, a1 :: al2)).
FEnd transl_expr with transl_exprlist.

FDefinition transl_expression : S.expr -> composite_env -> mon (T.stmt * T.expr) := fun r ce =>
  do (sl, a) <- transl_expr r ce self__SimplExpr.For_val; ret (makeseq sl, a).

FDefinition transl_expr_stmt : S.expr -> composite_env -> mon T.stmt := fun r ce =>
  do (sl, a) <- transl_expr r ce self__SimplExpr.For_effects; ret (makeseq sl).

FDefinition transl_if : S.expr -> T.stmt -> T.stmt -> composite_env -> mon T.stmt  := fun r s1 s2 ce =>
  do (sl, a) <- transl_expr r ce self__SimplExpr.For_val;
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
FDefinition final : self__SimplExpr.destination -> T.expr -> list T.stmt := fun dst a =>
match dst with
| self__SimplExpr.For_val => nil
| self__SimplExpr.For_effects => nil
| self__SimplExpr.For_set sd => do_set sd a
end.

FInductive tr_expr : composite_env -> T.temp_env -> destination -> S.expr -> list T.stmt -> T.expr -> list ident -> Prop :=
| tr_val_effect: forall ce le v ty any tmp,
    tr_expr ce le self__SimplExpr.For_effects (S.Eval v ty) nil any tmp
| tr_val_value: forall ce le v ty a tmp,
    T.typeof a = ty ->
    (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      T.eval_expr tge e le' m a v) ->
    tr_expr ce le self__SimplExpr.For_val (S.Eval v ty) nil a tmp
| tr_val_set: forall ce le sd v ty a any tmp,
    T.typeof a = ty ->
    (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      T.eval_expr tge e le' m a v) ->
    tr_expr ce le (self__SimplExpr.For_set sd) (S.Eval v ty)
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
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Eunop op e1 ty)
                (sl1 ++ final dst (T.Eunop op a1 ty))
                (T.Eunop op a1 ty) tmp
| tr_binop: forall ce le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le self__SimplExpr.For_val e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le dst (S.Ebinop op e1 e2 ty)
                (sl1 ++ sl2 ++ final dst (T.Ebinop op a1 a2 ty))
                (T.Ebinop op a1 a2 ty) tmp
| tr_cast_effects: forall ce le e1 ty sl1 a1 any tmp,
    tr_expr ce le self__SimplExpr.For_effects e1 sl1 a1 tmp ->
    tr_expr ce le self__SimplExpr.For_effects (S.Ecast e1 ty)
                sl1 any tmp
| tr_cast_val: forall ce le dst e1 ty sl1 a1 tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp ->
    tr_expr ce le dst (S.Ecast e1 ty)
                (sl1 ++ final dst (T.Ecast a1 ty))
                (T.Ecast a1 ty) tmp
| tr_seqand_val: forall ce le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le self__SimplExpr.For_val (S.Eseqand e1 e2 ty)
          (sl1 ++ makeif a1 (makeseq sl2)
                            (T.Sset t (T.Econst_int Int.zero ty)) :: nil)
          (T.Etempvar t ty) tmp
| tr_seqand_effects: forall ce le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le self__SimplExpr.For_effects (S.Eseqand e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil)
                  any tmp
| tr_seqand_set: forall ce le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le (self__SimplExpr.For_set sd) (S.Eseqand e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq sl2)
                                    (makeseq (do_set sd (T.Econst_int Int.zero ty))) :: nil)
                  any tmp
| tr_seqor_val: forall ce le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le self__SimplExpr.For_val (S.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 (T.Sset t (T.Econst_int Int.one ty))
                                    (makeseq sl2) :: nil)
                  (T.Etempvar t ty) tmp
| tr_seqor_effects: forall ce le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le self__SimplExpr.For_effects (S.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil)
                  any tmp
| tr_seqor_set: forall ce le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
    tr_expr ce le (self__SimplExpr.For_set sd) (S.Eseqor e1 e2 ty)
                  (sl1 ++ makeif a1 (makeseq (do_set sd (T.Econst_int Int.one ty)))
                                    (makeseq sl2) :: nil)
                  any tmp
| tr_condition_val: forall ce le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e2 sl2 a2 tmp2 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
    tr_expr ce le self__SimplExpr.For_val (S.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    (T.Etempvar t ty) tmp
| tr_condition_effects: forall ce le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le self__SimplExpr.For_effects e2 sl2 a2 tmp2 ->
    tr_expr ce le self__SimplExpr.For_effects e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
    tr_expr ce le self__SimplExpr.For_effects (S.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    any tmp
| tr_condition_set: forall ce le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
    tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e2 sl2 a2 tmp2 ->
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e3 sl3 a3 tmp3 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint tmp1 tmp3 ->
    incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
    tr_expr ce le (self__SimplExpr.For_set sd) (S.Econdition e1 e2 e3 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                    any tmp
| tr_comma: forall ce le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
    tr_expr ce le self__SimplExpr.For_effects e1 sl1 a1 tmp1 ->
    tr_expr ce le dst e2 sl2 a2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_expr ce le dst (S.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
| tr_paren_val: forall ce le e1 tycast ty sl1 a1 t tmp,
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase tycast ty t)) e1 sl1 a1 tmp ->
    In t tmp ->
    tr_expr ce le self__SimplExpr.For_val (S.Eparen e1 tycast ty) sl1 (T.Etempvar t ty) tmp
| tr_paren_effects: forall ce le e1 tycast ty sl1 a1 tmp any,
    tr_expr ce le self__SimplExpr.For_effects e1 sl1 a1 tmp ->
    tr_expr ce le self__SimplExpr.For_effects (S.Eparen e1 tycast ty) sl1 any tmp
| tr_paren_set: forall ce le t sd e1 tycast ty sl1 a1 tmp any,
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons tycast ty t sd)) e1 sl1 a1 tmp ->
    In t tmp ->
    tr_expr ce le (self__SimplExpr.For_set sd) (S.Eparen e1 tycast ty) sl1 any tmp

with tr_exprlist : composite_env -> T.temp_env -> S.exprlist -> list T.stmt -> list T.expr -> list ident -> Prop :=
| tr_nil: forall ce le tmp,
    tr_exprlist ce le S.Enil nil nil tmp
| tr_cons: forall ce le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp,
      tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1 ->
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
  by plain {intros until tmp; intros H; inv H; eauto}.

Closing Fact tr_sizeof_inv :
  forall ce le dst ty' ty sl a tmp,
  tr_expr ce le dst (S.Esizeof ty' ty) sl a tmp ->
  sl = final dst (T.Esizeof ty' ty)
  /\ a = T.Esizeof ty' ty
  by plain {intros until tmp; intros H; inv H; eauto}.

Closing Fact tr_alignof_inv :
  forall ce le dst ty' ty sl a tmp,
  tr_expr ce le dst (S.Ealignof ty' ty) sl a tmp ->
  sl = final dst (T.Ealignof ty' ty)
  /\ a = T.Ealignof ty' ty
  by plain {intros until tmp; intros H; inv H; eauto}.

Closing Fact tr_unop_inv :
  forall ce le dst op e1 ty sl a tmp,
  tr_expr ce le dst (S.Eunop op e1 ty) sl a tmp ->
  exists sl1 a1,
  sl = sl1 ++ final dst (T.Eunop op a1 ty)
  /\ a = T.Eunop op a1 ty
  /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_binop_inv :
  forall ce le dst op e1 e2 ty sl a tmp,
  tr_expr ce le dst (S.Ebinop op e1 e2 ty) sl a tmp ->
  exists sl1 a1 tmp1 sl2 a2 tmp2,
  sl = sl1 ++ sl2 ++ final dst (T.Ebinop op a1 a2 ty)
  /\ a = T.Ebinop op a1 a2 ty
  /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
  /\ tr_expr ce le self__SimplExpr.For_val e2 sl2 a2 tmp2
  /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_cast_inv :
  forall ce le dst e1 ty sl a tmp,
  tr_expr ce le dst (S.Ecast e1 ty) sl a tmp ->
  (exists a1, dst = self__SimplExpr.For_effects /\ tr_expr ce le self__SimplExpr.For_effects e1 sl a1 tmp)
  \/ (exists sl1 a1, sl = sl1 ++ final dst (T.Ecast a1 ty) /\ a = T.Ecast a1 ty /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp)
  by plain {intros until tmp; intros H; inv H; [ left; eauto | right; eauto ]}.

Closing Fact tr_seqand_inv :
  forall ce le dst e1 e2 ty sl a tmp,
  tr_expr ce le dst (S.Eseqand e1 e2 ty) sl a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1 (makeseq sl2)
      (T.Sset t (T.Econst_int Int.zero ty)) :: nil
    /\ a = T.Etempvar t ty
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase type_bool ty t)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists sl1 a1 tmp1 sl2 a2 tmp2,
    sl = sl1 ++ makeif a1 (makeseq sl2) T.Sskip :: nil
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le self__SimplExpr.For_effects e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp
  | self__SimplExpr.For_set sd =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1
      (makeseq sl2)
      (makeseq (do_set sd (T.Econst_int Int.zero ty)))
      :: nil
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  end
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

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
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase type_bool ty t)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists sl1 a1 tmp1 sl2 a2 tmp2,
    sl = sl1 ++ makeif a1 T.Sskip (makeseq sl2) :: nil
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le self__SimplExpr.For_effects e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp
  | self__SimplExpr.For_set sd =>
    exists sl1 a1 tmp1 t sl2 a2 tmp2,
    sl = sl1 ++ makeif a1
      (makeseq (do_set sd (T.Econst_int Int.one ty)))
      (makeseq sl2)
      :: nil
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons type_bool ty t sd)) e2 sl2 a2 tmp2
    /\ list_disjoint tmp1 tmp2
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ In t tmp
  end
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_condition_inv :
  forall ce le dst e1 e2 e3 ty sl a tmp,
  tr_expr ce le dst (S.Econdition e1 e2 e3 ty) sl a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists t sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3,
    sl = sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil
    /\ a = T.Etempvar t ty
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e2 sl2 a2 tmp2
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase ty ty t)) e3 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3,
    sl = sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le self__SimplExpr.For_effects e2 sl2 a2 tmp2
    /\ tr_expr ce le self__SimplExpr.For_effects e3 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp
  | self__SimplExpr.For_set sd =>
    exists t sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3,
    sl = sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil
    /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e2 sl2 a2 tmp2
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons ty ty t sd)) e3 sl3 a3 tmp3
    /\ list_disjoint tmp1 tmp2 /\ list_disjoint tmp1 tmp3
    /\ incl tmp1 tmp /\ incl tmp2 tmp /\ incl tmp3 tmp /\ In t tmp
  end
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_comma_inv :
  forall ce le dst e1 e2 ty sl a2 tmp,
  tr_expr ce le dst (S.Ecomma e1 e2 ty) sl a2 tmp ->
  exists sl1 a1 tmp1 sl2 tmp2,
  sl = sl1 ++ sl2
  /\ tr_expr ce le self__SimplExpr.For_effects e1 sl1 a1 tmp1
  /\ tr_expr ce le dst e2 sl2 a2 tmp2
  /\ list_disjoint tmp1 tmp2
  /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_paren_inv :
  forall ce le dst e1 tycast ty sl1 a tmp,
  tr_expr ce le dst (S.Eparen e1 tycast ty) sl1 a tmp ->
  match dst with
  | self__SimplExpr.For_val =>
    exists a1 t,
    a = T.Etempvar t ty
    /\ tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDbase tycast ty t)) e1 sl1 a1 tmp
    /\ In t tmp
  | self__SimplExpr.For_effects =>
    exists a1, tr_expr ce le self__SimplExpr.For_effects e1 sl1 a1 tmp
  | self__SimplExpr.For_set sd =>
    exists t a1,
    tr_expr ce le (self__SimplExpr.For_set (self__SimplExpr.SDcons tycast ty t sd)) e1 sl1 a1 tmp
    /\ In t tmp
  end
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

Closing Fact tr_nil_inv :
  forall ce le sl al tmp,
  tr_exprlist ce le S.Enil sl al tmp ->
  sl = nil /\ al = nil
  by plain {intros until tmp; intros H; inv H; eauto}.

Closing Fact tr_cons_inv :
  forall ce le e1 el2 sl al tmp,
  tr_exprlist ce le (S.Econs e1 el2) sl al tmp ->
  exists sl1 a1 tmp1 sl2 al2 tmp2,
  sl = sl1 ++ sl2 /\ al = a1 :: al2
  /\ tr_expr ce le self__SimplExpr.For_val e1 sl1 a1 tmp1
  /\ tr_exprlist ce le el2 sl2 al2 tmp2
  /\ list_disjoint tmp1 tmp2 /\ incl tmp1 tmp /\ incl tmp2 tmp
  by plain {intros until tmp; intros H; inv H; repeat eexists; eauto}.

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
  self__SimplExpr.T.genv -> self__SimplExpr.T.env ->
  self__SimplExpr.T.temp_env -> mem ->  self__SimplExpr.destination ->
  self__SimplExpr.S.expr -> list self__SimplExpr.T.stmt ->
  self__SimplExpr.T.expr -> list ident -> Prop :=
| tr_top_val_val: forall ge e le m v ty a tmp,
    self__SimplExpr.T.typeof a = ty -> self__SimplExpr.T.eval_expr ge e le m a v ->
    tr_top ce ge e le m self__SimplExpr.For_val (self__SimplExpr.S.Eval v ty) nil a tmp
| tr_top_base: forall ge e le m dst r sl a tmp,
    self__SimplExpr.tr_expr ce le dst r sl a tmp ->
    tr_top ce ge e le m dst r sl a tmp.
FEnd tr_top.

MetaData tr_expression.
Inductive tr_expression (ce : composite_env): self__SimplExpr.S.expr -> self__SimplExpr.T.stmt -> self__SimplExpr.T.expr -> Prop :=
| tr_expression_intro: forall r sl a tmps,
    (forall ge e le m, self__SimplExpr.tr_top ce ge e le m self__SimplExpr.For_val r sl a tmps) ->
    tr_expression ce r (self__SimplExpr.makeseq sl) a.
FEnd tr_expression.

MetaData tr_expr_stmt.
Inductive tr_expr_stmt (ce : composite_env) : self__SimplExpr.S.expr -> self__SimplExpr.T.stmt -> Prop :=
| tr_expr_stmt_intro: forall r sl a tmps,
    (forall ge e le m, self__SimplExpr.tr_top ce ge e le m self__SimplExpr.For_effects r sl a tmps) ->
    tr_expr_stmt ce r (self__SimplExpr.makeseq sl).
FEnd tr_expr_stmt.

MetaData tr_if.
Inductive tr_if (ce : composite_env) : self__SimplExpr.S.expr -> self__SimplExpr.T.stmt -> self__SimplExpr.T.stmt -> self__SimplExpr.T.stmt  -> Prop :=
| tr_if_intro: forall r s1 s2 sl a tmps,
    (forall ge e le m, self__SimplExpr.tr_top ce ge e le m self__SimplExpr.For_val r sl a tmps) ->
    tr_if ce r s1 s2 (self__SimplExpr.makeseq (sl ++ self__SimplExpr.makeif a s1 s2 :: nil)).
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
  by plain {intros until ts; intros H; inv H; eauto}.

Closing Fact tr_do_inv :
  forall ce r s,
  tr_stmt ce (S.Sdo r) s ->
  tr_expr_stmt ce r s
  by plain {intros until s; intros H; inv H; eauto}.

Closing Fact tr_seq_inv :
  forall ce s1 s2 ts,
  tr_stmt ce (S.Sseq s1 s2) ts ->
  exists ts1 ts2, ts = T.Sseq ts1 ts2 /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s2 ts2
  by plain {intros until ts; intros H; inv H; eauto}.

Closing Fact tr_ifthenelse_inv :
  forall ce r s1 s2 ts,
  tr_stmt ce (S.Sifthenelse r s1 s2) ts ->
  (exists s' a, s1 = S.Sskip /\ s2 = S.Sskip /\ ts = T.Sseq s' T.Sskip /\ tr_expression ce r s' a)
  \/ (exists s' a ts1 ts2, ts = T.Sseq s' (T.Sifthenelse a ts1 ts2)
      /\ tr_expression ce r s' a /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s2 ts2)
  by plain {intros until ts; intros H; inv H; [ left; eauto 10 | right; eauto 10 ]}.

Closing Fact tr_return_inv :
  forall ce r s,
  tr_stmt ce (S.Sreturn r) s ->
  match r with
  | None => s = T.Sreturn None
  | Some r => exists s' a, s = T.Sseq s' (T.Sreturn (Some a)) /\ tr_expression ce r s' a
  end
  by plain {intros until s; intros H; inv H; eauto}.

Closing Fact tr_label_inv :
  forall ce lbl s ts,
  tr_stmt ce (S.Slabel lbl s) ts ->
  exists ts', ts = T.Slabel lbl ts' /\ tr_stmt ce s ts'
  by plain {intros until ts; intros H; inv H; eauto}.

Closing Fact tr_goto_inv :
  forall ce lbl ts,
  tr_stmt ce (S.Sgoto lbl) ts ->
  ts = T.Sgoto lbl
  by plain {intros until ts; intros H; inv H; eauto}.

Closing Fact tr_ls_nil_inv :
  forall ce ts,
  tr_lblstmts ce S.LSnil ts ->
  ts = T.LSnil
  by plain {intros until ts; intros H; inv H; eauto}.

Closing Fact tr_ls_cons_inv :
  forall ce c s ls ts,
  tr_lblstmts ce (S.LScons c s ls) ts ->
  exists ts' tls, ts = T.LScons c ts' tls /\ tr_stmt ce s ts' /\ tr_lblstmts ce ls tls
  by plain {intros until ts; intros H; inv H; eauto}.

MetaData tr_function.
Inductive tr_function (ce : composite_env) :  self__SimplExpr.S.function -> self__SimplExpr.T.function -> Prop :=
| tr_function_intro: forall f tf,
    self__SimplExpr.tr_stmt ce f.(self__SimplExpr.S.fn_body) tf.(self__SimplExpr.T.fn_body) ->
    self__SimplExpr.T.fn_return tf = self__SimplExpr.S.fn_return f ->
    self__SimplExpr.T.fn_callconv tf = self__SimplExpr.S.fn_callconv f ->
    self__SimplExpr.T.fn_params tf = self__SimplExpr.S.fn_params f ->
    self__SimplExpr.T.fn_vars tf = self__SimplExpr.S.fn_vars f ->
    tr_function ce f tf.
FEnd tr_function.

MetaData tr_fundef.
Inductive tr_fundef (p: self__SimplExpr.S.program): self__SimplExpr.S.fundef -> self__SimplExpr.T.fundef -> Prop :=
    | tr_internal: forall f tf,
        self__SimplExpr.tr_function p.(prog_comp_env) f tf ->
        tr_fundef p (Internal f) (Internal tf).
FEnd tr_fundef.

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
    dst = self__SimplExpr.For_val \/ dst = self__SimplExpr.For_effects -> S.simple r = true -> sl = nil)
with tr_simple_exprlist_nil
  about tr_exprlist
  motive (fun ce le rl sl al tmps (_ : tr_exprlist ce le rl sl al tmps) =>
    S.simplelist rl = true -> sl = nil).
FProof.
all:
  assert (A: forall dst a, dst = self__SimplExpr.For_val \/ dst = self__SimplExpr.For_effects -> self__SimplExpr.final dst a = nil)
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
  apply self__SimplExpr.tr_val_inv in H2.
  destruct dst; destruct H2; intuition eauto.
(* unop *)
- intros. fsimpl.
  apply self__SimplExpr.tr_unop_inv in H3; unpack H3.
  exploit (H prog tprog tge); eauto. intros [A [B C]].
  subst sl sl1 a. simpl.
  assert (self__SimplExpr.T.eval_expr tge e le m (self__SimplExpr.T.Eunop op a1 ty) v).
  { fconstructor. congruence. }
  destruct dst.
  + fsimpl. auto.
  + auto.
  + simpl. eexists; repeat split; fsimpl; auto.
(* binop *)
- intros. fsimpl.
  apply self__SimplExpr.tr_binop_inv in H4; unpack H4.
  exploit (H prog tprog tge); eauto. intros [A [B C]].
  exploit (H0 prog tprog tge); eauto. intros [D [E F]].
  subst sl sl1 sl2 a. simpl.
  assert (self__SimplExpr.T.eval_expr tge e le m (self__SimplExpr.T.Ebinop op a1 a2 ty) v).
  { fconstructor. rewrite (self__SimplExpr.comp_env_preserved prog tprog ge tge); congruence. }
  destruct dst.
  + fsimpl. auto.
  + auto.
  + simpl. eexists; repeat split; fsimpl; auto.
(* cast *)
- intros. fsimpl.
  apply self__SimplExpr.tr_cast_inv in H3 as [[a1 []] | [sl1 [a1 [? []]]]].
  (* effects *)
  + destruct dst; try discriminate.
    exploit (H prog tprog tge); eauto.
  (* val *)
  + exploit (H prog tprog tge); eauto.
    intros [A [B C]]. subst sl sl1 a. simpl.
    assert (self__SimplExpr.T.eval_expr tge e le m (self__SimplExpr.T.Ecast a1 ty) v).
    { fconstructor. congruence. }
    destruct dst.
    * fsimpl. auto.
    * auto.
    * simpl. eexists; repeat split; fsimpl; auto.
(* sizeof *)
- intros. rewrite <- (self__SimplExpr.comp_env_preserved prog tprog ge tge); try assumption.
  fsimpl. apply self__SimplExpr.tr_sizeof_inv in H2 as []; subst sl a; simpl.
  destruct dst.
  + repeat split; fsimpl; auto. fconstructor.
  + auto.
  + exists (self__SimplExpr.T.Esizeof ty1 ty).
    repeat split; fsimpl; auto. fconstructor.
(* sizeof *)
- intros. rewrite <- (self__SimplExpr.comp_env_preserved prog tprog ge tge); try assumption.
  fsimpl. apply self__SimplExpr.tr_alignof_inv in H2 as []; subst sl a; simpl.
  destruct dst.
  + repeat split; fsimpl; auto. fconstructor.
  + auto.
  + exists (self__SimplExpr.T.Ealignof ty1 ty).
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
- intros. apply self__SimplExpr.tr_unop_inv in H0; unpack H0; subst.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * subst sl1. rewrite app_assoc. eauto.
  * auto.
  * intros. rewrite app_assoc. fconstructor.
(* binop left *)
- intros. apply self__SimplExpr.tr_binop_inv in H0; unpack H0; subst.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * subst sl1. rewrite <- app_assoc. eauto.
  * red. auto.
  * intros. rewrite app_assoc. fconstructor.
    eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
(* binop right *)
- intros. apply self__SimplExpr.tr_binop_inv in H0; unpack H0; subst.
  assert (sl1 = nil) by (eapply self__SimplExpr.tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl2. rewrite app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2'). rewrite <- app_assoc.
    fconstructor. eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
(* cast *)
- intros. apply self__SimplExpr.tr_cast_inv in H0 as [[a1 []] | [sl1 [a1 [? []]]]].
  (* for effects *)
  + exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * eauto.
    * auto.
    * intros. subst dst. eauto using self__SimplExpr.tr_cast_effects.
  (* generic *)
  + exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * subst sl sl1. rewrite app_assoc. eauto.
    * auto.
    * intros. rewrite app_assoc. subst a. eauto using self__SimplExpr.tr_cast_val.
(* seqand *)
- intros. apply self__SimplExpr.tr_seqand_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_seqand_val.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_seqand_effects.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_seqand_set.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
(* seqor *)
- intros. apply self__SimplExpr.tr_seqor_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_seqor_val.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_seqor_effects.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_seqor_set.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto.
(* condition *)
- intros. apply self__SimplExpr.tr_condition_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_condition_val.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto. -- auto. -- auto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_condition_effects.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto. -- auto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
    intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
    * rewrite Q. rewrite app_assoc. eauto.
    * red. auto.
    * intros. rewrite app_assoc. eapply self__SimplExpr.tr_condition_set.
      -- apply S; auto.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
      -- auto. -- auto. -- auto. -- auto. -- auto. -- auto.
(* comma *)
- intros. apply self__SimplExpr.tr_comma_inv in H0. unpack H0.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl sl1. rewrite app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. eapply self__SimplExpr.tr_comma with (tmp2 := tmp2).
    * apply S; auto.
    * eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
    * auto. * auto. * auto.
(* paren *)
- intros. apply self__SimplExpr.tr_paren_inv in H0. destruct dst.
  (* for val *)
  + unpack H0. subst. exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * rewrite Q. eauto.
  * red. auto.
  * intros. eapply self__SimplExpr.tr_paren_val; eauto.
  (* for effects *)
  + unpack H0. subst. exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * rewrite Q. eauto.
  * red. auto.
  * intros. eapply self__SimplExpr.tr_paren_effects; eauto.
  (* for set *)
  + unpack H0. subst. exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  * rewrite Q. eauto.
  * red. auto.
  * intros. eapply self__SimplExpr.tr_paren_set; eauto.
(* cons left *)
- intros. apply self__SimplExpr.tr_cons_inv in H0; unpack H0; subst.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl1. rewrite app_assoc. eauto.
  + red. auto.
  + intros. rewrite app_assoc. fconstructor.
    eapply self__SimplExpr.tr_exprlist_invariant; eauto. UNCHANGED.
(* cons right *)
- intros. apply self__SimplExpr.tr_cons_inv in H0; unpack H0; subst.
  assert (sl1 = nil) by (eapply self__SimplExpr.tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H; eauto.
  intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]]. TR.
  + subst sl2. eauto.
  + red. auto.
  + intros. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2').
    fconstructor. eapply self__SimplExpr.tr_expr_invariant; eauto. UNCHANGED.
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
- apply (self__SimplExpr.S.leftcontext_val_top r v ty) in H2; auto. subst c r.
  exists self__SimplExpr.For_val. repeat eexists.
  + apply self__SimplExpr.tr_top_val_val; eauto.
  + instantiate (1 := nil); auto.
  + apply incl_refl.
  + intros. rewrite app_nil_r. constructor. auto.
(* base *)
- subst r. exploit self__SimplExpr.tr_expr_leftcontext; eauto.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  exists dst' sl1 sl2 a' tmp'. repeat split.
  + apply self__SimplExpr.tr_top_base; auto.
  + auto.
  + auto.
  + intros. apply self__SimplExpr.tr_top_base. apply S; auto.
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
- destruct (self__SimplExpr.eval_simpl_expr a); auto. subst.
  destruct (sem_cast v1 (self__SimplExpr.T.typeof a) ty Mem.empty) as [v'|] eqn:C; auto.
  eapply self__SimplExpr.sem_cast_deterministic; eauto.
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
  intros. functional induction (self__SimplExpr.makeif a s1 s2).
- specialize (self__SimplExpr.eval_simpl_expr_sound tge _ _ _ _ _ H). cbv. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (self__SimplExpr.T.typeof a) m = Some true) by (apply self__SimplExpr.static_bool_val_sound; auto).
  replace b with true by congruence. constructor.
- specialize (self__SimplExpr.eval_simpl_expr_sound tge _ _ _ _ _ H). cbv. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (self__SimplExpr.T.typeof a) m = Some false) by (apply self__SimplExpr.static_bool_val_sound; auto).
  replace b with false by congruence. constructor.
- apply star_one. eapply self__SimplExpr.T.step_ifthenelse; eauto.
- apply star_one. eapply self__SimplExpr.T.step_ifthenelse; eauto.
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
    match_cont_exp ce self__SimplExpr.For_effects a (S.Kdo k) tk
| match_Kifthenelse_empty: forall ce a k tk,
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_val a (S.Kifthenelse S.Sskip S.Sskip k) (T.Kseq T.Sskip tk)
| match_Kifthenelse_1: forall ce a s1 s2 k ts1 ts2 tk,
    tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_val a (S.Kifthenelse s1 s2 k) (T.Kseq (T.Sifthenelse a ts1 ts2) tk)
| match_Kreturn: forall ce k a tk,
    match_cont ce k tk ->
    match_cont_exp ce self__SimplExpr.For_val a (S.Kreturn k) (T.Kseq (T.Sreturn (Some a)) tk).

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
  by plain {intros until tk; intros MK; inv MK; auto}.

Closing Fact match_cont_seq_inv :
  forall ce s k tk,
  match_cont ce (S.Kseq s k) tk ->
  exists ts tk', tk = T.Kseq ts tk' /\ tr_stmt ce s ts /\ match_cont ce k tk'
  by plain {intros until tk; intros H; inv H; eauto}.

Closing Fact match_cont_exp_no_set :
  forall ce sd a k tk,
  ~ match_cont_exp ce (self__SimplExpr.For_set sd) a k tk
  by {intros; intro Hc; inversion Hc}.

Closing Fact match_cont_exp_do_inv :
  forall ce dst a k tk,
  match_cont_exp ce dst a (S.Kdo k) tk ->
  dst = self__SimplExpr.For_effects /\ match_cont ce k tk
  by plain {intros until tk; intros H; inv H; eauto}.

Closing Fact match_cont_exp_ifthenelse_inv :
  forall ce dst a s1 s2 k tk,
  match_cont_exp ce dst a (S.Kifthenelse s1 s2 k) tk ->
  (exists tk', dst = self__SimplExpr.For_val /\ s1 = S.Sskip /\ s2 = S.Sskip /\ tk = T.Kseq T.Sskip tk' /\ match_cont ce k tk')
  \/ (exists ts1 ts2 tk', dst = self__SimplExpr.For_val /\ tk = T.Kseq (T.Sifthenelse a ts1 ts2) tk'
      /\ tr_stmt ce s1 ts1 /\ tr_stmt ce s2 ts2 /\ match_cont ce k tk')
  by plain {intros until tk; intros H; inv H; [ left; eauto 10 | right; eauto 10]}.

Closing Fact match_cont_exp_return_inv :
  forall ce dst a k tk,
  match_cont_exp ce dst a (S.Kreturn k) tk ->
  exists tk', dst = self__SimplExpr.For_val /\ tk = T.Kseq (T.Sreturn (Some a)) tk'
    /\ match_cont ce k tk'
  by plain {intros until tk; intros H; inv H; eauto}.

MetaData Kseqlist.
Fixpoint Kseqlist (sl: list self__SimplExpr.T.stmt) (k: self__SimplExpr.T.cont) :=
match sl with
| nil => k
| s :: l => self__SimplExpr.T.Kseq s (Kseqlist l k)
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
intros. unfold self__SimplExpr.makeseq. generalize self__SimplExpr.T.Sskip. revert sl k.
induction sl; simpl; intros.
apply star_refl.
eapply star_right. apply IHsl. fconstructor. traceEq.
Qed. CloseFLemma.

MetaData match_states.
Inductive match_states (tge : self__SimplExpr.T.genv) : self__SimplExpr.S.state -> self__SimplExpr.T.state -> Prop :=
    | match_exprstates: forall f r k e m tf sl tk le dest a tmps (cu: self__SimplExpr.S.program)
        (* (LINK: linkorder cu prog)*)
        (TRF: self__SimplExpr.tr_function cu.(prog_comp_env) f tf)
        (TR: self__SimplExpr.tr_top cu.(prog_comp_env) tge e le m dest r sl a tmps)
        (MK: self__SimplExpr.match_cont_exp cu.(prog_comp_env) dest a k tk),
        match_states tge (self__SimplExpr.S.ExprState f r k e m)
                      (self__SimplExpr.T.State tf self__SimplExpr.T.Sskip (self__SimplExpr.Kseqlist sl tk) e le m)
    | match_regularstates: forall f s k e m tf ts tk le (cu: self__SimplExpr.S.program)
        (* (LINK: linkorder cu prog) *)
        (TRF: self__SimplExpr.tr_function cu.(prog_comp_env) f tf)
        (TR: self__SimplExpr.tr_stmt cu.(prog_comp_env) s ts)
        (MK: self__SimplExpr.match_cont cu.(prog_comp_env) k tk),
        match_states tge (self__SimplExpr.S.State f s k e m)
                      (self__SimplExpr.T.State tf ts tk e le m)
    | match_callstates: forall fd args k m tfd tk cu
        (* (LINK: linkorder cu prog)*)
        (TR: self__SimplExpr.tr_fundef cu fd tfd)
        (MK: forall ce, self__SimplExpr.match_cont ce k tk),
        match_states tge (self__SimplExpr.S.Callstate fd args k m)
                      (self__SimplExpr.T.Callstate tfd args tk m)
    | match_returnstates: forall res k m tk
        (MK: forall ce, self__SimplExpr.match_cont ce k tk),
        match_states tge (self__SimplExpr.S.Returnstate res k m)
                      (self__SimplExpr.T.Returnstate res tk m)
    | match_stuckstate: forall S,
        match_states tge self__SimplExpr.S.Stuckstate S.
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
  assert (forall sl s, self__SimplExpr.nolabel lbl s -> self__SimplExpr.nolabel_list lbl sl -> self__SimplExpr.nolabel lbl (self__SimplExpr.makeseq_rec s sl)).
  { induction sl; intros. auto. destruct H0. apply IHsl; fsimpl; auto.
    red. intros; fsimpl. rewrite H. apply H0. }
  intros. unfold self__SimplExpr.makeseq. apply H; auto. red. fsimpl. auto.
Qed. CloseFLemma.

FLemma makeif_nolabel:
  forall lbl a s1 s2, nolabel lbl s1 -> nolabel lbl s2 -> nolabel lbl (makeif a s1 s2).
FProofLemma.
  intros. functional induction (self__SimplExpr.makeif a s1 s2); auto.
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
  destruct dst; simpl; intros. auto. auto. apply self__SimplExpr.nolabel_do_set.
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
  | [ |- self__SimplExpr.nolabel_list ?lbl nil ] => exact I
  | [ |- self__SimplExpr.nolabel_list ?lbl (self__SimplExpr.do_set _ _) ] => apply (self__SimplExpr.nolabel_do_set lbl) (*; NoLabelTac*)
  | [ |- self__SimplExpr.nolabel_list ?lbl (self__SimplExpr.final _ _) ] => apply (self__SimplExpr.nolabel_final lbl) (*; NoLabelTac*)
  | [ |- self__SimplExpr.nolabel_list ?lbl (_ :: _) ] => simpl; split; NoLabelTac
  | [ |- self__SimplExpr.nolabel_list ?lbl (_ ++ _) ] => apply (self__SimplExpr.nolabel_list_app lbl); NoLabelTac
  | [ H: _ -> self__SimplExpr.nolabel_list ?lbl ?x |- self__SimplExpr.nolabel_list ?lbl ?x ] => apply H; NoLabelTac
  | [ |- self__SimplExpr.nolabel ?lbl (self__SimplExpr.makeseq _) ] => apply (self__SimplExpr.makeseq_nolabel lbl); NoLabelTac
  | [ |- self__SimplExpr.nolabel ?lbl (self__SimplExpr.makeif _ _ _) ] => apply (self__SimplExpr.makeif_nolabel lbl); NoLabelTac
  | [ |- self__SimplExpr.nolabel _ _ ] => red; intros; fsimpl; auto
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
  - eapply self__SimplExpr.tr_find_label_expr. eassumption.
Qed. CloseFLemma.

FLemma tr_find_label_expression:
  forall ce (tge: self__SimplExpr.T.genv) lbl r s a,
  tr_expression ce r s a -> forall k, T.find_label s lbl k = None.
FProofLemma.
  intros. inv H.
  assert (self__SimplExpr.nolabel lbl (self__SimplExpr.makeseq sl)). apply self__SimplExpr.makeseq_nolabel.
  eapply self__SimplExpr.tr_find_label_top with
    (e := self__SimplExpr.T.empty_env) (le := PTree.empty val) (m := Mem.empty) (tge := tge).
  eauto. apply H.
Qed. CloseFLemma.

FLemma tr_find_label_expr_stmt:
  forall ce (tge: self__SimplExpr.T.genv) lbl r s,
  tr_expr_stmt ce r s -> forall k, T.find_label s lbl k = None.
FProofLemma.
  intros. inv H.
  assert (self__SimplExpr.nolabel lbl (self__SimplExpr.makeseq sl)). apply self__SimplExpr.makeseq_nolabel.
  eapply self__SimplExpr.tr_find_label_top with
    (e := self__SimplExpr.T.empty_env) (le := PTree.empty val) (m := Mem.empty) (tge := tge).
  eauto. apply H.
Qed. CloseFLemma.

(* FLemma tr_find_label_if:
  forall ce (tge: self__SimplExpr.T.genv) lbl r s,
  tr_if ce r S.Sskip S.Sbreak s ->
  forall k, T.find_label s lbl k = None.
FProofLemma.
  intros. inv H.
  assert (self__SimplExpr.nolabel lbl (self__SimplExpr.makeseq (sl ++ self__SimplExpr.makeif a Sskip Sbreak :: nil))).
  apply self__SimplExpr.makeseq_nolabel.
  apply self__SimplExpr.nolabel_list_app.
  eapply self__SimplExpr.tr_find_label_top with
    (e := self__SimplExpr.T.empty_env) (le := PTree.empty val) (m := Mem.empty) (tge := tge).
  eauto.
  simpl; split; auto. apply self__SimplExpr.makeif_nolabel. red; simpl; auto. red; simpl; auto.
  apply H.
Qed. CloseFLemma. *)

FInduction tr_find_label
  about S.stmt
  motive (fun (s : S.stmt) =>
    forall ce (tge: self__SimplExpr.T.genv) lbl k ts tk
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
    forall ce (tge: self__SimplExpr.T.genv) lbl k ts tk
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
- intros. apply self__SimplExpr.tr_seq_inv in TR; unpack TR; subst. fsimpl.
  exploit (H ce tge lbl (self__SimplExpr.S.Kseq __i0 k)); eauto. fconstructor.
  destruct (self__SimplExpr.S.find_label __i lbl (self__SimplExpr.S.Kseq __i0 k)) as [[s' k'] | ].
  + intros [ts1' [tk' [A [B C]]]]. fsimpl. rewrite A. eauto.
  + intro EQ. fsimpl. rewrite EQ. eapply H0; eauto.
(* skip *)
- intros. apply self__SimplExpr.tr_skip_inv in TR; subst. fsimpl. fsimpl. auto.
(* do *)
- intros. apply self__SimplExpr.tr_do_inv in TR. fsimpl.
  eapply self__SimplExpr.tr_find_label_expr_stmt; eauto.
(* ifthenelse *)
- intros. apply self__SimplExpr.tr_ifthenelse_inv in TR as [He|Hn].
  (* ifthenelse empty *)
  + unpack He; subst.
    assert (Hf: self__SimplExpr.S.find_label (self__SimplExpr.S.Sifthenelse e self__SimplExpr.S.Sskip self__SimplExpr.S.Sskip) lbl k = None)
      by (do 3 fsimpl; auto); rewrite Hf; clear Hf.
    fsimpl. rewrite (self__SimplExpr.tr_find_label_expression ce tge lbl _ _ _ TEMP3).
    fsimpl. auto.
  (* ifthenelse non empty *)
  + unpack Hn; subst. rename s' into sr.
    fsimpl. fsimpl. rewrite (self__SimplExpr.tr_find_label_expression ce tge lbl _ _ _ TEMP0).
    exploit (H ce tge lbl k); eauto.
    destruct (self__SimplExpr.S.find_label __i lbl k) as [[s' k'] | ].
    * intros [ts' [tk' [A [B C]]]]. fsimpl. rewrite A. eauto.
    * intro EQ. fsimpl. rewrite EQ. eapply H0; eauto.
(* return *)
- intros. apply self__SimplExpr.tr_return_inv in TR. destruct o; unpack TR; subst.
  (* return some *)
  + fsimpl. fsimpl. rewrite (self__SimplExpr.tr_find_label_expression ce tge lbl _ _ _ TEMP1).
    fsimpl. auto.
  (* return none *)
  + fsimpl. fsimpl. auto.
(* label *)
- intros. apply self__SimplExpr.tr_label_inv in TR; unpack TR; subst.
  fsimpl. fsimpl. destruct (ident_eq lbl l).
  + eauto.
  + apply H; eauto.
(* goto *)
- intros. apply self__SimplExpr.tr_goto_inv in TR; subst.
  fsimpl. fsimpl. auto.

(* nil *)
- intros. apply self__SimplExpr.tr_ls_nil_inv in TR; subst.
  fsimpl. fsimpl. auto.
(* cons *)
- intros. apply self__SimplExpr.tr_ls_cons_inv in TR; unpack TR; subst. rename ts' into tsr.
  fsimpl. fsimpl. exploit (H ce tge lbl (self__SimplExpr.S.Kseq (self__SimplExpr.S.seq_of_labeled_statement __i0) k)); eauto.
  + fconstructor. apply self__SimplExpr.tr_seq_of_labeled_statement; eauto.
  + destruct (self__SimplExpr.S.find_label __i lbl (self__SimplExpr.S.Kseq (self__SimplExpr.S.seq_of_labeled_statement __i0) k)) as [[s' k'] | ].
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
Case Slabel lbl s := 0%nat.
Case Sgoto lbl := 0%nat.
Case Sseq s1 s2 := 0%nat.
Case Sreturn e := 0%nat.
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

FInduction estep_simulation about S.estep 
  motive (fun ge S1 t S2 (_ : S.estep ge S1 t S2) => 
    forall prog tprog tge, match_prog prog tprog -> 
    S.globalenv prog = ge -> T.globalenv tprog = tge ->
    forall T1 (MS : match_states tge S1 T1),
    exists T2,
    (plus T.step tge T1 t T2 \/ (star T.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
    /\ match_states tge S2 T2).
FProof.
all: intros; inv MS.
(* expr *)
- assert (self__SimplExpr.tr_expr (prog_comp_env cu) le dest r sl a tmps).
    { inv TR. exfalso; unfold self__SimplExpr.S.is_val in n; eauto. auto. }
  exploit self__SimplExpr.tr_simple_rvalue; eauto. destruct dest.
  (* for value *)
  + intros [SL1 [TY1 EV1]]. subst sl.
    econstructor. split.
    * right; split. apply star_refl. unfold self__SimplExpr.measure. fsimpl.
      destruct (self__SimplExpr.esize r) eqn:Hs.
      -- apply self__SimplExpr.esize_zero_val in Hs. contradiction.
      -- lia. 
    * eapply self__SimplExpr.match_exprstates with (tmps := tmps); eauto.
      apply self__SimplExpr.tr_top_val_val; auto using EV1.
  (* for effects *)
  + intros SL1. subst sl.
    econstructor. split.
    * right; split. apply star_refl. unfold self__SimplExpr.measure. fsimpl.
      destruct (self__SimplExpr.esize r) eqn:Hs.
      -- apply self__SimplExpr.esize_zero_val in Hs. contradiction.
      -- lia.
    * eapply self__SimplExpr.match_exprstates with (tmps := tmps); eauto.
      apply self__SimplExpr.tr_top_base. fconstructor.
  (* for set *)
  + apply self__SimplExpr.match_cont_exp_no_set in MK as [].
(* seqand true *)
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_seqand_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + apply self__SimplExpr.tr_paren_val with (a1 := a2); auto.
          apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + apply self__SimplExpr.tr_paren_effects with (a1 := a2); auto.
          apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + apply self__SimplExpr.tr_paren_set with (a1 := a2) (t := t); auto.
          apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
(* seqand false *)       
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_seqand_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply star_one. fconstructor. fconstructor.
          * reflexivity.
        + reflexivity.
      - eapply self__SimplExpr.match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor. rewrite H0; auto using PTree.gss.
        + intros. apply PTree.gso. congruence.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
        + reflexivity.
      - eapply self__SimplExpr.match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
(* seqor true *)
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_seqor_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply star_one. fconstructor. fconstructor.
          * reflexivity.
        + reflexivity.
      - eapply self__SimplExpr.match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor. rewrite H0; auto using PTree.gss.
        + intros. apply PTree.gso. congruence.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
        + reflexivity.
      - eapply self__SimplExpr.match_exprstates; eauto.
        change sl2 with (nil ++ sl2). apply S.
        + fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + fconstructor.
          * fsimpl. auto.
          * intros. fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
(* seqor false *)
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_seqor_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + apply self__SimplExpr.tr_paren_val with (a1 := a2); auto.
          apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + apply self__SimplExpr.tr_paren_effects with (a1 := a2); auto.
          apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist.
      eexists. { split.
      - left. eapply plus_left.
        + fconstructor.
        + eapply star_trans.
          * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
          * apply self__SimplExpr.push_seq.
          * reflexivity.
        + reflexivity.
      - rewrite <- self__SimplExpr.Kseqlist_app.
        eapply self__SimplExpr.match_exprstates; eauto.
        apply S.
        + apply self__SimplExpr.tr_paren_set with (a1 := a2) (t := t); auto.
          apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
        + auto.
        + do 2 fsimpl. auto. }
(* condition *)
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_condition_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1 a'. simpl self__SimplExpr.Kseqlist. destruct b.
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
            * apply self__SimplExpr.push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- self__SimplExpr.Kseqlist_app.
          eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + apply self__SimplExpr.tr_paren_val with (a1 := a2); auto.
            apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
          + auto.
          + do 2 fsimpl. auto. }
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
            * apply self__SimplExpr.push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- self__SimplExpr.Kseqlist_app.
          eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + apply self__SimplExpr.tr_paren_val with (a1 := a3); auto.
            apply self__SimplExpr.tr_expr_monotone with tmp3; eauto.
          + auto.
          + do 2 fsimpl. auto. }
    (* for effects *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist. destruct b.
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
            * apply self__SimplExpr.push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- self__SimplExpr.Kseqlist_app.
          eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + apply self__SimplExpr.tr_paren_effects with (a1 := a2); auto.
            apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
          + auto.
          + do 2 fsimpl. auto. }
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
            * apply self__SimplExpr.push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- self__SimplExpr.Kseqlist_app.
          eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + apply self__SimplExpr.tr_paren_effects with (a1 := a3); auto.
            apply self__SimplExpr.tr_expr_monotone with tmp3; eauto.
          + auto.
          + do 2 fsimpl. auto. }
    (* for set *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [SL [TY EV]].
      subst sl0 sl1. simpl self__SimplExpr.Kseqlist. destruct b.
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply self__SimplExpr.step_makeif with (b := true) (v1 := v); auto. congruence.
            * apply self__SimplExpr.push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- self__SimplExpr.Kseqlist_app.
          eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + apply self__SimplExpr.tr_paren_set with (a1 := a2) (t := t); auto.
            apply self__SimplExpr.tr_expr_monotone with tmp2; eauto.
          + auto.
          + do 2 fsimpl. auto. }
      -- eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + eapply star_trans.
            * apply self__SimplExpr.step_makeif with (b := false) (v1 := v); auto. congruence.
            * apply self__SimplExpr.push_seq.
            * reflexivity.
          + reflexivity.
        - rewrite <- self__SimplExpr.Kseqlist_app.
          eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + apply self__SimplExpr.tr_paren_set with (a1 := a3) (t := t); auto.
            apply self__SimplExpr.tr_expr_monotone with tmp3; eauto.
          + auto.
          + do 2 fsimpl. auto. }
(* comma *)
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_comma_inv in H0. unpack H0.
    exploit self__SimplExpr.tr_simple_rvalue; eauto. simpl; intro SL1.
    subst sl0 sl1; simpl self__SimplExpr.Kseqlist.
    eexists. { split.
    - right. split.
      + apply star_refl.
      + rewrite <- Nat.succ_lt_mono.
        apply (self__SimplExpr.leftcontext_size _ _ _ l). fsimpl. lia.
    - eapply self__SimplExpr.match_exprstates; eauto.
      apply S.
      + eapply self__SimplExpr.tr_expr_monotone; eauto.
      + auto.
      + fsimpl. auto. }
(* paren *)
- exploit self__SimplExpr.tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P.
  + (* fdiscriminate. *) apply cheat.
  + apply self__SimplExpr.tr_paren_inv in H0. destruct dst'; unpack H0.
    (* for value *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [b [SL1 [TY1 EV1]]].
      subst sl1 a'; simpl self__SimplExpr.Kseqlist.
      eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + apply star_one. fconstructor. fconstructor.
            rewrite <- TY1; eauto.
          + reflexivity.
        - eapply self__SimplExpr.match_exprstates; eauto.
          change sl2 with (self__SimplExpr.final self__SimplExpr.For_val (self__SimplExpr.T.Etempvar t (self__SimplExpr.S.typeof r)) ++ sl2).
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
          apply (self__SimplExpr.leftcontext_size _ _ _ l). do 2 fsimpl. lia.
      - eapply self__SimplExpr.match_exprstates; eauto.
        exploit self__SimplExpr.tr_simple_rvalue; eauto.
        simpl. intros A. subst sl1.
        apply S.
        + fconstructor.
        + auto.
        + do 2 fsimpl. auto. }
    (* for set *)
    * exploit self__SimplExpr.tr_simple_rvalue; eauto. intros [b [SL1 [TY1 EV1]]].
      subst sl1; simpl self__SimplExpr.Kseqlist.
      eexists. { split.
        - left. eapply plus_left.
          + fconstructor.
          + apply star_one. fconstructor. fconstructor.
            rewrite <- TY1; eauto.
          + reflexivity.
        - eapply self__SimplExpr.match_exprstates; eauto.
          apply S.
          + fconstructor.
            * fsimpl. auto.
            * intros. fconstructor. rewrite H0; auto using PTree.gss.
          + intros. apply PTree.gso. congruence.
          + do 2 fsimpl. auto. }
Qed. FEnd estep_simulation.

FLemma tr_top_val_for_val_inv:
  forall tge ce e le m v ty sl a tmps,
  tr_top ce tge e le m self__SimplExpr.For_val (S.Eval v ty) sl a tmps ->
  sl = nil /\ T.typeof a = ty /\ T.eval_expr tge e le m a v.
FProofLemma.
  intros. inv H.
  - (* finjection H0. *) apply cheat.
  - apply self__SimplExpr.tr_val_inv in H0. intuition.
Qed. CloseFLemma.

(* FLemma alloc_variables_preserved:
  forall prog tprog ge tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall e m params e' m',
  S.alloc_variables ge e m params e' m' ->
  T.alloc_variables tge e m params e' m'.
FProofLemma.
  
Qed. CloseFLemma.

FLemma bind_parameters_preserved:
  forall prog tprog ge tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall e m params args m',
  S.bind_parameters ge e m params args m' ->
  T.bind_parameters tge e m params args m'.
FProofLemma.
  
Qed. CloseFLemma. *)

FLemma blocks_of_env_preserved:
  forall prog tprog ge tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
  forall e, T.blocks_of_env tge e = S.blocks_of_env ge e.
FProofLemma.
  intros; unfold self__SimplExpr.T.blocks_of_env, self__SimplExpr.S.blocks_of_env.
  unfold self__SimplExpr.T.block_of_binding, self__SimplExpr.S.block_of_binding.
  rewrite (self__SimplExpr.comp_env_preserved prog tprog ge tge); auto.
Qed. CloseFLemma.

FInduction sstep_simulation about S.sstep 
   motive (fun ge S1 t S2 (_ : S.sstep ge S1 t S2) => 
           forall prog tprog tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
           forall T1 (MS : match_states tge S1 T1),
           exists T2,
           (plus T.step tge T1 t T2 \/
              (star T.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
                    /\ match_states tge S2 T2).
FProof.
all: intros; inv MS.
(* do 1 *)
- apply self__SimplExpr.tr_do_inv in TR. inv TR.
  eexists. split.
  + right. split. apply self__SimplExpr.push_seq. simpl. fsimpl. lia.
  + econstructor; eauto. fconstructor.
(* do 2 *)
- apply self__SimplExpr.match_cont_exp_do_inv in MK as []; subst. inv TR.
  apply self__SimplExpr.tr_val_inv in H0; subst.
  eexists. split.
  + right. split. apply star_refl. simpl. fsimpl. lia.
  + econstructor; eauto. fconstructor.
(* seq *)
- apply self__SimplExpr.tr_seq_inv in TR; unpack TR; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto. fconstructor.
(* skip seq *)
- apply self__SimplExpr.tr_skip_inv in TR; subst.
  apply self__SimplExpr.match_cont_seq_inv in MK; unpack MK; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto.
(* ifthenelse *)
- apply self__SimplExpr.tr_ifthenelse_inv in TR as [He|Hn].
  (* ifthenelse empty *)
  + unpack He. inv TEMP3. eexists. split.
    * left. eapply plus_left. fconstructor. apply self__SimplExpr.push_seq. auto.
    * econstructor; eauto. fconstructor.
  (* ifthenelse non empty *)
  + unpack Hn. inv TEMP0. eexists. split.
    * left. eapply plus_left. fconstructor. apply self__SimplExpr.push_seq. auto.
    * econstructor; eauto. fconstructor. 
(* ifthenelse *)
- apply self__SimplExpr.match_cont_exp_ifthenelse_inv in MK as [He|Hn].
  (* ifthenelse empty *)
  + unpack He; subst.
    exploit self__SimplExpr.tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
    eexists. split.
    * right. destruct b; split; do 2 (simpl; fsimpl); auto.
      -- eapply star_left. fconstructor. constructor. auto.
      -- eapply star_left. fconstructor. constructor. auto.
    * destruct b; econstructor; eauto; fconstructor.
  (* ifthenelse non empty *)
  + unpack Hn; subst.
    exploit self__SimplExpr.tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
    eexists. split.
    * left. eapply plus_two. fconstructor. fconstructor. auto.
    * destruct b; econstructor; eauto.
(* return none *)
- apply self__SimplExpr.tr_return_inv in TR; subst.
  eexists. split.
  + left. apply plus_one. fconstructor. erewrite self__SimplExpr.blocks_of_env_preserved; eauto.
  + econstructor. intros. eapply self__SimplExpr.match_cont_call_cont; eauto.
(* return some 1 *)
- apply self__SimplExpr.tr_return_inv in TR; unpack TR; subst. inv TEMP1.
  eexists. split.
  + left. eapply plus_left. fconstructor. apply self__SimplExpr.push_seq. auto.
  + econstructor; eauto. fconstructor.
(* return some 2 *)
- apply self__SimplExpr.match_cont_exp_return_inv in MK; unpack MK; subst.
  exploit self__SimplExpr.tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  eexists. split.
  + left. eapply plus_two.
    -- fconstructor.
    -- fconstructor. erewrite self__SimplExpr.function_return_preserved; eauto.
      erewrite self__SimplExpr.blocks_of_env_preserved; eauto.
    -- auto.
  + econstructor. intros. eapply self__SimplExpr.match_cont_call_cont; eauto.
(* skip return *)
- apply self__SimplExpr.tr_skip_inv in TR; subst.
  assert (self__SimplExpr.T.is_call_cont tk). { eapply self__SimplExpr.is_call_cont_preserved; eauto. }
  eexists. split.
  + left. apply plus_one. fconstructor.
    erewrite self__SimplExpr.blocks_of_env_preserved; eauto.
  + econstructor. intros. eapply self__SimplExpr.match_cont_is_call_cont; eauto.
(* label *)
- apply self__SimplExpr.tr_label_inv in TR; unpack TR; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
  + econstructor; eauto.
(* goto *)
- apply self__SimplExpr.tr_goto_inv in TR; unpack TR; subst.
  inversion TRF; subst.
  exploit self__SimplExpr.tr_find_label.
  + refine (self__SimplExpr.T.globalenv tprog).
  + eauto.
  + eapply self__SimplExpr.match_cont_call_cont; eauto.
  + rewrite e0. intros [ts' [tk' [A [B C]]]]. eexists. split.
    * left. apply plus_one. fconstructor.
    * econstructor; eauto.
(* internal function *)
- inv TR. inversion H1; subst.
  eexists. split.
  + left. apply plus_one. fconstructor.
    (* TODO: function_entry *)
    Unshelve. all: eauto; apply cheat.
  + econstructor; eauto.
Qed. FEnd sstep_simulation.

FLemma simulation :
     (forall ge S1 t S2 (_ : C.step ge S1 t S2),
     forall prog tprog tge, match_prog prog tprog -> S.globalenv prog = ge -> T.globalenv tprog = tge ->
     forall T1 (MS : match_states tge S1 T1),
        exists T2,
         (plus Clight.step tge T1 t T2 \/
           (star Clight.step tge T1 t T2 /\ measure S2 < measure S1)%nat)
     /\ match_states tge S2 T2).
FProofLemma.
intros ge S1 t S2 STEP. destruct STEP.
- apply self__SimplExpr.estep_simulation; auto.
- apply self__SimplExpr.sstep_simulation; auto.
Qed. CloseFLemma.

FEnd SimplExpr.

FEnd Base.

Trait Comp_Loops extends Base.

Trait C_Swhile extends C.
FInductive stmt : Type :=
  | Swhile : expr -> stmt -> stmt(* while loop *)
  | Sbreak : stmt(* break stmt *)
  | Scontinue : stmt. (* continue statement *)
FEnd C_Swhile.

Trait C_Sdowhile extends C.
FInductive stmt : Type :=
| Sdowhile : expr -> stmt -> stmt. (* do loop *)
FEnd C_Sdowhile.

Trait C_Sfor extends C.
FInductive stmt : Type :=
| Sfor: stmt -> expr -> stmt -> stmt -> stmt. (* for loop *)
FEnd C_Sfor.

Family C extends C_Swhile, C_Sdowhile, C_Sfor.
FEnd C.

Trait Clight_Sloop extends Clight.
FInductive stmt : Type :=
  | Sloop: stmt -> stmt -> stmt (* infinite loop *)
  | Sbreak : stmt (* break statement *)
  | Scontinue : stmt. (* continue statement *)
FEnd Clight_Sloop.

Family Clight extends Clight_Sloop.
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Swhile extends SimplExpr.
Family S extends C_Swhile. FEnd S.

FRecursion transl_stmt
           with transl_lblstmt.
Case Swhile e s1 :=
(fun ce =>
 do s' <- transl_if e T.Sskip T.Sbreak ce;
 do ts1 <- transl_stmt s1 ce;
 ret (T.Sloop (T.Sseq s' ts1) T.Sskip)).
Case Sbreak := (fun ce => ret T.Sbreak).
Case Scontinue := (fun ce => ret T.Scontinue).
FEnd transl_stmt with transl_lblstmt.

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
FEnd C.

Family Clight.
FInductive stmt : Type :=
| Sbuiltin: option ident -> external_function -> list type -> list expr -> stmt. (* builtin invocation *)
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

FEnd SimplExpr.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

(*| Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
| Epostincr (id: incr_or_decr) (l: expr) (ty: type)
| Eloc (b: block) (ofs: ptrofs) (bf: bitfield) (ty: type) *)

Trait C_Eassignop extends C.
FInductive expr : Type :=
| Eassignop : Cop.binary_operation -> expr -> expr -> type -> type -> expr.

FRecursion typeof.
Case Eassignop op e0 e1 ty' ty := ty.
FEnd typeof.
FEnd C_Eassignop.

Trait C_Epostincr extends C.
FInductive expr : Type :=
  | Epostincr : incr_or_decr -> expr -> type -> expr.

FRecursion typeof.
Case Epostincr a b ty := ty.
FEnd typeof.
FEnd C_Epostincr.

(* This is used internally by the semantics of memory *)
Trait C_Eloc extends C.
FInductive expr : Type :=
  | Eloc : block -> ptrofs -> bitfield -> type -> expr.

FRecursion typeof.
Case Eloc a b c ty := ty.
FEnd typeof.
FEnd C_Eloc.

Trait C_Eaddrof extends C.
FInductive expr : Type :=
| Eaddrof : expr -> type -> expr.

FRecursion typeof.
Case Eaddrof e ty := ty.
FEnd typeof.
FEnd C_Eaddrof.

Trait C_Ederef extends C.
FInductive expr : Type :=
| Ederef : expr -> type -> expr.

FRecursion typeof.
Case Ederef e ty := ty.
FEnd typeof.
FEnd C_Ederef.

Trait C_Evalof extends C.
FInductive expr : Type :=
| Evalof : expr -> type -> expr. (* l-value used as a r-value *)

FRecursion typeof.
Case Evalof e ty := ty.
FEnd typeof.
FEnd C_Evalof.

Trait C_Eassign extends C.
FInductive expr : Type :=
| Eassign : expr -> expr -> type -> expr. (* assignment l = r *)

FRecursion typeof.
Case Eassign e1 e2 ty := ty.
FEnd typeof.
FEnd C_Eassign.

Family C extends
  C_Eassign,
  C_Evalof,
  C_Ederef,
  C_Eaddrof,
  C_Eassignop,
  C_Epostincr,
  C_Eloc.
FEnd C.

Trait Clight_Evar extends Clight.
FInductive expr : Type :=
| Evar: ident -> type -> expr. (* variable *)

FRecursion typeof.
Case Evar i t := t.
FEnd typeof.
FEnd Clight_Evar.

Trait Clight_Ederef extends Clight.
FInductive expr : Type :=
| Ederef: expr -> type -> expr. (* pointer dereference (unary *)

FRecursion typeof.
Case Ederef i t := t.
FEnd typeof.
FEnd Clight_Ederef.

Trait Clight_Eaddrof extends Clight.
FInductive expr : Type :=
| Eaddrof: expr -> type -> expr. (* address-of operator (&) *)

FRecursion typeof.
Case Eaddrof e t := t.
FEnd typeof.
FEnd Clight_Eaddrof.

Trait Clight_Sassign extends Clight.
FInductive stmt : Type :=
| Sassign : expr -> expr -> stmt. (* assignment lvalue = rvalue *)
FEnd Clight_Sassign.

Family Clight extends
  Clight_Sassign,
  Clight_Eaddrof,
  Clight_Ederef,
  Clight_Evar.
FEnd Clight.

Trait SimplExpr_Eassign extends SimplExpr.
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
 do (sl1, a1) <- transl_expr l1 ce self__SimplExpr_Eassign.For_val;
 do (sl2, a2) <- transl_expr r2 ce self__SimplExpr_Eassign.For_val;
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
FEnd SimplExpr_Eassign.

Trait SimplExpr_Evalof extends SimplExpr, SimplExpr_Eassign.
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

(*FRecursion is_bitfield_access about T.expr motive (fun (_ : T.expr) => mon bitfield) by _rect.
Case _ := (ret Full).
FEnd is_bitfield_access.*)

FDefinition transl_valof : composite_env -> type -> T.expr -> mon (list T.stmt * T.expr) := fun ce ty l =>
  if type_is_volatile ty
  then do t <- gensym ty;
       do bf <- is_bitfield_access l ce;
       ret (make_set bf t l :: nil, T.Etempvar t ty)
  else ret (nil, l).

FRecursion transl_expr with transl_exprlist.
Case Evalof l ty :=
(fun ce dst =>
   do (sl1, a1) <- transl_expr l ce self__SimplExpr_Evalof.For_val;
   do (sl2, a2) <- transl_valof ce (S.typeof l) a1;
   ret (finish dst (sl1 ++ sl2) a2)).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Evalof.

Trait SimplExpr_Ederef extends SimplExpr.
Family S extends C_Ederef. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist.
Case Ederef r ty :=
  (fun ce dst => do (sl, a) <- transl_expr r ce self__SimplExpr_Ederef.For_val;
  ret (finish dst sl (T.Ederef a ty))).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Ederef.

Trait SimplExpr_Eaddrof extends SimplExpr.
Family S extends C_Eaddrof. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist.
Case Eaddrof l ty :=
   (fun ce dst => do (sl, a) <- transl_expr l ce self__SimplExpr_Eaddrof.For_val;
      ret (finish dst sl (T.Eaddrof a ty))).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Eaddrof.

Trait SimplExpr_Eassignop extends SimplExpr_Evalof, SimplExpr_Eassign, SimplExpr.
Family S extends C_Eassignop. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.

FRecursion transl_expr with transl_exprlist.
Case Eassignop op l1 r2 tyres ty :=
  (fun ce dst =>
     let ty1 := S.typeof l1 in
      do (sl1, a1) <- transl_expr l1 ce self__SimplExpr_Eassignop.For_val;
      do (sl2, a2) <- transl_expr r2 ce self__SimplExpr_Eassignop.For_val;
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

FEnd SimplExpr_Eassignop.

Trait SimplExpr_Epostincr extends SimplExpr_Evalof, SimplExpr_Eassign, SimplExpr.
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
      do (sl1, a1) <- transl_expr l1 ce self__SimplExpr_Epostincr.For_val;
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

FEnd SimplExpr_Epostincr.

Trait SimplExpr_Eloc extends SimplExpr.
Family S extends C_Eloc. FEnd S.

FRecursion eval_simpl_expr.
Case _ := None.
FEnd eval_simpl_expr.


FRecursion transl_expr with transl_exprlist.
Case Eloc b ofs bf ty :=
   (fun ce dst => error (msg "SimplExpr.transl_expr: Eloc")).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr_Eloc.

Family SimplExpr
  extends
  SimplExpr_Eassign,
  SimplExpr_Evalof,
  SimplExpr_Ederef,
  SimplExpr_Eaddrof,
  SimplExpr_Eassignop,
  SimplExpr_Epostincr,
  SimplExpr_Eloc.
FEnd SimplExpr.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.
Family C.
FInductive expr : Type :=
| Efield : expr -> ident -> type -> expr.

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.
FEnd C.

Family Clight.
FInductive expr : Type :=
| Efield: expr -> ident -> type -> expr. (* access to a member of a struct or union *)

FRecursion typeof.
Case Efield e i ty := ty.
FEnd typeof.

FEnd Clight.

Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

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

FRecursion transl_expr with transl_exprlist.
Case Efield r f ty :=
  (fun ce dst =>
    do (sl, a) <- transl_expr r ce self__SimplExpr.For_val;
    ret (finish dst sl (T.Efield a f ty))).
FEnd transl_expr with transl_exprlist.
FEnd SimplExpr.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family C.
FInductive expr : Type :=
| Ecall : expr -> exprlist -> type -> expr.

FRecursion typeof.
Case Ecall e args t := t.
FEnd typeof.

FEnd C.

Family Clight.
FInductive stmt : Type :=
| Scall: option ident -> expr -> list expr -> stmt. (* function call *)

FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Family SimplExpr.
Family S extends C. FEnd S.
Family T extends Clight. FEnd T.

FRecursion transl_expr with transl_exprlist.
Case Ecall r1 rl2 ty :=
  (fun ce dst =>
   do (sl1, a1) <- transl_expr r1 ce self__SimplExpr.For_val;
   do (sl2, al2) <- cheat (*transl_exprlist rl2*);
   match dst with
   | self__SimplExpr.For_val | self__SimplExpr.For_set _ =>
       do t <- gensym ty;
       ret (finish dst (sl1 ++ sl2 ++ T.Scall (Some t) a1 al2 :: nil)
                       (T.Etempvar t ty))
   | self__SimplExpr.For_effects =>
       ret (sl1 ++ sl2 ++ T.Scall None a1 al2 :: nil, dummy_expr)
   end).
FEnd transl_expr with transl_exprlist.

FEnd SimplExpr.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait C_Switch extends C.
FInductive stmt : Type :=
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)

FEnd C_Switch.

Family C extends C_Switch.
FEnd C.

Trait Clight_Switch extends Clight.
FInductive stmt : Type :=
| Sswitch : expr -> lbl_stmts -> stmt. (* switch statement *)
FEnd Clight_Switch.

Family Clight extends Clight_Switch.
FEnd Clight.

From Rocqet Require Import Mon.
Local Open Scope gensym_monad_scope.

Trait SimplExpr_Switch extends SimplExpr.
Family S extends C_Switch. FEnd S.

FRecursion transl_stmt with transl_lblstmt.
Case Sswitch e ls :=
(fun ce =>
   do (s', a) <- transl_expression e ce;
   do tls <- transl_lblstmt ls ce;
 ret (T.Sseq s' (T.Sswitch a tls))).
FEnd transl_stmt with transl_lblstmt.

FEnd SimplExpr_Switch.

Family SimplExpr extends SimplExpr_Switch.
FEnd SimplExpr.

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

Family SimplExpr.
Final Family S := C.
Final Family T := Clight.
FEnd SimplExpr.

FEnd Comp.

Require Extraction.
Cd "extraction".

Separate Extraction Comp.SimplExpr.

Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.


(*Family CompX extends Comp_Loops.

Family SimplExpr.
Final Family S := C.
Final Family T := Clight.
FEnd SimplExpr.

Family Cshmgen.
Final Family S := Clight.
Final Family T := Csharpminor.
FEnd Cshmgen.

Family Cminorgen.
Final Family S := Csharpminor.
Final Family T := Cminor.
FEnd Cminorgen.

Family Selection.
Final Family S := Cminor.
Final Family T := CminorSel.
FEnd Selection.

Family RTLgen.
Final Family S := CminorSel.
Final Family T := RTL.
FEnd RTLgen.

Inherit Lfam.
Family Linear extends Lfam. FEnd Linear.
Family Mach extends Lfam. FEnd Mach.

Family Linearize.
Final Family S := LTL.
Final Family T := Linear.

FEnd Linearize.

Family Stacking.
Final Family S := Linear.
Final Family T := Mach.
FEnd Stacking.

Family Asmgen.
Final Family S := Mach.
FEnd Asmgen.

FEnd CompX.*)


(*

 Require Extraction.
Cd "extract_lib".
Extraction Library AST.
Extraction Library Ascii.

Extraction Library Archi.
Extraction Library BinInt.
Extraction Library BinNums.
Extraction Library Bool.
Extraction Library Coqlib.
Extraction Library Datatypes.
Extraction Library Errors.
Extraction Library Floats.
Extraction Library Integers.
Extraction Library List.
Extraction Library Maps.
Extraction Library Specif.
Extraction Library String.

Extraction Library Coqlib.
Extraction Library AST.
Extraction Library Builtins0.
Extraction Library Events.
Extraction Library Intv.
Extraction Library Archi.
Extraction Library Builtins1.
Extraction Library Linking.
Extraction Library Ordered.
Extraction Library Floats.
Extraction Library Maps.
Extraction Library Values.
Extraction Library Axioms.
Extraction Library Globalenvs.
Extraction Library Memdata.
Extraction Library Zbits.
Extraction Library Ctypes.
Extraction Library IEEE754_extra.
Extraction Library Memory.
Extraction Library Smallstep.
Extraction Library Builtins.
Extraction Library Errors.
Extraction Library Integers.
Extraction Library Memtype.
Extraction Library Cop.
Extraction Library Mon.
Extraction Library Prelude.
From Rocqet Require Import Registers.
Extraction Library Registers.
From Rocqet Require Import Decidableplus.
Extraction Library Decidableplus.
From Rocqet Require Import Machregs.
Extraction Library Machregs.
From Rocqet Require Import Locations.
Extraction Library Locations.
From Rocqet Require Import Conventions1.
Extraction Library Conventions1.
From Rocqet Require Import Mregisters.
Extraction Library Mregisters.
From Rocqet Require Import RTLmonad.
Extraction Library RTLmonad.
From Rocqet Require Import Heaps.
Extraction Library Heaps.
From Rocqet Require Import Kildall.
Extraction Library Kildall.
From Rocqet Require Import Lattice.
Extraction Library Lattice.
From Rocqet Require Import Iteration.
Extraction Library Iteration.
From Rocqet Require Import Wfsimpl.
Extraction Library Wfsimpl.
From Rocqet Require Import Bounds.
Extraction Library Bounds.
From Rocqet Require Import Separation.
Extraction Library Separation.
From Rocqet Require Import Stacklayout.
Extraction Library Stacklayout.
From Rocqet Require Import Switch.
Extraction Library Switch.
From Rocqet Require Import Op.
Extraction Library Op.
From Rocqet Require Import BoolEqual.
Extraction Library BoolEqual.

Separate Extraction AST.*)
