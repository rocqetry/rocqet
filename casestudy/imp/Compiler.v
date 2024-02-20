(* A Compiler for Imp *)

(* Definition id := ... *)

Inductive instruction: Type :=
  | Iconst(n: nat)                 (**r push integer [n] on stack *)
  | Ivar(x: id)                    (**r push the value of variable [x] *)
  | Isetvar(x: id)                 (**r pop an integer, assign it to variable [x] *)
  | Iadd                           (**r pop [n2], pop [n1], push back [n1+n2] *)
  | Isub                           (**r pop [n2], pop [n1], push back [n1-n2] *)
  | Imul                           (**r pop [n2], pop [n1], push back [n1*n2] *)
  | Ibranch_forward(ofs: nat)      (**r skip [ofs] instructions forward *)
  | Ibranch_backward(ofs: nat)     (**r skip [ofs] instructions backward *)
  | Ibeq(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1=n2] *)
  | Ibne(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<>n2] *)
  | Ible(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<=n2] *)
  | Ibgt(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1>n2] *)
  | Ihalt.                         (**r terminate execution successfully *)

Definition code := list instruction.

Fixpoint code_at (C: code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i :: C', O => Some i
  | i :: C', S pc' => code_at C' pc'
  end.

Definition stack := list nat.

Definition configuration := (nat * stack * state)%type.

Inductive transition (C: code): configuration -> configuration -> Prop :=
  | trans_const: forall pc stk s n,
      code_at C pc = Some(Iconst n) ->
      transition C (pc, stk, s) (pc + 1, n :: stk, s)
  | trans_var: forall pc stk s x,
      code_at C pc = Some(Ivar x) ->
      transition C (pc, stk, s) (pc + 1, s x :: stk, s)
  | trans_setvar: forall pc stk s x n,
      code_at C pc = Some(Isetvar x) ->
      transition C (pc, n :: stk, s) (pc + 1, stk, t_update s x n)
  | trans_add: forall pc stk s n1 n2,
      code_at C pc = Some(Iadd) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 + n2) :: stk, s)
  | trans_sub: forall pc stk s n1 n2,
      code_at C pc = Some(Isub) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 - n2) :: stk, s)
  | trans_mul: forall pc stk s n1 n2,
      code_at C pc = Some(Imul) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 * n2) :: stk, s)
  | trans_branch_forward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      transition C (pc, stk, s) (pc', stk, s)
  | trans_branch_backward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      transition C (pc, stk, s) (pc', stk, s)
  | trans_beq: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibeq ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bne: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibne ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_ble: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ible ofs) ->
      pc' = (if leb n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bgt: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibgt ofs) ->
      pc' = (if leb n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s).

Definition mach_terminates (C: code) (s_init s_fin: state) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, nil, s_init) (pc, nil, s_fin).

Definition mach_diverges (C: code) (s_init: state) :=
  infseq (transition C) (0, nil, s_init).

Definition mach_goes_wrong (C: code) (s_init: state) :=
  exists pc, exists stk, exists s_fin,
  star (transition C) (0, nil, s_init) (pc, stk, s_fin)
  /\ irred (transition C) (pc, stk, s_fin)
  /\ (code_at C pc <> Some Ihalt \/ stk <> nil).

Lemma machine_deterministic:
  forall C config config1 config2,
  transition C config config1 -> transition C config config2 -> config1 = config2.
Proof.
  intros. inversion H; subst; inversion H0; try congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (leb n1 n2); congruence.
  destruct (leb n1 n2); congruence.
Qed.

Remark stop_irred:
  forall C pc stk st,
  code_at C pc = Some Ihalt -> irred (transition C) (pc, stk, st).
Proof.
  unfold irred; intros. unfold not; intros. inversion H0; congruence.
Qed.

Lemma terminates_unique:
  forall C st st1 st2, mach_terminates C st st1 -> mach_terminates C st st2 -> st1 = st2.
Proof.
  unfold mach_terminates; intros. destruct H as (pc1 & A1 & B1), H0 as (pc2 & A2 & B2).
  assert (((pc1, nil, st1) : configuration) = ((pc2, nil, st2) : configuration)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  congruence. 
Qed.

Lemma terminates_goeswrong_exclusive:
  forall C st st', mach_terminates C st st' -> mach_goes_wrong C st -> False.
Proof.
  unfold mach_terminates, mach_goes_wrong; intros.
  destruct H as (pc1 & A1 & B1), H0 as (pc2 & stk2 & st2 & A2 & B2 & C2).
  assert (((pc1, nil, st') : configuration) = ((pc2, stk2, st2) : configuration)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  inversion H. subst pc2 stk2 st2. destruct C2; congruence.
Qed.

Lemma terminates_diverges_exclusive:
  forall C st st', mach_terminates C st st' -> mach_diverges C st -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.



