Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Registers.

Record mapping: Type := mkmapping {
  map_vars: PTree.t reg;
  map_letvars: list reg
}.

Record state (A : Type) : Type := mkstate {
  st_nextreg: positive;
  st_nextnode: positive;
  st_code: PTree.t A;
  st_wf: forall (pc: positive), Plt pc st_nextnode \/ st_code!pc = None
}.

Inductive state_incr (A : Type) : state A -> state A -> Prop :=
  state_incr_intro:
    forall (s1 s2: state A),
    Ple s1.(st_nextnode A) s2.(st_nextnode A) ->
    Ple s1.(st_nextreg A) s2.(st_nextreg A) ->
    (forall pc,
      s1.(st_code A)!pc = None \/ s2.(st_code A)!pc = s1.(st_code A)!pc) ->
    state_incr A s1 s2.

Lemma state_incr_refl:
  forall A s, state_incr A s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl. apply Ple_refl. intros; auto.
Qed.

Lemma state_incr_trans:
  forall A s1 s2 s3, state_incr A s1 s2 -> state_incr A s2 s3 -> state_incr A s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode A s2); assumption.
  apply Ple_trans with (st_nextreg A s2); assumption.
  intros. generalize (H3 pc) (H5 pc). intuition congruence.
Qed.

Inductive res (A: Type) (C: Type) (s: state C): Type :=
  | Error: Errors.errmsg -> res A C s
  | OK: A -> forall (s': state C), state_incr C s s' -> res A C s.

Arguments OK [A C s].
Arguments Error [A C s].

Definition mon (A: Type) (C : Type) : Type := forall (s: state C), res A C s.

Definition ret {A: Type} {C: Type} (x: A) : mon A C :=
  fun (s: state C) => OK x s (state_incr_refl C s).

Definition error {A: Type} {C: Type} (msg: Errors.errmsg) : mon A C := fun (s: state C) => Error msg.

Definition bind {A B C: Type} (f: mon A C) (g: A -> mon B C) : mon B C :=
  fun (s: state C) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i' => OK b s'' (state_incr_trans C s s' s'' i i')
        end
    end.

Definition bind2 {A B C D: Type} (f: mon (A * B) D) (g: A -> B -> mon C D) : mon C D :=
  bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error {A: Type} {C: Type} (f g: mon A C) : mon A C :=
  fun (s: state C) =>
    match f s with
    | OK a s' i => OK a s' i
    | Error _ => g s
    end.


