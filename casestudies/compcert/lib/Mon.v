Require Import Ctypes.
Require Import AST.
Require Import Coqlib.
          
Local Open Scope string_scope.
Local Open Scope list_scope.

Record generator : Type := mkgenerator {
   gen_next: ident;
   gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
| Err: Errors.errmsg -> result A g
| Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200)
  : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).
