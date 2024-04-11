

CoInductive itree (E : Type -> Type) (R : Type) : Type :=
  | Ret (r : R)
  | Tau (t : itree E R)
  | Vis { A : Type } (e : E A) (k :  A -> itree E R).

Inductive IO : Type -> Type := 
  | Input : IO nat
  | Output : nat -> IO unit.

Inductive void := .

CoFixpoint spin : itree IO void := Tau IO void spin.

Check Tau.

Context { E : Type -> Type } { A B : Type } (r : A -> B -> Prop).

