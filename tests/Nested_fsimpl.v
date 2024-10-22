From NFPOP Require Import Loader.

Notation ident := nat.

Family STLCBase.
  FInductive Ty: Set :=
     | TUnit : Ty
     | TArr : Ty -> Ty -> Ty.

  Family X.
  FRecursion subst about Ty motive (fun (_ : Ty) => nat) by _rec.
     Case TUnit := 1.
     Case TArr := (fun _ n _ m => 1).
  FEnd subst.  
  FEnd X.
  
  FInduction easy_theorem
    about Ty
    motive (fun (t : Ty) => X.subst t = 1).
  FProof.          
  + fsimpl. reflexivity.
  + intros. fsimpl. reflexivity.
  Qed. FEnd easy_theorem.
FEnd STLCBase.
