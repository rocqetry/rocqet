Require Import Rocqet.Loader.

(*FRecursion subst
  with subst_ls about lbl_expr motive (fun (_ : expr) => ...) by _rect.

FEnd subst with subst_ls.*)

Axiom cheat : forall {x}, x.

Family STLC_base.
FDefinition ident := nat.

FInductive tm : Set :=
| tm_var : ident -> tm
| tm_app : tm -> tm -> tm.

FRecursion comb_size_tm about tm motive (fun (_ : tm) => nat) by _rect.
  (*with comb_size_val about val motive (fun (_ : val) => nat) by _rect.*)
Case tm_var := (fun i => 0).
Case tm_app := (fun f F a A => 0).

FEnd comb_size_tm. (* with comb_size_val.*)


FInduction comb_tm_size_tm about tm motive (fun (t : tm) => comb_size_tm t = 0).
  (*with comb_val_size_tm about val motive (fun (v : val) => comb_size_val v = 0).*)
FProof.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity.  
Qed. FEnd comb_tm_size_tm. (*with comb_val_size_tm.*)


FEnd STLC_base.

Family STLC_ext extends STLC_base.
FInductive tm : Set :=
| tm_val : val -> tm
with val : Set :=
| val_abs : ident -> tm -> val
| val_unit: val.

FRecursion comb_size_tm about tm motive (fun (_ : tm) => nat)
  with comb_size_val about val motive (fun (_ : val) => nat) by _rect.

Case tm_val v := 0.

Case val_abs i e := 10.
Case val_unit := 17.

FEnd comb_size_tm with comb_size_val.

FInduction comb_tm_size_tm about tm motive (fun (t : tm) => comb_size_tm t = 0)
  with comb_val_size_tm about val motive (fun (v : val) => comb_size_val v = 0).
FProof.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. apply cheat.
+ intros. fsimpl. apply cheat.  
Qed. FEnd comb_tm_size_tm with comb_val_size_tm.

FEnd STLC_ext.

Family STLC_X extends STLC_base, STLC_ext.

FEnd STLC_X.
