From NFPOP Require Import Loader.

Definition ident := nat.

Family STLC0.    
FInductive tm : Set :=
| tm_var : ident -> tm
| tm_app : tm -> tm -> tm
with val : Set :=
| val_abs : ident -> tm -> val.
FEnd STLC0.

Family STLC0_val extends STLC0.
FInductive tm : Set :=
| tm_val : val -> tm
with val : Set :=
| val_unit: val.

FEnd STLC0_val.

Family STLC.    
FInductive tm : Set :=
| tm_var : ident -> tm
| tm_app : tm -> tm -> tm.
FEnd STLC.

Family STLC_val extends STLC.
FInductive tm : Set :=
| tm_val : val -> tm
with val : Set :=
| val_abs : ident -> tm -> val
| val_unit: val.

FRecursion tm_size about tm motive (fun (_ : tm) => nat) by _rec.
Case tm_var := (fun i => 0).
Case tm_app := (fun f H a A => 0).
Case tm_val := (fun v => 0).
FEnd tm_size.

FRecursion val_size about val motive (fun (_ : val) => nat) by _rec.
Case val_abs := (fun i t => 0).
Case val_unit := 0.
FEnd val_size.

FInduction tm_size_tm about tm motive (fun (t : tm) => tm_size t = 0).
FProof.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity.
Qed. FEnd tm_size_tm.

FInduction val_size_tm about val motive (fun (v : val) => val_size v = 0).
FProof.
+ intros. fsimpl. reflexivity.
+ fsimpl. reflexivity.
Qed. FEnd val_size_tm.

FRecursion comb_size_tm about tm motive (fun (_ : tm) => nat)
  with comb_size_val about val motive (fun (_ : val) => nat) by _rect.
Case tm_var := (fun i => 0).
Case tm_app := (fun f F a A => 0).
Case tm_val := (fun v V => 0).

Case val_abs := (fun i t T => 0).
Case val_unit := 0.
FEnd comb_size_tm with comb_size_val.

FInduction comb_tm_size_tm about tm motive (fun (t : tm) => comb_size_tm t = 0)
  with comb_val_size_tm about val motive (fun (v : val) => comb_size_val v = 0).
FProof.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity. 

+ intros. fsimpl. reflexivity.
+ fsimpl. reflexivity.
Qed. FEnd comb_tm_size_tm with comb_val_size_tm.

FEnd STLC_val.
