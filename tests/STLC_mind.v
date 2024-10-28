From NFPOP Require Import Loader.

Definition ident := nat.

Family STLC.    
FInductive tm : Set :=
| tm_var : ident -> tm
| tm_app : tm -> tm -> tm
| tm_val : val -> tm
with val : Set :=
| val_abs : ident -> tm -> val
| val_unit: val.

FRecursion tm_size about tm motive (fun (_ : tm) => nat) by _rec.
Case tm_var := (fun i => 0).
Case tm_app := (fun f H a A => 0).
Case tm_val := (fun v => 0).
FEnd tm_size.

FInduction tm_size_tm about tm motive (fun (t : tm) => tm_size t = 0).
FProof.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity.
Qed. FEnd tm_size_tm.

FRecursion val_size about val motive (fun (_ : val) => nat) by _rec.
Case val_abs := (fun i t => 0).
Case val_unit := 0.
FEnd val_size.

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

FEnd STLC.

Family STLC_bool extends STLC.  
FInductive tm : Set :=
| tm_if : tm -> tm -> tm -> tm
with val : Set :=
| val_true : val
| val_false : val.  

FRecursion tm_size.
Case tm_if := (fun t0 T0 t1 T1 t3 T3 => 0).
FEnd tm_size.

FInduction tm_size_tm.
FProof.
+ intros. fsimpl. reflexivity.
Qed.  FEnd tm_size_tm.

FRecursion val_size.
Case val_true := 0.
Case val_false := 0.
FEnd val_size.

FInduction val_size_tm.
FProof.
+ fsimpl. reflexivity. 
+ fsimpl. reflexivity. 
Qed. FEnd val_size_tm.

FRecursion comb_size_tm with comb_size_val.
Case tm_if := (fun t0 T0 t1 T1 t3 T3 => 0).

Case val_true := 0.
Case val_false := 0.
FEnd comb_size_tm with comb_size_val.

FInduction comb_tm_size_tm with comb_val_size_tm.
FProof. 
+ intros. fsimpl. reflexivity.

+ fsimpl. reflexivity. 
+ fsimpl. reflexivity. 
Qed. FEnd comb_tm_size_tm with comb_val_size_tm.

FEnd STLC_bool.

Family STLC_prod extends STLC.
FInductive tm : Set :=
| tm_prod : tm -> tm -> tm
| tm_pi1 : tm -> tm
| tm_pi2 : tm -> tm
with val : Set :=
| val_prod : val -> val -> val.

FRecursion tm_size.
Case tm_prod := (fun t0 T0 t1 T1 => 0).
Case tm_pi1 := (fun t T0 => 0).
Case tm_pi2 := (fun t T0 => 0).
FEnd tm_size.

FInduction tm_size_tm.
FProof.
+ intros. fsimpl. reflexivity. 
+ intros. fsimpl. reflexivity.
+ intros. fsimpl. reflexivity. 
Qed. FEnd tm_size_tm.

FRecursion val_size.
Case val_prod := (fun v0 V0 v1 V1 => 0).
FEnd val_size.

FInduction val_size_tm.
FProof.
+ intros. fsimpl. reflexivity.
Qed. FEnd val_size_tm.

FRecursion comb_size_tm with comb_size_val.
Case tm_prod := (fun t0 T0 t1 T1 => 0). 
Case tm_pi1 :=  (fun t0 T0 => 0). 
Case tm_pi2 :=  (fun t0 T0  => 0). 

Case val_prod := (fun v0 V0 v1 V1 => 0).
FEnd comb_size_tm with comb_size_val.

FInduction comb_tm_size_tm with comb_val_size_tm.
FProof. 
+ intros. fsimpl. reflexivity. 
+ intros. fsimpl. reflexivity.  
+ intros. fsimpl. reflexivity.  

+ intros. fsimpl. reflexivity. 
Qed. FEnd comb_tm_size_tm with comb_val_size_tm.

FEnd STLC_prod.

Family all extends STLC, STLC_bool, STLC_prod.
FEnd all.
