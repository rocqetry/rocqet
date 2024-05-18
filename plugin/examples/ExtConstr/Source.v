(* Take 1 *)
family STLC {
  Inductive Ty : Set := TUnit : Ty | TNat : Ty | TTuple : Ty -> Ty 
}

family PairExt { 
  Inductive Ty : Set += TTuple : Ty -> Ty -> Ty
  Default TTuple TUnit.
}


(* Take 2 *)
(* From https://github.com/DKXXXL/FPOP/blob/main/showcase_test/STLC_families.v *)
family STLC {
    FInductive ty: Set :=
     | ty_unit : ty
     | ty_arrow : ty -> ty -> ty.

   FInductive tm : Set :=
     | tm_var : ident -> tm    
     | tm_abs : ident -> tm -> tm
     | tm_app : tm -> tm -> tm
     | tm_unit: tm.

   FInductive value : self__STLC.tm -> Prop :=
    | vabs   : forall x body , (value (self__STLC.tm_abs x body))
    | vtunit : value (self__STLC.tm_unit).

  
  FRecursion subst 
    about tm 
    motive ((fun (_ : tm) => (ident -> tm -> tm))) by _rec.
     Case tm_var  
       := (fun s x t => if (eqb x s) then t else (self__STLC.tm_var s)).
     
     Case tm_abs 
       := (fun s body rec_body => 
          fun x t => 
         if (eqb x s) 
         then (self__STLC.tm_abs s body)
         else (self__STLC.tm_abs s (rec_body x t))).
     
    (* You will have to write a new case if you 
       add a new argument to tm_app *)
     Case tm_app 
       := (fun t rec_t t0 rec_t0 => 
         fun x t' =>
         self__STLC.tm_app (rec_t x t') (rec_t0 x t')).
     
     Case tm_unit 
       := (fun x t => self__STLC.tm_unit).
     
  FEnd subst.
}

family STLCAppCount extends STLC { 
    FInductive tm : Set :=          
     | tm_app : tm -> tm -> [nat] -> tm     
}




