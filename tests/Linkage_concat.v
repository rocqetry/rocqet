Require Import Rocqet.Loader.

Family Xe.
   FInductive expr : Type :=
      | expr_unit : expr
      | expr_nat : nat -> expr
      | expr_bool : bool -> expr.
   FDefinition d := 10.
   Family Language.
       FInductive fexpr : Type :=
          | fexpr_unit : fexpr
          | fexpr_nat : nat -> fexpr
          | fexpr_bool : bool -> fexpr.
       Family Expr.
           FDefinition x0 := 13.
           
           (*FInductive expr : Type :=
             | expr_unit : expr
             | expr_nat : nat -> expr
             | expr_bool : bool -> expr.*)
    
           FDefinition y0 := expr_nat.             
           
           Family Ty.
               FDefinition u0 := y0.
               
               FInductive ty : Type := 
                 | ty_unit : ty
                 | ty_nat : ty
                 | ty_bool : ty.

               FDefinition g0 := u0.
               
               Family Value.
                   FInductive constant : Type := 
                     | const_nat : nat -> constant
                     | const_bool : bool -> constant.
               
                   FInductive val : Type := 
                     | val_unit : val
                     | val_nat : nat -> val
                     | val_bool : bool -> val.
                   
                   FDefinition v0 := val.
               FEnd Value. 
               FDefinition i0  := ty_unit.
           FEnd Ty.                      
           FDefinition h0 := Ty.g0.
       FEnd Expr.       
       FDefinition v1 := expr_unit.
   FEnd Language.      
   FDefinition v0 := Language.Expr.y0.

   Family Ld extends Language.
   FEnd Ld.
FEnd Xe.

Family Xa extends Xe.
    FDefinition ident := nat.
    FInductive expr : Type :=                          
       | expr_lam : ident -> expr.
    Family Language. 
        FInductive fexpr : Type :=                          
           | fexpr_lam : ident -> fexpr.
        Family Expr.
            (*FDefinition ident := nat.
            FInductive expr : Type :=                          
             | expr_lam : ident -> expr.*)

            Family Ty.
                FInductive ty : Type :=                                   
                 | ty_arrow : ty -> ty -> ty.

                Family Value.
                    FInductive val : Type :=                                           
                     | val_clo : ident -> expr -> val.
                FEnd Value.
            FEnd Ty.
        FEnd Expr.
    FEnd Language.       
FEnd Xa.

Family Xo extends Xe.
    FDefinition ident := nat.
    FInductive expr : Type :=                          
       | expr_prod : expr -> expr -> expr.
    Family Language. 
        Family Expr.            
            (*FDefinition ident := nat.
            FInductive expr : Type :=                          
             | expr_prod : expr -> expr -> expr.*)

            Family Ty.
                FInductive ty : Type :=                                   
                 | ty_prod : ty -> ty -> ty.

                Family Value.
                    FInductive val : Type :=                                           
                     | val_prod : ident -> expr -> val.
                FEnd Value.
            FEnd Ty.
        FEnd Expr.
    FEnd Language.
FEnd Xo.

Family m extends Xe, Xa, Xo.
FEnd m.

Print m.Language.Expr.Ty.


Family Tl.
   Family Source extends Xe.
      FInductive x : Type := X000 : x.
   FEnd Source.
   
   Family Target extends Xe.
   FEnd Target.
FEnd Tl.

Print Tl.Source.

Family Tla extends Tl.
    Family Source extends Xa.
        FInductive x : Type := Y000 : x.
    FEnd Source.
    
    Family Target extends Xa.
    FEnd Target.
FEnd Tla.

Print Tla.Source.

Family Tlo extends Tla.
   Family Source extends Xo.
   FEnd Source.
    
   Family Target extends Xo.
   FEnd Target.
FEnd Tlo.

Print Tlo.Target.Language.Expr.Ty.


(*Family X extends A using B, C, D.
FEnd X.*)
