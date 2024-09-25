From NFPOP Require Import Loader.

Definition int := nat.
Definition float := nat.
Definition int64 := nat.
Definition float32 := nat.
Definition ident := nat.

Family Imp.
   (*MetaData type.*)
     FInductive type : Type :=
      | Tvoid: type(* the void type *).
   (*FEnd type.*)
    
   (*MetaData val.*)
      FInductive val: Type :=
        | Vundef: val
        | Vint: int -> val
        | Vlong: int64 -> val
        | Vfloat: float -> val
        | Vsingle: float32 -> val.
   (*FEnd val.*)

   Family I.
      FDefinition blah := nat.
      Family Clight.                    
          FInductive expr : Type :=          
             | Econst_int: blah -> int -> type -> expr(* integer literal *)
             | Econst_float: float -> type -> expr(* double float literal *)
             | Econst_single: float32 -> type -> expr(* single float literal *)
             | Econst_long: int64 -> type -> expr(* long integer literal *)                                            
             | Etempvar: ident -> type -> expr (* temporary variable *)          
             | Esizeof: type -> type -> expr (* size of a type *)
             | Ecast: expr -> type -> expr
             | Ealignof: type -> type -> expr. (* alignment of a type *)
      FEnd Clight.
   FEnd I.

   Family SimplExpr. 
       FRecursion eval_simpl_expr about I.Clight.expr motive (fun (_ : I.Clight.expr) => option val) by _rect.
          Case Econst_int := (fun _ n ty => Some(self__Imp.Vint n)).
          Case Econst_float := (fun n ty => Some(self__Imp.Vfloat n)).          
          Case Econst_single := (fun n ty => Some(self__Imp.Vsingle n)).
          Case Econst_long := (fun n ty => Some(self__Imp.Vlong n)).
          Case Ecast := (fun b eval_simpl_expr_b ty  => 
                            match eval_simpl_expr_b with
                            | None => None
                            | Some v => None
                            end).
          Case Etempvar := (fun id ty => None).
          Case Esizeof := (fun _ _ => None).
          Case Ealignof := (fun _ _ => None).
      FEnd eval_simpl_expr.
   FEnd SimplExpr.    
FEnd Imp.
