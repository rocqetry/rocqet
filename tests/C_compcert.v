From NFPOP Require Import Loader.

Family Imp.     
  FDefinition type := nat.
  FDefinition val := nat.
  FDefinition ident := nat.
  
  Family C.
      FInductive expr : Type :=
        | Eval : val -> type -> expr (* constant *)
        | Evar : ident -> type -> expr (* variable *)        
        | Ecast : expr -> type -> expr (* type cast (ty)r *)
        | Eseqand : expr -> expr -> type -> expr (* sequential "and" r1 && r2 *)
        | Eseqor : expr -> expr -> type -> expr (* sequential "or" r1 || r2 *)
        | Econdition : expr -> expr -> expr -> type -> expr (* conditional r1 ? r2 : r3 *)
        | Esizeof : type -> type -> expr (* size of a type *)
        | Ealignof : type -> type -> expr (* natural alignment of a type *)        
        | Ecomma : expr -> expr -> type -> expr (* sequence expression r1, r2 *)                
        | Eparen : expr -> type -> type -> expr. 
        
        FRecursion typeof : (e : expr) -> type.
          Case Eval v ty := ty.
          Case Evar x ty := ty.          
          Case Ecast r ty := ty. 
          Case Eseqand r1 r2 ty := ty. 
          Case Eseqor r1 r2 ty := ty. 
          Case Econdition r1 r2 r3 ty := ty.
          Case Esizeof ty' ty := ty.
          Case Ealignof ty' ty := ty.          
          Case Ecomma r1 r2 ty := ty.
          Case Eparen e ty' ty := ty.
        FEnd typeof.                
  FEnd C.
FEnd Imp.

      
