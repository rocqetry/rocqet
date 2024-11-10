From NFPOP Require Import Loader.

Trait Comp_Base.
FDefinition ident := nat.
Family C.

FDefinition val := nat.

FInductive expr : Type :=
| Eval : val  -> expr (* constant *)
| Evar : ident  -> expr. (* variable *)        

FDefinition label := ident.     
FInductive stmt : Type :=
| Sseq : stmt -> stmt -> stmt
| Sskip : stmt
| Sdo : expr -> stmt(* evaluate expression for side effects *)        
| Sifthenelse : expr -> stmt -> stmt -> stmt. (* conditional *)
FEnd C.

Family Cfam.
FInductive expr : Type :=
| Evar : ident -> expr. (* reading a temporary variable *)

FDefinition label := ident.

FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt.
FEnd Cfam.

Family Constant.
FInductive constant : Type :=
| Ointconst:  constant (* integer constant *)
| Ofloatconst: constant (* double-precision floating-point constant *)
| Osingleconst: constant (* single-precision floating-point constant *)
| Olongconst: constant.
FEnd Constant.

Family Csharpminor extends Cfam.
FInductive expr : Type := Econst : Constant.constant -> expr. (* constants *)
FInductive stmt : Type := Sifthenelse: expr -> stmt -> stmt -> stmt.
FEnd Csharpminor.

Family Cshmgen. 

FRecursion transl_expr about C.expr motive (fun (_ : C.expr) => Csharpminor.expr) by _rect.
Case _ := (Csharpminor.Econst Constant.Ointconst).
FEnd transl_expr.

FEnd Cshmgen. 

FEnd Comp_Base.

Trait Comp_Loops extends Comp_Base.


Family Cfam.
FInductive stmt : Type :=
  | Sloop: stmt -> stmt.
FEnd Cfam.

Family Csharpminor extends Cfam.
FEnd Csharpminor.

FEnd Comp_Loops.
