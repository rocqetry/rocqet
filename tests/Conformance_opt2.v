(* The plugin *)
From NFPOP Require Import Loader.

Axiom cheat : forall {X}, X.

Notation ident := nat.
Notation constant := nat.
Notation unary_operation := nat.
Notation binary_operation := nat.

Family BaseExt.  
  (* We use the val from the CompCert lib *)
  (* FInductive val: Type :=
     | Vundef: val
     | Vint: int -> val. *)
    
  Family Base.    
  FInductive expr : Type :=
    | Evar : ident -> expr (* reading a temporary variable *)            
    | Econst : constant -> expr (* constants *)          
    | Eunop : unary_operation -> expr -> expr(* unary operation *)
    | Ebinop : binary_operation -> expr -> expr -> expr.

  FInductive stmt : Type :=
    | Sskip: stmt
    | Sset : ident -> expr -> stmt            
    | Sseq: stmt -> stmt -> stmt.  
  FEnd Base.

  Family Basetransl.  
  Family Source extends Base.
  
  FEnd Source.  

  Family Target extends Base. 
  FEnd Target.

  FRecursion transl_expr about Source.expr motive (fun (_ : Source.expr) => Target.expr) by _rect.
  Case Evar := (fun id => (Target.Evar id)).
  Case Econst := (fun c => (Target.Econst c)).
  Case Eunop := (fun op e transl_expr_e =>
                   let te := transl_expr_e in
                   (Target.Eunop op te)).
  Case Ebinop := (fun op e0 transl_expr_e0 e1 transl_expr_e1 =>
     let te0 := transl_expr_e0 in
     let te1 := transl_expr_e1 in           
     (Target.Ebinop op te0 te1)).
  FEnd transl_expr.
  
  FRecursion transl_stmt about Source.stmt motive (fun (_ : Source.stmt) => Target.stmt) by _rect.
  Case Sskip := ((Target.Sskip)).  
  Case Sseq := (fun s1 transl_stmt_s1 s2 transl_stmt_s2 =>                        
    let ts1 := transl_stmt_s1 in
    let ts2 := transl_stmt_s2 in
    (Target.Sseq ts1 ts2)).
  Case Sset := (fun id e =>
    let te := transl_expr e in
    (Target.Sset id te)).
  FEnd transl_stmt.
  
  FEnd Basetransl.

  Family Implight extends Base.
  FEnd Implight.

  Family Imp extends Base.
  FEnd Imp.

  Family Impsharpminor extends Base.
  FEnd Impsharpminor.

  Family Impminor extends Base.
  FEnd Impminor. 

  (* Imp -> Implight *)
  Family SimplExpr extends Basetransl. 
    Family Source extends Imp.
    FEnd Source.
    
    Family Target extends Implight. 
    FEnd Target.
  FEnd SimplExpr.

  (* Implight -> Impsharpminor *)
  Family Impshmgen extends Basetransl. 
    Family Source extends Implight.
    FEnd Source.
    
    Family Target extends Impsharpminor. 
    FEnd Target.
  FEnd Impshmgen.

  (* Impsharpminor -> Impminor *)
  Family Impminorgen extends Basetransl. 
    Family Source extends Impsharpminor.
    FEnd Source.
    
    Family Target extends Impminor. 
    FEnd Target.
  FEnd Impminorgen.
FEnd BaseExt.
