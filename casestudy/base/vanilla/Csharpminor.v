Inductive constant : Type :=
  | Ointconst: int -> constant (* integer constant *) 

Definition unary_operation : Type := Cminor.unary_operation.
Definition binary_operation : Type := Cminor.binary_operation.

Inductive expr : Type :=
  | Evar : ident -> expr(* reading a temporary variable *)  
  | Econst : constant -> expr(* constants *)
  | Eunop : unary_operation -> expr -> expr(* unary operation *)
  | Ebinop : binary_operation -> expr -> expr -> expr(* binary operation *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sset : ident -> expr -> stmt    
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt    
  | Sswitch: bool -> expr -> lbl_stmt -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt

with lbl_stmt : Type :=
  | LSnil: lbl_stmt
  | LScons: option Z -> stmt -> lbl_stmt -> lbl_stmt.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list (ident * Z);
  fn_temps: list ident;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.

Definition program : Type := AST.program fundef unit.
  
