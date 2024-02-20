Inductive constant : Type :=
  | Ointconst: int -> constant          (**r integer constant *)
  | Ofloatconst: float -> constant      (**r double-precision floating-point constant *)
  | Osingleconst: float32 -> constant   (**r single-precision floating-point constant *)
  | Olongconst: int64 -> constant.      (**r long integer constant *)

Definition unary_operation : Type := Impminor.unary_operation.
Definition binary_operation : Type := Impminor.binary_operation.

Inductive expr : Type :=
  | Evar : ident -> expr                (**r reading a temporary variable  *)
  | Eaddrof : ident -> expr             (**r taking the address of a variable *)
  | Econst : constant -> expr           (**r constants *)
  | Eunop : unary_operation -> expr -> expr  (**r unary operation *)
  | Ebinop : binary_operation -> expr -> expr -> expr (**r binary operation *)
  | Eload : memory_chunk -> expr -> expr. (**r memory read *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sset : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> external_function -> list expr -> stmt
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
