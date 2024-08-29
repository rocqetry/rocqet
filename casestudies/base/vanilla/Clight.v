Definition label := ident.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr (* integer literal *)
  | Evar: ident -> type -> expr (* variable *)
  | Etempvar: ident -> type -> expr (* temporary variable *)
  | Eunop: unary_operation -> expr -> type -> expr (* unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr(* binary operation *)
  | Ecast: expr -> type -> expr (* type cast ((ty) e) *)

Inductive statement : Type :=
  | Sskip : statement (* do nothing *)
  | Sassign : expr -> expr -> statement (* assignment lvalue = rvalue *)
  | Ssequence : statement -> statement -> statement (* sequence *)
  | Sifthenelse : expr -> statement -> statement -> statement (* conditional *)
  | Sloop: statement -> statement -> statement (* infinite loop *)
  | Sbreak : statement (* break statement *)
  | Scontinue : statement (* continue statement *)
  | Sreturn : option expr -> statement (* return statement *)
  | Sswitch : expr -> labeled_statements -> statement

with labeled_statements : Type := (* cases of a switch *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements. 


(* The C loops are derived forms. *)
Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition fundef := Ctypes.fundef function.

Definition program := Ctypes.program function.
