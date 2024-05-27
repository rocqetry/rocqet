Inductive expr : Type :=
  | Eval (v: val) (ty: type)(* constant *)
  | Evar (x: ident) (ty: type)(* variable *)
  | Efield (l: expr) (f: ident) (ty: type)
  | Evalof (l: expr) (ty: type)(* l-value used as a r-value *)
  | Ederef (r: expr) (ty: type)(* pointer dereference (unary *) *)
  | Eaddrof (l: expr) (ty: type)(* address-of operators (&) *)
  | Eunop (op: unary_operation) (r: expr) (ty: type)
  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
  | Ecast (r: expr) (ty: type)(* type cast (ty)r *)
  | Eseqand (r1 r2: expr) (ty: type)(* sequential "and" r1 && r2 *)
  | Eseqor (r1 r2: expr) (ty: type)(* sequential "or" r1 || r2 *)
  | Econdition (r1 r2 r3: expr) (ty: type)(* conditional r1 ? r2 : r3 *)
  | Esizeof (ty': type) (ty: type)(* size of a type *)
  | Ealignof (ty': type) (ty: type)(* natural alignment of a type *)
  | Eassign (l: expr) (r: expr) (ty: type)(* assignment l = r *)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)
  | Ecomma (r1 r2: expr) (ty: type)(* sequence expression r1, r2 *)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)
  | Ebuiltin (ef: external_function) (tyargs: typelist) (rargs: exprlist) (ty: type)
  | Eloc (b: block) (ofs: ptrofs) (bf: bitfield) (ty: type)
  | Eparen (r: expr) (tycast: type) (ty: type)(* marked subexpression *)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).


Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement(* do nothing *)
  | Sdo : expr -> statement(* evaluate expression for side effects *)
  | Ssequence : statement -> statement -> statement(* sequence *)
  | Sifthenelse : expr -> statement -> statement -> statement(* conditional *)
  | Swhile : expr -> statement -> statement(* while loop *)
  | Sdowhile : expr -> statement -> statement(* do loop *)
  | Sfor: statement -> expr -> statement -> statement -> statement(* for loop *)
  | Sbreak : statement(* break statement *)
  | Scontinue : statement(* continue statement *)
  | Sreturn : option expr -> statement(* return statement *)
  | Sswitch : expr -> labeled_statements -> statement(* switch statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=(* cases of a switch *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Definition fundef := Ctypes.fundef function.

Definition program := Ctypes.program function.

