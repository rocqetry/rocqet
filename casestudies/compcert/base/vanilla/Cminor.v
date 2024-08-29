Inductive constant : Type :=
  | Ointconst: int -> constant(* integer constant *)  
  | Oaddrsymbol: ident -> ptrofs -> constant(* address of the symbol plus the offset *)
  | Oaddrstack: ptrofs -> constant.(* stack pointer plus the given offset *)

Inductive unary_operation : Type :=
  | Ocast8unsigned: unary_operation(* 8-bit zero extension *)
  | Ocast8signed: unary_operation(* 8-bit sign extension *)
  | Ocast16unsigned: unary_operation(* 16-bit zero extension *)
  | Ocast16signed: unary_operation(* 16-bit sign extension *)
  | Onegint: unary_operation(* integer opposite *)
  | Onotint: unary_operation(* bitwise complement *)  
  | Onegl: unary_operation(* long integer opposite *)
  | Onotl: unary_operation(* long bitwise complement *)
  | Ointoflong: unary_operation(* long to int *)
  | Olongofint: unary_operation(* signed int to long *)
  | Olongofintu: unary_operation(* unsigned int to long *)  

Inductive binary_operation : Type :=
  | Oadd: binary_operation(* integer addition *)
  | Osub: binary_operation(* integer subtraction *)
  | Omul: binary_operation(* integer multiplication *)
  | Odiv: binary_operation(* integer signed division *)
  | Odivu: binary_operation(* integer unsigned division *)
  | Omod: binary_operation(* integer signed modulus *)
  | Omodu: binary_operation(* integer unsigned modulus *)
  | Oand: binary_operation(* integer bitwise ``and'' *)
  | Oor: binary_operation(* integer bitwise ``or'' *)
  | Oxor: binary_operation(* integer bitwise ``xor'' *)
  | Oshl: binary_operation(* integer left shift *)
  | Oshr: binary_operation(* integer right signed shift *)
  | Oshru: binary_operation(* integer right unsigned shift *)  
  | Ocmp: comparison -> binary_operation(* integer signed comparison *)
  | Ocmpu: comparison -> binary_operation(* integer unsigned comparison *)  

Inductive expr : Type :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr.  

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt  
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt  
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
