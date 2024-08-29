Definition label := positive.

Inductive instruction: Type :=
  | Lgetstack: slot -> Z -> typ -> mreg -> instruction
  | Lsetstack: mreg -> slot -> Z -> typ -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction  
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Ljumptable: mreg -> list label -> instruction
  | Lreturn: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
