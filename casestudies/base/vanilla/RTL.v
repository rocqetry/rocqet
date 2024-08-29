Definition node := positive.

Inductive instruction: Type :=
  | Inop: node -> instruction      
  | Iop: operation -> list reg -> reg -> node -> instruction  
  | Icond: condition -> list reg -> node -> node -> instruction      
  | Ijumptable: reg -> list node -> instruction      
  | Ireturn: option reg -> instruction.      

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
