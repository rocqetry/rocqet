Definition node := positive.

Inductive instruction: Type :=
  | Lop (op: operation) (args: list mreg) (res: mreg)  
  | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
  | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)  
  | Lbranch (s: node)
  | Lcond (cond: condition) (args: list mreg) (s1 s2: node)
  | Ljumptable (arg: mreg) (tbl: list node)
  | Lreturn.

Definition bblock := list instruction.

Definition code: Type := PTree.t bblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
