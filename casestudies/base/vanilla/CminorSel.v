Inductive expr : Type :=
  | Evar : ident -> expr
  | Eop : operation -> exprlist -> expr  
  | Econdition : condexpr -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr  

with exprlist : Type :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist

with condexpr : Type :=
  | CEcond : condition -> exprlist -> condexpr
  | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
  | CElet: expr -> condexpr -> condexpr.

Inductive exitexpr : Type :=
  | XEexit: nat -> exitexpr
  | XEjumptable: expr -> list nat -> exitexpr
  | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
  | XElet: expr -> exitexpr -> exitexpr.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt  
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: exitexpr -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.


