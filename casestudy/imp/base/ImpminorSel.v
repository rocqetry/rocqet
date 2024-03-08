(* Includes Machine-dependent ops *)
Inductive expr : Type :=
  | Evar : ident -> expr
  | Eop : operation -> exprlist -> expr
  | Eload : memory_chunk -> addressing -> exprlist -> expr
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

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: exitexpr -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.
