Definition label := positive.

Inductive instruction: Type :=
  | Mgetstack: ptrofs -> typ -> mreg -> instruction
  | Msetstack: mreg -> ptrofs -> typ -> instruction
  | Mgetparam: ptrofs -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Mtailcall: signature -> mreg + ident -> instruction
  | Mbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mjumptable: mreg -> list label -> instruction
  | Mreturn: instruction.

Definition code := list instruction.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: ptrofs;
    fn_retaddr_ofs: ptrofs }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
