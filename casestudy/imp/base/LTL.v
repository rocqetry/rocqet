Definition node := positive.

Inductive instruction: Type :=
  | Lop (op: operation) (args: list mreg) (res: mreg)
  | Lload (chunk: memory_chunk) (addr: addressing) (args: list mreg) (dst: mreg)
  | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
  | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)
  | Lstore (chunk: memory_chunk) (addr: addressing) (args: list mreg) (src: mreg)
  | Lcall (sg: signature) (ros: mreg + ident)
  | Ltailcall (sg: signature) (ros: mreg + ident)
  | Lbuiltin (ef: external_function) (args: list (builtin_arg loc)) (res: builtin_res mreg)
  | Lbranch (s: node)
  | Lcond (cond: condition) (args: list mreg) (s1 s2: node)
  | Ljumptable (arg: mreg) (tbl: list node)
  | Lreturn.
