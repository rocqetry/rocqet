
family Impzero.LTL extends Impbackend {
    
    Inductive instruction: Type :=
       | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
       | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)       
       | Lop (op: operation) (args: list mreg) (res: mreg)       
       | Lbranch (s: node)
       | Lcond (cond: condition) (args: list mreg) (s1 s2: node)
       | Ljumptable (arg: mreg) (tbl: list node)

    family Semantics { }
      
}


