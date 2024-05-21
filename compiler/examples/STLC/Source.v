family STLCBase { 
    Inductive Ty := TyUnit | TNat | TArr (t1 t2 : Ty)        
    Inductive Exp := EVal (v : Val) | EApp(e1 e2 : Exp)
    with Val := Unit | Var (x : string) | Lam (x : string) (e : Exp)
}

family STLCIf extends STLCBase { 
    Inductive Ty += TBool
    Inductive Val += VTrue | VFalse
    Inductive Exp += EIf (e e1 e2 : Exp) 
}


family BaseComp {
    family STLC extends STLCBase { }
    
    Definition Ident := nat

    family IL {
        Inductive Ty := TUnit | TCont (ts : list Ty)
        Inductive Val := Unit | Var (x : Ident)
        Inductive Exp := 
          | ELet (x : Ident) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
    }

    family ILK extends IL { 
        Inductive Val += Lam (x : list Ident) (e : Exp)
    }

    family ILC extends IL { 
        Inductive Ty += TVar (s : Ident) | TExist (x : Ident) (t : Ty)
        Inductive Val += Pack (t : Ty) (v : Val) | Name (n : Ident)
        Inductive Exp += EUnpack(a : string) (x : Ident) (v : Val) (e : Exp)        
    }
}

family IfExt extends BaseComp {
     family STLC extends STLCIf { }

     family IL { 
       Inductive Ty += TBool
       Inductive Val += Bool (b : bool)
       Inductive Exp += EIf (v : Val) (e1 e2 : Exp)
     }     
}
