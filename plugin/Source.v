family STLCBase { 
    Inductive Ty := TyUnit | TNat | TArr (t1 t2 : Ty)        
    Inductive Exp := EVal (v : Val) | EApp(e1 e2 : Exp)
    with Val := Unit | Var (x : string) | Lam (x : string) (e : Exp)
}

family STLCIf extends STLCBase { 
    Inductive Ty += TBool
    Inductive Val += EIf (e e1 e2 : Exp)              
}

family BaseComp {
    family STLC extends STLCBase { }

    family IL {        
        Inductive Ty := TUnit | TCont (ts : list Ty)
        Inductive Val := Unit | Var (x : string)
        Inductive Exp := 
          | ELet (x : string) (v : Val) (e : Exp)
          | EApp (v : Val) (vs : list Val) 
          | EHalt (v : Val)
    }

    family ILK extends IL { 
        Inductive Val += Lam (x : list string) (e : Exp)
    }

    family ILC extends IL { 
        Inductive Ty += TVar (s : string) | TExist (x : string) (t : Ty)
        Inductive Val += Pack (t : Ty) (v : Val) | Name (n : string)
        Inductive Exp += EUnpack(a : string) (x : string) (v : Val) (e : Exp)        
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
(* Compilation *)
