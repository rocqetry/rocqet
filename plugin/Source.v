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
    Inductive env := ...
    family STLC extends STLCBase { }

    family IL { 
        Definition MyEnv := self(BaseComp).env
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

     family IL { }
     family ILC { }     
}


family STLC { 
    Inductive term = 
      | term_var : string -> term 
      | term_abs : string -> term -> term
      | term_app : term -> term -> term                                        
   
    family Semantics {
      Inductive step : term -> term -> Prop := 
         | step_abs : ...
         | step_var : ...
         | step_app : ...
    }    

    family Correctness {
        FTheorem works_correctly : forall a b, Sementics.step a b ...
    }
}


Module Type STLC_term_ctx. 
End STLC_term_ctx

Module Type STLC_term (self : STLC_term_ctx). 
   ....
End 

Module Type STLC_Semantics_ctx.
  Include STCL_term_ctx.
  Include STLC_term.
End STLC_Semantics_ctx

Module Type STLC_Semantics_step_ctx. 
  Include STCL_term_ctx.
  Include STLC_term.
End STLC_Semantics_step_ctx

Module Type STLC_Semantics_step(self: STCL_Semantics_step_ctx).        
        ...
End STLC_Semantics_step

Module Type STLC_Semantics(self : STLC_Semantics_ctx).
  Module Semantics : Semantics.
     Include STLC_Semantics_step(self).
     
  End Semantics      
End STLC_Semantics.


Module STLC.
    ... 
    
    Module Semantics 
           ...
    End Semantics
  

End STLC


family STLCBool extends STLC {
    Inductive term += 
        | term_if : term -> term -> term -> term 
    
    family Semantics { 
        Inductive step : term -> term -> Prop += 
           | step_if : ...                                               
    }

    family Correctness {
        
    }
}


(* Compilation *)
