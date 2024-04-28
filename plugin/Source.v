family BaseComp { 
    family STLC { 
        Inductive Ty := TyUnit | TNat | TArr (t1 t2 : Ty)        
        Inductive Exp := EVal (v : Val) | EApp(e1 e2 : Exp)
        with Val := Unit | Var (x : string) | Lam (x : string) (e : Exp)

        Definition eval : Exp -> option Val := ...
    }

    family IL { 
        Inductive Ty := ...
        Inductive Val := ... 
        Inductive Exp := ...
    }
    family ILC extends IL { 
        Inductive Fun := ...
    }
    family ILK extends IL { }

    Definition cps_val : STLC.Exp -> ILK.Exp
    Definition cc_val : ILK.Exp -> ILC.Fun * ILC.Exp
}

family IfExt extends BaseComp {
     family STLC { }

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
