

family Imzero.RTL { 
    Inductive instruction : Type := 
        | Inop: node -> instruction
        | Iop: operation -> list reg -> reg -> node -> instruction        
        | Icond: condition -> list reg -> node -> node -> instruction      
        | Ijumptable: reg -> list node -> instruction        
      
    
    family Semantics { }

}
