family ProbCompCert extends ImpCompCert { }

(* I have ImpCompCert developed. I want to creates ProbCompCert. 
   As a proof engineer, what do I need to do? 

   * I need to somehow change the structure of the passes
   * I need to define the new syntax and semantics 
*)

family ProbCompCert.Base.Stan extends Base.SourceLanguage { 
  Inductive expression += 
    | Earray: list expr -> expr
    | Erow: list expr -> expr
    | Eindexed: expr -> list index -> expr
    (* Probabilistic expressions *)
    | Edist: identifier -> list expr -> expr
    | Etarget
    ...

  Inductive statement += 
     | Sforeach: identifier -> expr -> statement -> statement
     (* Probabilistic statements *)
     | Starget: expr -> statement
     | Stilde: expr -> identifier -> list expr -> (option expr * option expr) -> statement.
    
  family Semantics { } 

}

family ProbCompCert.Base.Stanlight extends Base.SourceLanguage { }

family ProbCompCert.Base.Stan extends Base.Implight { }

