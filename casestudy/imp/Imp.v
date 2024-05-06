family Base.Imp extends SourceLanguage {
    Inductive expression : Type :=
       | Evar : ident -> expression (* reading a temporary variable *)
       | Econst : constant -> expression (* constants *)       
       | Ebinop : binary_operation -> expression -> expression -> expression (* binary operation *)
      
     Inductive statement : Type :=
        | Sskip: statement
        | Sset : ident -> expr -> statement                
        | Sseq: statement -> statement -> statement
        | Sifthenelse: expr -> statement -> statement -> statement
        | Swhile : expr -> statement -> statement
    
    family Semantics { }    
}
