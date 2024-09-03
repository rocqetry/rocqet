From NFPOP Require Import Loader.


Family IR.
   FInductive constant : Type :=
      | Ointconst: (* int ->*) constant 
      | Ofloatconst: (*float ->*) constant 
      | Osingleconst: (*float32 ->*) constant
      | Olongconst: (* int64 ->*) constant.

   FDefinition ident := nat.   
   
   FDefinition label := ident.

   FInductive expr : Type :=
      | Evar : ident -> expr 
      | Econst : constant -> expr. 
   
   FInductive stmt : Type :=
      | Sskip : stmt
      | Sset : ident -> expr -> stmt
      | Ssequence : stmt -> stmt -> stmt
      | Sifthenelse : expr -> stmt -> stmt -> stmt
      | Sloop: stmt -> stmt -> stmt 
      | Sbreak : stmt
      | Scontinue : stmt
      | Sreturn : option expr -> stmt. 


   FInductive cont: Type :=
      | Kstop: cont
      | Kseq: stmt -> cont -> cont
      | Kblock: cont -> cont.   

   FRecursion call_cont about cont motive (fun (c : cont) => cont) by _rect.           
      Case Kstop := Kstop.
      Case Kseq := ( fun s k call_cont_k => call_cont_k).
      Case Kblock := (fun c call_cont_k => call_cont_k).
   FEnd call_cont.
            
   FRecursion is_call_cont about cont motive (fun (_ : cont) => Prop) by _rect.
        Case Kstop := True.                   
        Case Kseq := (fun s c call_cont_c => False).
        Case Kblock := (fun c call_cont_c => False).
   FEnd is_call_cont.
FEnd IR.

Family A extends IR.
FEnd A.

Family B extends IR.
   FInductive cont: Type :=
      | Knothing: cont.

   FRecursion call_cont.
      Case Knothing := Kstop.
   FEnd call_cont.
   
   FRecursion is_call_cont.
       Case Knothing := True.
   FEnd is_call_cont.   
FEnd B.

Family C extends B.
FEnd C.
