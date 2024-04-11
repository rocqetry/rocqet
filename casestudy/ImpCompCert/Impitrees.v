(* Experimenting Imp with itrees-style semantics *)
(* https://github.com/DeepSpec/InteractionTrees/tree/1569790e28bb5d88381f0763298418d6ccc52eb9/tutorial/Imp.v *)

family Impitrees extends Impzero { }

family Impitrees.Impfrontend {
   family Semantics *overrides* {
      (* We want to change the semantics entirely *)
      
      Context {eff : Type -> Type}.
      Context {HasImpState : ImpState -< eff}.  
    
      Fixpoint denote_expr (e : expr) : itree eff value :=
        match e with
        | Var v     => trigger (GetVar v)
        | Lit n     => ret n
        | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)
        | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
        | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
        end.
        
        Fixpoint denote_imp (s : stmt) : itree eff unit :=
             match s with
             | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v)
             | Seq a b    =>  denote_imp a ;; denote_imp b
             | If i t e   =>
               v <- denote_expr i ;;
               if is_true v then denote_imp t else denote_imp e
         
             | While t b =>
               while (v <- denote_expr t ;;
         	           if is_true v
                      then denote_imp b ;; ret (inl tt)
                      else ret (inr tt))
         
             | Skip => ret tt
             end.
    }

    Holes family self.super { }
    Holes family self { }
}

(* This prints the things that are broken becuase of the change just made to a family *)
Holes family Impitrees { }

(* 
Q: In this case, what is broken? 
1. Simulation proofs 
2. The "Semantics" nested family in all IR families 

Q: What is breaks but seems like should be reuseable (i.e not broken)?

Q: How can we display this in an intuitive way? 

Q: How does this list change once we start filling things up 
   in a family with a higher hierarchy? (e.g in Impfrontend)

Q: What happens when you try to form a mixin with `Impitrees` and 
   a family from the classic `Impzero` hierarchy? 
*)

family Impitrees.Impshmgen *overrides* { }

family Impitrees.Impshmgen.CorrectnessProofs {
    Lemma compile_expr_correct : forall {E} e s ts l n,
      Renv g_imp g_asm ->
      @eutt E _ _ (sim_rel l n)
            (Source.interp (denote_expr e) s)
            (Target.interp (denote_list (compile_expr n e)) ts l).
    Proof. 
      ...
    Qed. 

    Theorem compile_correct {E} {HasExit : Exit -< E} (s : statement) :
      equivalent (E := E) s (compile s).
    Proof.
      ...
    Qed.
}

family Impitrees.Impfrontend {
    family Semantics {
        Fixpoint denote_unary (op : unary_operation) (e : expression) : itree eff Values.value := ...
        Fixpoint denote_binary (op : binary_operation) 
                               (a : expression) (b : expression)
                                 : itree eff Values.value := ... 
        match op with 
        | Binplus => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r) 
        ...
        end.
        Fixpoint denote_expression (e : expression) : itree eff Values.value :=
           match e with
           | Evar v     => trigger (GetVar v)
           | Econst n     => ret n
           | Eunop op n => denote_unary op n 
           | Ebinop op a b => denote_binary op a b           
           end.
        
         Definition loop (step : itree eff (unit + unit)) : itree eff unit :=
            iter (C := Kleisli (itree eff)) (fun _ => step) tt.
       
        Fixpoint denote_statement (s : statement) : itree eff unit := 
          match s with 
          | Sassign x e =>  v <- denote_expression e ;; trigger (SetVar x v) 
          | Sseq a b =>  denote_imp a ;; denote_imp b
          | Sifthenelsle i t e   =>
               v <- denote_expr i ;;
               if is_true v then denote_imp t else denote_imp e
          (* | Sloop s => loop ( result <- denote_stateme b ;; ret (inl result)) *)
          | Sskip s => ...
          | Ssblock s => denote_statement s                              
          end.        
    }
}

family Impitrees.Imptransformfrontend {
    family Source extends Impfrontend { }
    family Target extends Impfrontend { }
    
    family CorrectnessProof {
        Lemma compile_expr_correct : forall {E} e s ts l n,
           Renv g_imp g_asm ->
           @eutt E _ _ (sim_rel l n)
                 (Source.interp (denote_expr e) s)
                 (Target.interp (denote_list (compile_expr n e)) ts l).
         Proof. 
           ...
         Qed. 

        Theorem compile_correct {E} {HasExit : Exit -< E} (s : statement) :
          equivalent (E := E) s (compile s).
        Proof.
            induction s. 
            Case Sassign := ...
            Case Sseq := ...
            Case Sifthenelse := ...
            Case Sskip := ...
            Case Sblock := ...
            Case Sexit := ...
        Qed.
    }
}

(* The frontend languges different forms of switch statements *)

family Impitrees.Implight.Semantics {    
   Fixpoint denote_statement (s : statement) : itree eff unit := 
      match s with 
      | Sswitch ... => ...
}

family Impitrees.Impsharpminor.Semantics { 
  Fixpoint denote_statement (s : statement) : itree eff unit := 
      match s with 
      | Sswitch ... => ...
}

family Impitrees.Impshmgen { 
  family Source extends Implight { }
  family Target extends Impsharpminor { }
  
  (* This transformation simplifies implight switch statements *)
  Fixpoint compile (s : Source.statement) : Target.statement =       
      | Sswitch ... => ...

  family CorrectnessProof {
      Theorem compile_correct {E} {HasExit : Exit -< E} (s : statement) :
          equivalent (E := E) s (compile s).
       Proof.
         Case Sswitch := ...
       Qed.
  }                      
}

family Impitrees.Imppminor.Semantics { 
    Fixpoint denote_statement (s : statement) : itree eff unit := 
      match s with 
      | Sswitch ... => ...
}

family Impitrees.Impminorgen { 
  family Source extends Impsharpminor { }
  family Target extends Impminor { }
    
  Fixpoint compile (s : Source.statement) : Target.statement =       
      | Sswitch ... => ...

  family CorrectnessProof {
      Theorem compile_correct {E} {HasExit : Exit -< E} (s : statement) :
          equivalent (E := E) s (compile s).
       Proof.
         Case Sswitch := ...
       Qed.
  }                      
}

(* Add some machine dependent operation *)
family Impitrees.Impminorsel.Semantics {
    (* New kinds of expressions *)
    Fixpoint denote_expression (e : expression) : itree eff Values.value :=
       match e with
       | Econdition ... => ...
       | Elet ... => ...
       | Eletvar ... => ...
       end.

    Fixpoint denote_exitexpr (s : exitexpr) : itree eff unit := ...

    Fixpoint denote_condexpr (s : exitexpr) : itree eff unit := ...                                                                
    
    Fixpoint denote_statement (s : statement) : itree eff unit := 
      match s with 
      | Sswitch ... => ...
}

family Impitrees.Impselection { 
  family Source extends Impsharpminor { }
  family Target extends Impminor { }
    
  Fixpoint compile (s : Source.statement) : Target.statement =       
      | Sswitch ... => ...

  family CorrectnessProof {
      Theorem compile_correct {E} {HasExit : Exit -< E} (s : statement) :
          equivalent (E := E) s (compile s).
       Proof.
         Case Sswitch := ...
       Qed.
  }                      
}
