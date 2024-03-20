family Impzero.Asm {  
  (* This is a parameter *)  
  family Op extends {
      Inductive operation := ...

      Inductive condition := ...
  }
}

family Impzero.ImppminorSel extends Impfrontend {         
  Inductive expression : Type +=
    | Eop : Asm.Op.operation -> exprlist -> expression                        
    | Econdition : condexpr -> expr -> expr -> expr
    | Elet : expr -> expr -> expr
    | Eletvar : nat -> expr

  with exprlist : Type :=
   | Enil: exprlist
   | Econs: expr -> exprlist -> exprlist
                                 
  with condexpr : Type :=
    | CEcond : Asm.Op.condition -> exprlist -> condexpr
    | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
    | CElet: expression -> condexpr -> condexpr.


  Inductive exitexpr : Type :=
     | XEexit: nat -> exitexpr
     | XEjumptable: expr -> list nat -> exitexpr
     | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
     | XElet: expr -> exitexpr -> exitexpr

  (* Overriding some constructors here *)
  Inductive statement : Type +=
     | Sswitch: exitexpr -> statement
     | Sifthenelse: condexpr -> statement -> statement -> statement
                              
  family Semantics {
    Inductive eval_expr: letenv -> expr -> val -> Prop := ...

    with eval_exprlist: letenv -> exprlist -> list val -> Prop := ...

    with eval_condexpr: letenv -> condexpr -> bool -> Prop :=  ...

    Inductive eval_exitexpr: letenv -> exitexpr -> nat -> Prop := ...

    Inductive step: state -> trace -> state -> Prop := ...
  }
}

(* Instruction Selection *)
(* Translation from Impminor -> ImpminorSel *)
family Impzero.ImpSelection extends ImpfrontendTransform {
  family Source extends Impminor { }
  family Target extends ImpminorSel { }

  family Proofs {
    Inductive match_cont := ...

    Theorem translate_program_correct: forall prog tprog,
        forward_simulation (Source.semantics prog) (Target.semantics tprog).
    Proof.
      ...
    Qed.
  }
}
