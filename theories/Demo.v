From NFPOP Require Import Loader.

Family Meta.
   MetaData _b.
       Definition add (x : nat) := x.
   FEnd _b.
   
   FDefinition b := self__Meta.add.

   MetaData _x. 
       Definition y := self__Meta.b.
   FEnd _x.
FEnd Meta.

Print Meta.

Notation ident := nat.

Family T.
  FDefinition b : nat := 0.
FEnd T.

Family IR.
   FInductive constant : Type :=
      | Ointconst: nat -> constant.
    
    FInductive unary_operation : Type := Negation : unary_operation.

    FInductive binary_operation : Type :=
        | Binplus : binary_operation
        | Binminus : binary_operation
        | Binmult : binary_operation.

    FInductive expr : Type :=
        | Evar : ident -> expr
        | Econst : constant -> expr
        | Eunop : unary_operation -> expr -> expr
        | Ebinop : binary_operation -> expr -> expr -> expr.
      
   Family Semantics. 
      FInductive state : Type := State : state | CallState : state | ReturnState : state.
      FInductive step : state -> state -> Type :=
        | step_assign : step State State
        | step_skip : step State State.
   FEnd Semantics.
FEnd IR.

Family RTL extends IR.
   Family Semantics.     
      FInductive step : state -> state -> Type :=
        | step_store : step State State.
   FEnd Semantics.
FEnd RTL.

Family Translation.
   Family Source extends IR.
   FEnd Source.

   Family Target extends IR.
   FEnd Target.
FEnd Translation.

Family ConstFold extends Translation.
    Family Source extends RTL.
        Family Semantics. 
           FInductive step : state -> state -> Type :=
                | step_load : step State State.           
        FEnd Semantics.                
    FEnd Source.
FEnd ConstFold.

(* Precedence of further binding? *)
Check ConstFold.Source.Semantics.step_store.

(* Further binding + Inheritance *)
Family IfExt.
   Family Base.
       FInductive value : Type := tt : value | ff : value.
   FEnd Base.
   
   Family Derived extends Base.
   FEnd Derived.
FEnd IfExt.

Family Random. 
FEnd Random. 

Family Try extends IfExt. 
   Family Base.
      FInductive value : Type :=  nothing : value.

      FInductive usevalue : Type := user : value -> usevalue.
   FEnd Base.

   (* Family Derived extends Random.
   FEnd Derived.*)
FEnd Try.

Check Try.Derived.nothing.
Check Try.Derived.usevalue.



Family A.
   Family B.
      FInductive value : Type := tt : value | ff : value.
      FInductive expr : Type := val : value -> expr.
   FEnd B.
FEnd A.

Family A1 extends A.
    Family B. 
       FInductive value : Type := clo : value -> value.
    FEnd B.
FEnd A1.


Family A0.
  Family B. 
     Family C.
        FInductive N : Set := Zero : N | Succ : N -> N.
     FEnd C.
  FEnd B.
FEnd A0.

Family A10.
   FInductive N : Set := Zero : N | Succ : N -> N.
   FInductive B : Set := TT : B | FF : B | Haha : N -> B.
   Family A1.
      FInductive basic : Set := car : basic.

      Family A2.
           FInductive step : Set := exec_assign : N -> step
           with person : Set := Faya : person.
           Family A3.
              FInductive eval_expr : Set :=
                | eval_unop : basic -> step -> eval_expr.
           FEnd A3.
      FEnd A2.      
   FEnd A1.

   FInductive work : Set :=
     | home : A1.A2.A3.eval_expr -> work
     | school : A1.basic -> work.
FEnd A10.

Family B10 extends A10.
   FInductive N : Set := extraN : N.
   FInductive B : Set := extraB : N -> B.
   
   Family A1.
     FInductive basic : Set := extraBasic : B -> basic.
     Family A2. 
     FEnd A2.
   FEnd A1.   
FEnd B10.

Check B10.A1.A2.A3.eval_expr.
Check B10.extraN. 
    
Family Semantics.   
   FInductive basic : Set := car : basic.

    FInductive step : Set :=
     | exec_skip : step
    with person : Set := GG : person.     

   FInductive eval_expr : Set := eval_binary : basic -> eval_expr | eval_const : eval_expr.

   FInductive call_state : Set := CallState : call_state.

   FInductive work : Set := home : work | school : work.
FEnd Semantics.

 Family BSemantics extends Semantics.
    FInductive step : Set := exec_assign : basic -> step
      with person : Set := Faya : person.

   FInductive eval_expr : Set := lahexpr : eval_expr.
   
   FInductive call_state : Set := ReturnState : eval_expr -> call_state.       
FEnd BSemantics.

Family D extends BSemantics.

FInductive eval_expr : Set := eval_ifthenelse : eval_expr.
   
FEnd D.

Family F extends D.
FEnd F.
