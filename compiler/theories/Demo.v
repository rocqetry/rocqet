From NFPOP Require Import Loader.

Notation ident := nat.

Family A.
   Family B.
      FInductive value : Type := tt : value | ff : value.
      FInductive expr : Type := val : self__B.value -> expr.
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
   FInductive B : Set := TT : B | FF : B | Haha : self__A10.N -> B.
   Family A1.
      FInductive basic : Set := car : basic.

      Family A2.
           FInductive step : Set := exec_assign : self__A10.N -> step
           with person : Set := Faya : person.
           Family A3.
              FInductive eval_expr : Set :=
                | eval_unop : self__A1.basic -> self__A2.step -> eval_expr.
           FEnd A3.
      FEnd A2.      
   FEnd A1.

   FInductive work : Set :=
     | home : self__A10.A1.A2.A3.eval_expr -> work
     | school : self__A10.A1.basic -> work.
FEnd A10.

Family B10 extends A10.
   FInductive N : Set := extraN : N.
   FInductive B : Set := extraB : self__B10.N -> B.
   
   Family A1.
     FInductive basic : Set := extraBasic : self__B10.B -> basic.
     Family A2. FEnd A2.
   FEnd A1.   
FEnd B10.

Check B10.A1.A2.A3.eval_expr.
Check B10.extraN. 
    
Family Semantics.   
   FInductive basic : Set := car : basic.

    FInductive step : Set :=
     | exec_skip : step
    with person : Set := GG : person.     

   FInductive eval_expr : Set := eval_binary : self__Semantics.basic -> eval_expr | eval_const : eval_expr.

   FInductive call_state : Set := CallState : call_state.

   FInductive work : Set := home : work | school : work.
FEnd Semantics.

 Family BSemantics extends Semantics.
    FInductive step : Set := exec_assign : self__BSemantics.basic -> step
      with person : Set := Faya : person.

   FInductive eval_expr : Set := lahexpr : eval_expr.
   
   FInductive call_state : Set := ReturnState : self__BSemantics.eval_expr -> call_state.       
FEnd BSemantics.

Family D extends BSemantics.

FInductive eval_expr : Set := eval_ifthenelse : eval_expr.
   
FEnd D.

Family F extends D.
FEnd F.
