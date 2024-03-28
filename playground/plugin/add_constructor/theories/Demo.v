From Add_constructor Require Import Loader.

Inductive term : Type := 
  | Var 
  | Abs 
  | App.


AddConstructor asdf Str.

Is 1 2 nonempty.

What is 1 2 a list of.

Intern term.
Intern (fun x => x).
Intern (Type : Type).
Intern _.

MyDefine name := term.

MyPrint name.

Check1 (1 = 23).

Convertible (1 + 1) 2.

Check1 (Type : Type).

Convertible Type Prop.

Convertible 1 2.

Accept 23 34 3.

Is Everything Awesome.

Count. 

Count.
