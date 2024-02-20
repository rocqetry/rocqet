Family of Imp

Each folder represents an Imp compiler which will be in the family hierarchy.

Compilation pipleline:
Imp -> Impsharpminor -> Impminor -> ImpminorSel -> RTL -> LTL -> Linear -> Mach -> aarch64

Q:
1. What pass is LTLin???
2. Is this compilation pipeline too long?
3. Type checking for the imp source language?
4. Would it make sense to use a diffing algorithm to check the
   difference between two inductive type in different families,
   but representing the same "thing."


Optimization passes:
1. DCE
2. Constant folding/propagations

Each family will add a feature to Imp and extend each IR and
inherit from the base Imp compiler.

Families include:
1. Imp with local variable & functions and function calls
2. Imp with pointers
3. Imp with arrays
4. Imp with C types: structs, enums,
5. Imp with more primitives (e.g float32 float64)
