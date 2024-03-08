Family of Imp

Each folder represents an Imp compiler which will be in the family hierarchy.

Compilation pipleline:
Imp -> Impsharpminor -> Impminor -> ImpminorSel -> RTL -> LTL -> Linear -> Mach -> aarch64

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
