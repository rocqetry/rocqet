An extensible certified compiler framework

The high level idea of the casestudy is to show how nested family polymorphism
can be used for extensible certified compilers. We showcase this by developing
families of the Imp certified compiler.

We have the base Imp compiler, which has all the details. We can extend the
base compiler with very small features (e.g Imp w pairs), and then we can
compose all of these small features to create an Imp 2.0 with a lot more
feaures. Note that each of these small features compiler extends the whole
base family of the Imp compiler.

The base Imp compiler has the following compiler pipeline: 
Imp -> Impsharpminor -> Impminor -> ImpminorSel -> RTL -> LTL -> Linear -> Mach -> "native code"

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
