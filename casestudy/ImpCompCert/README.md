An extensible certified compiler framework

The high level idea of the casestudy is to show how nested family polymorphism
can be used for extensible certified compilers. We showcase this by developing
families of the Imp certified compiler.

We have the base Imp compiler, which has all the details. We can extend the
base compiler with very small features (e.g Imp with pairs), and then we can
compose all of these small features to create an Imp 2.0 with a lot more
feaures. Note that each of these small features compiler extends the whole
base family of the Imp compiler.

Compiler pipeline:
Imp -> Implight -> Impshpminor -> Impminor -> ImpminorSel -> RTL -> LTL -> Linear -> Mach -> Asm

Ideas list for families:
1. Imp with functions, local, & function calls
2. Imp with pointers and memory-related operations
3. Imp with more control flow operators (e.g break, continue)
3. Imp with C-style arrays
4. Imp with C-style structs (this is basically "pairs")
5. Imp with more primitives (e.g float32, float64)
6. Imp with a different semantics style (e.g denotational semantics with itrees)

*aarch64: A tiny subset of aarch64