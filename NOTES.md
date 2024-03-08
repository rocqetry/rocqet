

1. Create the data pipeline for the compiler architecture
   The pipeline is similar to the pipeline in CompCert.
   We compile to Cminor (ImpMinor) -> CSel (ImpSel) -> RTL (ImpRTL) -> LTL (ImpLTL)
   We can create all the inductive types and figure out how reuse with nested family
   polymorphism will work.
2. We want to have a syntax-directed algorithm (like [| e |]) for compiling nested
   family polymorphism to vanilla Coq terms/modules. The problem is that we might
   need to prove that this algorithm is correct... or we can say "This is just a
   demonstration of the algorithm" - I'd personally prefer if we could prove this.
   In some sense, proving this algorithm would be the equivalent of writing the
   implementation in MetaCoq and proving the actual compilation algorithm correct.
3. I think the processor-dependent style of types can be a good room to show case
   family polymorphism. Because in some sense that is a kind of reuse/abstraction? 

Q: 
1. What happens when two families are not too far part from each other?
   Does it make sense to still include them in them like that? 


Language design:
1. It might be a goood idea to be able to override a field name in a derived family 