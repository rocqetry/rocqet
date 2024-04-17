# A Proof Language for Scalable Extensibility in Verified Compilers

## Scalable Extensibility

The term _scalable extensibility_ in software engineering means that an
extension to a piece of code should require addition of code which is 
proportional to the size of the extension. In the content of proof 
engineering, scalable extensibility means that in addition to the size 
of the code being added to implement a new feature, the proof of correctness
of said feature should be proportional in size to the change. 

Compilers are the hallmark of software complexity. Even more so, verified 
compilers. Compilers are usually structured in _passes_ which modify a 
few nodes of the abstract syntax tree. The proof for a compiler pass is 
usually structured as a simulation proof. Basically, given the translation 
from a source language S to a target language T, if we have a semantics 
for S and a semantics for T, then a simulation proof ensures that each step 
that the source program can takes is matched by one or more steps in the 
target program. A simulation proof is usually an induction on the derivation 
of the execution of the source program. Extesnsibility can be achived from a 
key observation about compiler intermediate representations (IR). The IRs 
which are relatively close in the compiler pipeline have similar features. 
This means that they share a large portion of their syntax and semantics. 





## A Family of Extensible Verified Compilers
This example shows how to develop an extensible certified compiler using 
a proof language equipped with nested family polymorphism. This example 
shows how we incrementally add features to the first verified compiler by 
McCarthy, and scale it up to a toy language like Imp and eventually to a 
realistic compiler with a CompCert-like architecture.


### Extensible Simulation Diagrams

 * Extensible matching state relations 
 * Extensible IR 
 * Extensible operational semantics

### Observations / Ideas

1. We can generalize the correctness property using a star simulation 
   and a measure. i.e all simulation diagrams can have a proof statement 
   of a star simulation equipped with a measure, becuase star similation 
   diagrams _subsume_ other simulation diagrams (i.e lock-step simulation and 
   plus simulation)

2. Our case study will be informed by the historical example of a verified 
   compiler, from John McCarthy and James Painter (the McPain compiler), 
   and show extensiblity by incrementally adding features until the resulting 
   compiler is CompCert-like:

```
   McPain -----------------------> Imp -----------------------> * -----------------------> CompCert
             Add statements               Add functions                Add memory model
```

3. If there is case in a simulation proof that follows directly from the 
   inductive hypothesis or from other assumptions, then the proof of 
   such a case can be inherited from a proof of the identity translation.

4. Determinate-ness and Receptive-ness (we have to prove backward simulation using
    a forward simulation)
    * Can the proofs be reused somehow? 

5. There seem to be a few CompCert extensions
     * In some sense, these are "realistic" extensions of CompCert
     * Can our language design/case study architecture enable 
       such extensions?

     #### Extension of CompCert
     * CompCert used in a JIT [1, 15]
     * CompCert for Cryptographic Constant-Time Preservation [2]
     * CompCertTSO - CompCert for a relaxed memory model [3]
     * ProbCompCert - CompCert for PPL [4]
     * L2C - CompCert extension for a Lustre-like language [5]
     * Velus - Compcert extension for Lustre [6]
     * Vericert - CompCert for high-level synthesis [7]
     * CompCertSSA - CompCert with SSA [8]
     * CompCertO - CompCert for composing certified components [9]
     * CompCertKVX - CompCert with a KVX backend [10]
     * Stack-Aware CompCert - Composes several CompCert extensions 
       and compiles to machine code [11]
     * Compositional CompCert - CompCert for separate compilation [12]
     * CompCertS - CompCert with a richer semantics for pointer arithmetic [13]
     * Quantitative CompCert - CompCert for preserving quantitative 
       properties [14]
     * SepCompCert - CompCert for lightweight verification of separate 
       compilation [16]
     * CompCert SIMD - CompCert with x86 SIMD instructions [17]
     
     [1]: https://dl.acm.org/doi/abs/10.1145/3571202
     [2]: https://dl.acm.org/doi/10.1145/3371075
     [3]: https://dl.acm.org/doi/10.1145/1925844.1926393
     [4]: https://dl.acm.org/doi/abs/10.1145/3591245
     [5]: https://github.com/l2ctsinghua/l2c
     [6]: https://github.com/INRIA/velus
     [7]: https://dl.acm.org/doi/10.1145/3485494
     [8]: https://dl.acm.org/doi/10.1145/2579080
     [9]: https://dl.acm.org/doi/abs/10.1145/3453483.3454097
     [10]: https://certicompil.gricad-pages.univ-grenoble-alpes.fr/compcert-kvx/
     [11]: https://dl.acm.org/doi/10.1145/3290375
     [12]: https://dl.acm.org/doi/10.1145/2775051.2676985
     [13]: https://link.springer.com/chapter/10.1007/978-3-319-66107-0_6
     [14]: https://dl.acm.org/doi/10.1145/2594291.2594301
     [15]: https://dl.acm.org/doi/10.1145/3434327
     [16]: https://dl.acm.org/doi/10.1145/2837614.2837642
     [17]: https://github.com/haslab/ccomp-simd

6. Xavier Leroy seems to be concered about extensible verified code generators
   for CompCert

7. "Advice on structuring compilers and proving them correct" [20]
    * This paper seems to have the first proof architecture of something that 
      resembles a simulation diagram
    
    + Also interesting that it was published at the first ever POPL

    [20]: https://dl.acm.org/doi/10.1145/512927.512941