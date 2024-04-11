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
 * Extensible (operational) semantics



### Obervations 

1. We can generalize the correctness property using a star simulation 
   and a measure. i.e all simulation diagrams can have a proof statement 
   of a star simulation equipped with a measure, becuase they star similation 
   diagrams subsume other simulation diagrams (i.e lock-step simulation and 
   plus simulation)

2. Our case study will be informed by the historical example of a verified compiler,
   and show extensiblity by incrementally adding features until we are CompCert-like.
   
   McPainter -----------------------> Imp -----------------------> * -----------------------> CompCert
                Add statements               Add functions                Add Memory Model

3. If there is case in a simulation proof that follows directly from the 
   inductive hypothesis or from other assumptions, then the proof can be inherited 
   from a proof of the identity translation.

4. Determinate and Receptiveness (we have to prove backward simulation using a forward simulation)

5. There seem to be a few CompCert extensions (e.g CompCert JIT, CompCert for secure compilation)
   * In some sense this is a "realistic" extension of CompCert
   * Can our architecture be used to create such extension? 

6. Xavier Leroy seems to be concered about extensible verified code generators for CompCert