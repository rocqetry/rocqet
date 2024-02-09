Family of Imp

A single Imp family will have:

  IRs: 
  1. Stack based IR
  2. RTL (or an SSA form)
  3. LTL (after register allocation)
  4. Mach (high level machine code)

  Optimization passes:
  1. DCE
  2. Constant folding/propagations


Each family will add a feature to Imp and extend each IR and
inherit from the base Imp compiler.

Families include:
1. Imp with denotational semantics (this can also be an alternate
   base family)
2. Imp with functions and function calls 
3. 
