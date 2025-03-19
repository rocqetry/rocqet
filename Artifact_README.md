# [PLDI'25 Artifact] Certified Compilers à la Carte

## Platform requirements

We recommend a Linux or macOS system.

## Getting Started Guide

Our artifact depends on OCaml 5.1, Rocq 8.19, and the Flocq Rocq library.
We provide a [Nix](https://nixos.org/) shell with all these dependencies present in it. You can 
also install these dependencies using [opam](https://opam.ocaml.org/).

### Installation 

#### Using Nix (recommended)
We provide all dependencies to evaluate our artifact inside a Nix environment.

This environment includes an OCaml 5.1 distribution, a Rocq 8.19 distribution 
(compiled with OCaml 5.1), Emacs (terminal) with Proof General installed, 
and the Flocq Rocq library.

First install Nix:
```
sh <(curl -L https://nixos.org/nix/install) --daemon
```

Please refer to https://nixos.org/download for more info.

To enter a  Nix shell use
```
nix --experimental-features 'nix-command flakes' develop -i
```


#### Using Opam
If you are a seasoned OCaml/Rocq user, and you don't want to use the Nix shell, 
then you can create a new opam switch with the following dependencies for Rocqet: 

1. OCaml 5.1
2. Rocq 8.19
3. Dune
4. Flocq (see https://flocq.gitlabpages.inria.fr/)


You will also need to create a *separate* opam switch for FPOP with the following dependencies: 

1. OCaml 4.13.1
2. Rocq 8.15.0
3. Dune

### Directory Structure

The `./FPOP` directory contains the artifact for Extensible Metatheory Mechanization via Family Polymorphism, a PLDI'23
paper, which we make comparison to. 

The `./rocqet` directory contains our implementation of Rocqet and our CompCert casestudy. 

We package `FPOP` with Nix as well. So both the `./FPOP` and `./rocqet` directory contain a `flake.nix` file 
which provides a reproducible environment. 


### Building Rocqet

The `./rocqet` directory contains our implementation of Rocqet and our CompCert casestudy.

Navigate the the Rocqet implementation:
```
$ cd rocqet
```

Enter into the Nix shell:
```
nix --experimental-features 'nix-command flakes' develop -i
```

Build the code:
```
$ dune b
```

## Rocqet Implementation

The `src` directory contains the implementation of Rocqet. It is written 
in OCaml.

After building, to get a feel for the Rocqet, and to test that things 
are working correctly you can step through the example programs 
in the `./tests` directory.

Use the Emacs provided in the shell with Proof General 
to step through the Rocqet program interactively. 

Refer to https://proofgeneral.github.io/doc/master/userman/Coq-Proof-General/ for how to 
use Proof General for Rocq.


## Performance Evaluation: Rocqet vs FPOP
To reproduce the comparison of Rocqet to FPOP in Figure 9.


### To Get Rocqet Numbers 
While in the Nix shell for Rocqet, navigate into the `bench` directory: 
```
$ cd bench
```

List files to see various STLC combinations:
```
$ ls
```

Run benchmark script (can take up to ~4 minutes):
```
$ ./bench.sh
```

After processing each file, the output will be in a `benchmark_results.csv` file.
The CSV file contains each STLC combination and the proof compilation time in seconds. 
Check that these numbers match the ones given Figure 9 for Rocqet.


### To Get FPOP Numbers

Leave the Nix shell for Rocqet (Ctrl-D to leave a Nix shell).

Go to the root directory and navigate into FPOP: 

```
$ cd FPOP
```

Enter into the Nix shell for FPOP:
```
nix --experimental-features 'nix-command flakes' develop -i
```

Build the code:
```
$ dune b
```

Navigate into a similar benchmark directory:
```
$ cd bench
```

List files to see various STLC combinations (you can also view the files to check that their contents match):
```
$ ls
```

Run benchmark script (can take up to ~30 minutes):
```
$ ./bench.sh
```

Again, the output will be in `benchmark_results.csv`. Check that the 
numbers match the numbers shown in Figure 9 for FPOP.

## Case Study: Certified Compiler Framework

Now, navigate back into `rocqet`, enter into the Nix shell, and build:

```
$ cd rocqet
$ nix --experimental-features 'nix-command flakes' develop -i
$ dune b
```

Navigate into the CompCert casestudy: 

```
$ cd casestudies/compcert
```

Take a look at the structure of the directory: 
```
$ ls
```

Compiler families are spread across multiples files. Thus, a file 
such as `SimplExpr` will contain all the compiler extensions with only 
that pass and its proof of correctness. It will also import other families 
it depends on. The `./lib` directory contains the "infrastructure" code and 
proofs used by compiler passes, correctness proofs, IR semantics, and
theorem statements. 

### Nanopasses

As mentioned in the paper, we modularize the `SimplExpr` pass of the compiler 
with nanopasses:

In `SimplExpr.v`:
* In the `Comp_Heap` extension, we have the following nanopasses: 
  `SimplExpr_Eassign`, `SimplExpr_Evalof`, `SimplExpr_Ederef`, 
   `SimplExpr_Eaddrof`, `SimplExpr_Eassignop`, `SimplExpr_Epostincr`, 
   and `SimplExpr_Eloc`.
   
* In the `Comp_Loops` extension, we have the following nanopasses: 
  `SimplExpr_Swhile`, `SimplExpr_Sdowhile`, and `SimplExpr_Sfor`. 

### Fusing Nanopasses

As mentioned in the paper, nanopasses are fused into a single pass, 
to ensure we get a single tree traversal. This fusing is powered by 
mixin composition and late binding. 

See for the above nanopasses:

* For `Comp_Loops` see the `SimplExpr.v` file around line 3816-3820

* For `Comp_Heap` see the `SimplExpr.v` file around line 4407-4416

### Lfam: A Common Family for Linear and Mach

As mentioned in the paper, `Linear` and `Mach` languages share common 
constructs. The file `Lfam.v` contains the abstracted common functionality 
of these languages. Check the `Linear.v` and `Mach.v` files to see that 
both `Linear` and `Mach` share common functionality from `Lfam`.

### Cfam: A Common Family for Csharpminor, Cminor, and CminorSel

As mentioned in the paper, `Csharpminor`, `Cminor`, and `CminorSel` share 
a common IR and semantics constructs. 
The file `Cfam.v` contains the abstracted common functionality 
of these languages. Check the `Csharpminor.v`, `Cminor.v`, and `CminorSel.v` 
files to see that they all reuse functionality from `Cfam`.

### Cfamtransl: A Common Family for Cminorgen and Selection

`Cminorgen` and `Selection` share common code and proof functionality, 
especially in the base compiler in a common `Cfamtransl` base family. 
Check `Cminorgen.v` to see that `Cminorgen` inherits from `Cfamtransl` and 
`Selection.v` to see that `Selection` reuses `Cfamtransl`.

### Modular RISC-V Representation and Semantics

We modularize the RISC-V semantics of CompCert as our compiler backend.
In the `Asm.v` file, the `RV` family contains all the base RISC-V extensions. 

The `RV` family contains the following RISC-V base/extension ISA as 
nested families: 

* Common: common functionality and Pseudo instructions used by all ISAs
* RV32I: Base RISC-V ISA for 32-bit arithmetic 
* RV64I: Base RISC-V ISA for 64-bit arithmetic, which extends RV32I
* M : RISC-V extension ISA for integer multiplication and division
* F: RISC-V extension ISA for floating point arithmetic
* D: RISC-V extension ISA for double-precision floating point, which extends F

We them combine all extensions to yeild the CompCert RISC-V backend as `Asm`

### Base Compiler and Compiler Extension 

The Base compiler and extension are defined across multiple files, 
Look at any file to see that files contribution to the base compiler 
or an extension.

### Compiler Passes and Correctness Proofs

Our case study is a substantial subset of CompCert which involves the 
following IRs:

* C
* Clight 
* Csharpminor
* CminorSel
* RTL
* LTL
* Linear 
* Mach 
* Asm (RISC-V)

And the translation and correctness proofs for the following passes:

* SimplExpr 
* Cshmgen
* Cminorgen
* Selection
* RTLgen
* Linearize
* Stacking
* Asmgen

You can check that the translation, semantics, and
simulation theorem matches that which is found in https://compcert.org/doc/

### Stepping Through Proofs Interactively

Inside the Nix shell for Rocqet, in the `casestudies/compcert` subdirectory, 
you can use the Emacs (with Proof General) provided in the shell to step through 
the Rocqet implementation of CompCert interactively.

* Check that the base compiler proofs are complete
* Check the translation for each pass is complete


### Performance Evaluation: Rocqet/CompCert vs Rocq/CompCert

We extract passes written in Rocqet into OCaml and "link" with 
CompCert to check that nanopasses or family polymorphism don't 
affect the performance of the compiler. We don't extract Selection and 
Asmgen to link with CompCert because these passes are machine dependent 
and we only support RISC-V, thus we reuse Rocq/CompCert's Selection 
and Asmgen in in our Rocqet/CompCert.

To reproduce the Table 1

#### To Get Rocq/CompCert Numbers 

The `Rocq_CompCert` directory contains the base `CompCert` compiler. 
We also provide a `flake.nix` to

Navigate to `Rocq_CompCert`: 
```
$ cd Rocq_CompCert
$ nix --experimental-features 'nix-command flakes' develop -i
```

Configure the build based on your platform (`-help` will show platforms available): 
```
$ ./configure -help
```

Build the Compiler: 
```
$ make
```

Navigate into tests:
```
$ cd tests
```

List available test files
```
$ ls
```

Navigate into `raytracer`, `regression`, `compression`, `c`, `spass`, and `abi` (do for each): 
```
$ cd raytracer
```

Run make and time the output: 
```
$ time make 
```

Check time output with Table 1.


#### To Get Rocqet/CompCert Numbers 

First we need to build `Rocqet_CompCert`. This is located in the 
toplevel directory. This is just the vanilla CompCert but we keep it 
separate becuase we want to "link" our extracted compiler with it. 

Repeat the steps above to build `Rocqet_CompCert`, but don't run the tests yet.

Now, navigate back into `rocqet` and enter the Nix shell there. 

Navigate into the case study: 
```
cd casestudies/compcert
```

Next, we need to extract our Rocqet passes into OCaml, and link 
with `Rocqet_CompCert`. 

We provide a script which does this extraction automatically. You can run:
```
$ ./extract_passes.sh
```

This will extract the required compiler passes into the `./extraction` 
directory and link with `Rocqet_CompCert`. Check the extracted passes 
are fully generated.

We provide "already extracted" passes in `./extracted` and 
link these passes with `Rocqet_CompCert` because it required 
additional manual setup. You can check that the extracted passes in 
`extracted` match those in `extraction` modulo the mangled name difference.

We have now linked our extracted code with `Rocqet_CompCert`. You should 
leave the Nix shell for Rocqet and go back into the Nix shell for `Rocqet_CompCert`. 

Rebuild the Compiler: 
```
$ make
```

Run the tests as shown for `Rocq_CompCert` and compare with Table 1.
