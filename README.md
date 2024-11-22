# Rocqet Proof Language

## Overview

Rocqet equips [Rocq](https://coq.inria.fr/) with *nested family polymorphism* to 
enable scalable, extensible mechanized proofs.

## Building
We currently build with Rocq version `8.19.0` using OCaml `5.1.0`.

Currently, we only support installation from source. 
In the future, you can expect to install it like so: 
```sh
$ opam install rocqet
```

Right now, you can follow these steps to get build:
1. Install [opam](https://opam.ocaml.org/doc/Install.html)

2. Create a new opam switch with OCaml `5.1.0`:
```sh
$ opam switch create 5.1.0
```
3. Install Rocq:
```sh
$ opam pin add coq 8.19.0
```
4. The CompCert case study has a dependency 
on [Flocq](https://flocq.gitlabpages.inria.fr/). 
You need to install it before trying out that case study.
5. Finally, we can build by runinng the command: 
```sh
$ dune b
```

### Nix/NixOS
We provide a `flake.nix` with all the dependencies (including Emacs, Proof General, Flocq, etc)

## Proof User Interface
We recommend [Proof General](https://proofgeneral.github.io/) 
in [Emacs](https://www.gnu.org/software/emacs/) for all platforms.
If you prefer [VSCode](https://code.visualstudio.com/), 
we recommend [VSCoq](https://github.com/coq/vscoq), 
but it only works properly for Linux systems with our plugin.

Other [user interfaces](https://coq.inria.fr/user-interfaces.html) exist, 
but we haven't tested them with our plugin. Feel free to try it out.

## Try It Out
After building and installing a proof interface, you can now step 
through proofs. We provide lots of example 
programs [here](https://github.com/ebresafegaga/rocqet/tree/main/tests).
You can step through the examples interactively, to get familiar with the 
proof language.

For more interesting programs, we have a framework for extensible certified 
C compilers [here](https://github.com/ebresafegaga/rocqet/tree/main/casestudies/compcert) and 
modular mechanized simply-typed lambda calculi 
[here](https://github.com/ebresafegaga/rocqet/tree/main/bench).

## Hacking
See [here](https://github.com/ebresafegaga/rocqet/blob/main/HACKING.md).

## Bugs and Knwon Issues
Generally, issues/bugs with our plugin can be found [here](https://github.com/ebresafegaga/rocqet/issues).

Others:
1. VSCoq, as a proof user interface, doesn't work properly with our plugin on macOS

