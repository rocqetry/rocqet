# The Rocqet Proof Language

## Overview

Rocqet equips the [Rocq Prover](https://coq.inria.fr/) with *nested family polymorphism* to 
enable scalable, extensible mechanized proofs.

## Getting Started
We currently build with Rocq version 8.19.0 using OCaml 5.1.0.

Currently, we only support installation from source. 
In the future, you can expect to install it like so: 
```sh
$ opam install rocqet
```

You can follow these steps to get started:
1. Install [opam](https://opam.ocaml.org/doc/Install.html)

2. Create a new opam switch with OCaml 5.1.0
```sh
$ opam switch create fpop2.0-memtrace 5.1.0
```

```sh
$ opam pin add coq 8.19.0
```

The CompCert case study has a dependency 
on [Flocq](https://flocq.gitlabpages.inria.fr/). 
You need to install it before trying out that case study.

### Nix/NixOS
We provide a `flake.nix` with all the dependencies (including Emacs, Proof General, Flocq, etc)

## Proof User Interface
We recommend [Proof General](https://proofgeneral.github.io/) 
in [Emacs](https://www.gnu.org/software/emacs/) for all platforms.
If you prefer [VSCode](https://code.visualstudio.com/), 
we recommend [VSCoq](https://github.com/coq/vscoq), 
but it only properly for Linux systems with our plugin.

Other [user interfaces](https://coq.inria.fr/user-interfaces.html) exist, 
but we haven't tested them with our plugin. Feel free to try it out.

## Case Studies
1. CompCert
2. STLC

## Bugs and Knwon Issues
Generally, issues/bugs with our plugin can be found [here](https://github.com/ebresafegaga/rocqet/issues).

Other issues:
1. VSCoq, as a proof user interface, doesn't work properly with our plugin on macOS

