{
  description = "Rocqet: nested family polymorphism for the Rocq prover";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ ]; };        
        coq_8_19 = pkgs.coq_8_19.override { customOCamlPackages = pkgs.ocaml-ng.ocamlPackages_5_1; };
        ocamlPkgs = coq_8_19.ocamlPackages;
        
        # Make sure Coq packages use our custom Coq 8.19, which is built with OCaml 5.1
        coqPkgs = pkgs.coqPackages_8_19.overrideScope' (self: super: {
            coq = coq_8_19;
        });

        shellDeps = [
          ocamlPkgs.ocaml
          ocamlPkgs.findlib
          pkgs.dune_3
          coq_8_19
          coqPkgs.flocq
          pkgs.emacs
          pkgs.emacsPackages.exec-path-from-shell
          pkgs.emacsPackages.proof-general

          # For bench
          pkg.coreutils
          pkg.gnugrep
          pkg.gawk
          pkg.bc
        ];
      in
        {
          devShell = pkgs.mkShell {
            buildInputs = shellDeps;
            shellHook = ''
              echo "Using OCaml version: $(ocaml -version)"
              echo "Using Coq version: $(coqc --version)"
            '';
          };
        }
    );
}
