{
  description = "Nested family polymorphism in a proof language";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";    
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ ]; };
        coq = pkgs.coq_8_19;
        ocamlPkgs = coq.ocamlPackages;
        coqPkgs = pkgs.coqPackages_8_19;

        shellDeps = [
          ocamlPkgs.ocaml          
          ocamlPkgs.findlib
          pkgs.dune_3
          coq
          coqPkgs.flocq
          pkgs.emacs
          pkgs.emacsPackages.exec-path-from-shell
          pkgs.emacsPackages.proof-general
        ];
      in
        {
          devShell = pkgs.mkShell {
            buildInputs = shellDeps;
          };
        }
    );
}