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
        ocamlDeps = with pkgs.ocaml-ng.ocamlPackages_5_1; [
          ocaml          
          findlib
          dune_3
          ocamlformat_0_26_1
          pkgs.coq
        ];
      in
        {
          devShell = pkgs.mkShell {
            buildInputs = ocamlDeps;
          };
        }
    );
}
