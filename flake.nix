
{
  description = "Build a rocq (coq) package";
  inputs.opam-nix.url = "github:tweag/opam-nix";
  inputs.opam-repository.url = "github:ocaml/opam-repository";
  inputs.opam-repository.flake = false;
  inputs.nixpkgs.url = "github:nixos/nixpkgs";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.opam-coq-archive.url = "github:rocq-prover/opam/";
  inputs.opam-coq-archive.flake = false;

  outputs =
    {
      self,
      opam-nix,
      flake-utils,
      opam-repository,
      opam-coq-archive,
      nixpkgs,
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let pkgs = nixpkgs.legacyPackages.${system}; in {
      devShells.default = pkgs.mkShell {
          packages = with self.legacyPackages.${system}; [
            vscoq-language-server
            coq-library-undecidability
            coq
          ];
        };
      legacyPackages =
        let
          inherit (opam-nix.lib.${system}) queryToScope;
          scope =
            queryToScope
              {
                repos = [
                  "${opam-repository}"
                  "${opam-coq-archive}/released"
                ];
              }
              {
                coq-library-undecidability = "*"; # "1.1.2+8.20";
                ocaml-base-compiler = "*"; # "4.14.1+flambda";
                vscoq-language-server = "*";
              };
        in
        scope;

        packages.default = self.legacyPackages.${system}.coq-library-undecidability;
    });
}
