
{
  description = "Build a rocq (coq) package";
  inputs.opam-nix.url = "github:tweag/opam-nix";
  inputs.opam-repository.url = "github:ocaml/opam-repository";
  inputs.opam-repository.flake = false;
  inputs.nixpkgs.url = "github:nixos/nixpkgs";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  # inputs.coq-library-undecidability.url = "github:uds-psl/coq-library-undecidability/coq-8.20";
  # inputs.coq-library-undecidability.flake = false;
  outputs =
    {
      self,
      opam-nix,
      flake-utils,
      opam-repository,
      # coq-library-undecidability
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
          # pkgs = nixpkgs.legacyPackages.${system};
          opam-coq-archive = pkgs.fetchFromGitHub {
            "owner" = "rocq-prover";
            "repo" = "opam";
            "rev" = "faf3b3d4d2a25f0b9a312e416d1a43c826e25ec7";
            "hash" = "sha256-9+5jrUbNpuC7Ct6rWIRUmmwuH1NAPkJofQC3BK/3yGg=";
          };
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
