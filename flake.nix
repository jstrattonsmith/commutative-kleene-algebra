{
  description = "Description for the project";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    coq-library-undecidability.url = "github:uds-psl/coq-library-undecidability/rocq-9.0";
    coq-library-undecidability.flake = false;
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, coq-library-undecidability, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import an internal flake module: ./other.nix
        # To import an external flake module:
        #   1. Add foo to inputs
        #   2. Add foo as a parameter to the outputs function
        #   3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };

        # Per-system attributes can be defined here. The self' and inputs'
        # module parameters provide easy access to attributes of the same
        # system.

        # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
        packages.default = pkgs.coqPackages.coq-ka-comm-undec;

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
            pkgs.rocqPackages.vsrocq-language-server
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

      };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        overlays.default = final: prev: {
          coqPackages = prev.coqPackages.overrideScope (final: prev: {
            coq-ka-comm-undec = prev.mkCoqDerivation {
              pname = "coq-ka-comm-undec";
              defaultVersion = "dev";
              release.dev.src = ./.;
              propagatedBuildInputs = [
                final.coq
                final.coq-library-undecidability
                final.stdpp
              ];
            };
            coq-library-undecidability = prev.mkCoqDerivation {
              pname = "coq-library-undecidability";
              defaultVersion = "dev";
              release.dev.src = coq-library-undecidability;
              propagatedBuildInputs = [
                final.coq
                final.metarocq-template-rocq
              ];
            };
          });
        };

      };
    };
}
