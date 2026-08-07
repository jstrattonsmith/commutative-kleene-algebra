{
  description = "Description for the project";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    # Pinned to match coq-synthetic-computability's own pin, so the Rocq
    # toolchain (Rocq 9.0.1, Equations 1.3.1+9.0, stdpp 1.12.0) agrees between
    # the two projects.
    nixpkgs.url = "github:NixOS/nixpkgs/c5296fdd05cfa2c187990dd909864da9658df755";
    coq-library-undecidability.url = "github:uds-psl/coq-library-undecidability/rocq-9.0";
    coq-library-undecidability.flake = false;
    # Local checkout so in-progress edits are picked up without committing/
    # pushing first; consumed as a real flake so we can reuse its own overlay.
    coq-synthetic-computability.url = "path:/Users/Jeremy/Documents/College/RIT/PhD/CKA_Undec/coq-synthetic-computability";
    # Share our pinned coq-library-undecidability instead of building a
    # second, possibly-drifted copy.
    coq-synthetic-computability.inputs.coq-library-undecidability.follows = "coq-library-undecidability";
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, coq-library-undecidability, coq-synthetic-computability, ... }:
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
          overlays = [
            coq-synthetic-computability.overlays.default
            self.overlays.default
          ];
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
              version = ./.;
              # coq-library-undecidability (via its L/Tactics/Extract.v)
              # transitively needs the equations OCaml findlib plugin on
              # OCAMLPATH; mlPlugin ensures that setup hook fires for
              # consumers of this derivation too (e.g. `nix develop`).
              mlPlugin = true;
              propagatedBuildInputs = [
                final.coq
                final.coq-library-undecidability
                final.coq-synthetic-computability
                final.stdpp
              ];
            };
            # coq-library-undecidability is defined by
            # coq-synthetic-computability's own overlay (applied before this
            # one, above) -- it patches in the L/ files our Models/CT.v needs
            # plus the MetaRocq/equations deps. Deliberately not redefined
            # here so that patched version is what `final` resolves to.
          });
        };

      };
    };
}
