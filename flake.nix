{
  description = "Description for the project";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    # Pinned to match coq-synthetic-computability's own pin, so the Rocq
    # toolchain (Rocq 9.0.1, Equations 1.3.1+9.0, stdpp 1.12.0) agrees between
    # the two projects.
    nixpkgs.url = "github:NixOS/nixpkgs/c5296fdd05cfa2c187990dd909864da9658df755";
    # This fork's enable-L-nix-9.0 branch: uncomments the L/ extraction
    # framework and adds a working flake.nix on top of an otherwise-unmodified
    # rocq-9.0 (0 commits ahead/behind upstream at the branch point, checked
    # 2026-08-31). Pinned via github: rather than a local path: input -- Nix
    # flakes cannot resolve a relative path: input across sibling git repos
    # (confirmed empirically: it resolves against the referring flake's own
    # git-fetched store copy, not the real filesystem, even with --impure).
    coq-library-undecidability.url = "github:jstrattonsmith/coq-library-undecidability/enable-L-nix-9.0";
    coq-library-undecidability.flake = false;
    # Same reasoning: arthuraa/coq-synthetic-computability (a real GitHub
    # remote both projects already push to), not a local path: input.
    coq-synthetic-computability.url = "github:arthuraa/coq-synthetic-computability";
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
