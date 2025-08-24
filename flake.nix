{
  description = "Build an opam project not in the repo, using sane defaults";
  inputs.opam-nix.url = "github:tweag/opam-nix";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.coq-library-undecidability.url = "github:uds-psl/coq-library-undecidability";
  outputs =
    {
      self,
      opam-nix,
      coq-library-undecidability,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (system: {
      legacyPackages =
        let
          inherit (opam-nix.lib.${system}) buildOpamProject;
          scope = buildOpamProject { } "coq-library-undecidability" coq-library-undecidability {
            ocaml-system = "*";
          };
        in
        scope;

      packages.default = self.legacyPackages.${system}.coq-library-undecidability;
    });
}
# {
#   description = "Build a rocq (coq) package";
#   inputs.opam-nix.url = "github:tweag/opam-nix";
#   inputs.opam-repository.url = "github:ocaml/opam-repository";
#   inputs.opam-repository.flake = false;
#   inputs.nixpkgs.url = "github:nixos/nixpkgs";
#   inputs.flake-utils.url = "github:numtide/flake-utils";
#   outputs =
#     {
#       self,
#       opam-nix,
#       flake-utils,
#       opam-repository,
#       nixpkgs,
#     }:
#     flake-utils.lib.eachDefaultSystem (system: {
#       legacyPackages =
#         let
#           pkgs = nixpkgs.legacyPackages.${system};
#           opam-coq-archive = pkgs.fetchFromGitHub {
#             "owner" = "uds-psl";
#             "repo" = "coq-library-undecidability";
#             "rev" = "70dfc56f33a6e4835281044e68aa68279989047e";
#             "hash" = "sha256-yGXw7khdHcro1yTQrr2yngtOAVy8jHJEO7G93Znp5Cc=";
#           };
#           inherit (opam-nix.lib.${system}) queryToScope;
#           scope =
#             queryToScope
#               {
#                 repos = [
#                   "${opam-repository}"
#                   "${opam-coq-archive}/extra-dev"
#                 ];
#               }
#               {
#                 rocq-prover = "*";
#                 coq-inf-seq-ext = "*";
#                 ocaml-base-compiler = "*";
#               };
#         in
#         scope;

#       packages.default = self.legacyPackages.${system}.coq-inf-seq-ext;
#     });
# }

# {
#   inputs = {
#     opam-nix.url = "github:tweag/opam-nix";
#     flake-utils.url = "github:numtide/flake-utils";
#     nixpkgs.follows = "opam-nix/nixpkgs";
#   };
#   outputs =
#     {
#       self,
#       flake-utils,
#       opam-nix,
#       nixpkgs,
#     }@inputs:
#     # Don't forget to put the package name instead of `throw':
#     let
#       package = throw "Put the package name here!";
#     in
#     flake-utils.lib.eachDefaultSystem (
#       system:
#       let
#         pkgs = nixpkgs.legacyPackages.${system};
#         on = opam-nix.lib.${system};
#         scope = on.buildOpamProject { } package ./. { ocaml-base-compiler = "*"; };
#         overlay = final: prev: {
#           # Your overrides go here
#         };
#       in
#       {
#         legacyPackages = scope.overrideScope overlay;

#         packages.default = self.legacyPackages.${system}.${package};
#       }
#     );
# }
