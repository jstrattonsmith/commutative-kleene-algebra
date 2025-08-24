{ pkgs ? import <nixpkgs> {} }:

with pkgs;

mkShell {
  buildInputs = [ coq_8_20 coqPackages_8_20.vscoq-language-server ];
}