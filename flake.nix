{
  description = "A programming language for Polynomial Functors";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShell = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.fd
            pkgs.nixpkgs-fmt
            pkgs.opam
            pkgs.pkg-config
            pkgs.shellcheck
          ];
        };
      });
}
