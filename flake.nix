{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
  };
  outputs = { self, flake-utils, opam-nix, nixpkgs }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};

        localPackagesQuery = builtins.mapAttrs (_: pkgs.lib.last)
          (on.listRepo (on.makeOpamRepo ./.));

        devPackagesQuery = {
          ocaml-lsp-server = "*";
          ocp-indent = "*";
          merlin = "*";
        };

        query = devPackagesQuery // {
          ocaml-base-compiler = "*";
        };

        scope = on.buildDuneProject { pkgs = pkgs.pkgsStatic; } "polytt" ./. query;

        overlay = self: super: {
          # Prevent unnecessary dependencies on the resulting derivation
          polytt = super.polytt.overrideAttrs (_: {
            removeOcamlReferences = true;
            postFixup = "rm -rf $out/nix-support";
          });
        };

        scope' = scope.overrideScope' overlay;

        # Packages from devPackagesQuery
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');

        # Packages in this workspace
        packages =
          pkgs.lib.getAttrs (builtins.attrNames localPackagesQuery) scope';
      in
      {
        legacyPackages = scope';

        packages = packages // { default = packages.polytt; };

        devShells.default = pkgs.mkShell {
          inputsFrom = builtins.attrValues packages;
          buildInputs = devPackages ++ [
            pkgs.fd
            pkgs.nixpkgs-fmt
            pkgs.pkg-config
            pkgs.shellcheck
          ];
        };
      });
}
