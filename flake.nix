{
  description = "MetaCoq is a project formalizing Coq in Coq";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    makes.url = "github:fluidattacks/makes/24.02";
    nixpkgs.url = "github:nixos/nixpkgs/release-24.05";
  };

  outputs = { self, flake-utils, makes, nixpkgs, ... }:
    with flake-utils.lib;
    eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [self.overlays.default];
      };
    in {
        devShells.default = self.packages.${system}.default;

        packages = {
          default = self.packages.${system}.coqPackages_8_19-metacoq-dev;
        } // (with pkgs.lib; foldl' mergeAttrs {  }
          (concatMap (coq: [{
            # Released packages using upstream tarballs (see .nix/default.nix)
            "${coq}-metacoq" = pkgs.${coq}.metacoq;
            # Local source tree
            "${coq}-metacoq-dev" = pkgs.${coq}."metacoq-dev";
          }])
            [ "coqPackages_8_17" "coqPackages_8_18" "coqPackages_8_19" ]));

        # CI runner
        apps.makes = makes.apps.${system}.default;
    })
    // {
      overlays.default = import .nix/overlay.nix;
    };
}
