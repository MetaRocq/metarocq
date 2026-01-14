{
  fetchNixpkgs,
  inputs,
  makeSearchPaths,
  ...
}: {
  cache.readNixos = true;
  formatNix = {
    enable = true;
    targets = ["/"];
  };
  inputs = {
    # Use nixpkgs from recorded flake.lock
    nixpkgs = let
      nixpkgsAttrs = (builtins.fromJSON (builtins.readFile ./flake.lock)).nodes.nixpkgs_2.locked;
    in
      fetchNixpkgs {
        rev = nixpkgsAttrs.rev;
        sha256 = nixpkgsAttrs.narHash;
        acceptAndroidSdkLicense = false;
        allowUnfree = false;
        overlays = [(import .nix/overlay.nix)];
      };
  };
  outputs."/build" = makeSearchPaths {
    bin = [
      inputs.nixpkgs.coqPackages_8_17.metacoq-dev
    ];
  };
}
