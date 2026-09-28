final: prev: let
  pkg = ./default.nix;
  name = "metacoq";
  injectPkg = name: set:
    prev.${name}.overrideScope (self: _: {
      metacoq = self.callPackage pkg {};
      metacoq-dev = self.callPackage pkg { version = "dev"; };
    });
in (prev.lib.mapAttrs injectPkg {
  inherit (final) coqPackages_8_17 coqPackages_8_18 coqPackages_8_19;
})
