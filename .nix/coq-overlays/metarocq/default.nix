{
  lib,
  mkCoqDerivation,
  coq,
  single ? false,
  equations,
  ExtLib,
  stdlib,
  version ? null,
}@args:

let
  repo = "metarocq";
  owner = "MetaRocq";
  defaultVersion = null;
  releaseRev = v: "v${v}";

  # list of core MetaRocq packages and their dependencies
  packages = {
    "utils" = [ ];
    "common" = [ "utils" ];
    "template-rocq" = [ "common" ];
    "pcuic" = [ "common" ];
    "template-pcuic" = [
      "template-rocq"
      "pcuic"
    ];
    # includes the safechecker plugin
    "safechecker" = [
      "pcuic"
      "template-pcuic"
    ];
    # includes the erasure plugin
    "erasure" = [
      "safechecker"
      "template-pcuic"
    ];
    "quotation" = [
      "template-rocq"
      "pcuic"
      "template-pcuic"
    ];
    "translations" = [ "template-rocq" ];
    "all" = [
      "safechecker"
      "erasure"
      "translations"
      "quotation"
    ];
  };

  opamName =
    package:
    if package == "all" then
      "rocq-metarocq"
    else if package == "template-rocq" then
      "rocq-metarocq-template"
    else
      "rocq-metarocq-${package}";

  corePackages = map opamName (lib.remove "all" (lib.attrNames packages));

  # The plugins are now part of the safechecker and erasure packages; the
  # attributes are kept for the users of the former plugin packages.
  aliases = {
    "safechecker-plugin" = "safechecker";
    "erasure-plugin" = "erasure";
  };

  metarocq_ =
    package:
    let
      metarocq-deps = lib.optionals (package != "single") (map metarocq_ packages.${package});
      pname = if package == "all" then "metarocq" else "metarocq-${package}";
      derivation = mkCoqDerivation (
        {
          inherit
            version
            pname
            defaultVersion
            releaseRev
            repo
            owner
            ;

          # Each package is built from the whole source tree with
          # `dune build -p rocq-metarocq-<package>`.
          useDune = true;
          opam-name = opamName package;
          mlPlugin = true;
          propagatedBuildInputs = [
            equations
            ExtLib
            stdlib
          ] ++ metarocq-deps;

          meta = {
            homepage = "https://metarocq.github.io/";
            license = lib.licenses.mit;
            maintainers = with lib.maintainers; [ cohencyril ];
          };
        }
        // lib.optionalAttrs (package == "single") {
          # Build and install all the packages at once
          buildPhase = ''
            runHook preBuild
            dune build -p ${lib.concatStringsSep "," corePackages} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR ${lib.concatStringsSep " " corePackages}
            mkdir $out/lib/coq/
            mv $OCAMLFIND_DESTDIR/coq $out/lib/coq/${coq.coq-version}
            runHook postInstall
          '';
        }
        // lib.optionalAttrs (package == "all") {
          # The meta-package installs no theory, so there is no coq directory
          # to move, unlike in the default install phase.
          installPhase = ''
            runHook preInstall
            dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR ${opamName package}
            runHook postInstall
          '';
        }
        // lib.optionalAttrs (package != "single") {
          passthru =
            lib.mapAttrs (package: deps: metarocq_ package) packages
            // lib.mapAttrs (alias: package: metarocq_ package) aliases;
        }
      );
    in
    derivation;
in
metarocq_ (if single then "single" else "all")
