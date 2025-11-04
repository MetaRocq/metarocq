{
  lib,
  mkCoqDerivation,
  single ? false,
  coq,
  equations,
  stdlib,
  version ? null,
}@args:

let
  repo = "metarocq";
  owner = "MetaRocq";
  defaultVersion = lib.switch coq.coq-version [
    { case = "9.0"; out = "1.4-9.0"; }
  ] null;
  release = {
    "1.4-9.0".sha256 = "sha256-5QecDAMkvgfDPZ7/jDfnOgcE+Eb1LTAozP7nz6nkuxg=";
  };
  releaseRev = v: "v${v}";

  # list of core MetaCoq packages and their dependencies
  packages = {
    "utils" = [ ];
    "common" = [ "utils" ];
    "template-coq" = [ "common" ];
    "pcuic" = [ "common" ];
    "safechecker" = [ "pcuic" ];
    "template-pcuic" = [
      "template-coq"
      "pcuic"
    ];
    "erasure" = [
      "safechecker"
      "template-pcuic"
    ];
    "quotation" = [
      "template-coq"
      "pcuic"
      "template-pcuic"
    ];
    "safechecker-plugin" = [
      "template-pcuic"
      "safechecker"
    ];
    "erasure-plugin" = [
      "template-pcuic"
      "erasure"
    ];
    "translations" = [ "template-coq" ];
    "all" = [
      "safechecker-plugin"
      "erasure-plugin"
      "translations"
      "quotation"
    ];
  };

  template-coq = metacoq_ "template-coq";

  metacoq_ =
    package:
    let
      metacoq-deps = lib.optionals (package != "single") (map metacoq_ packages.${package});
      pkgpath = if package == "single" then "./" else "./${package}";
      pname = if package == "all" then "metacoq" else "metacoq-${package}";
      pkgallMake = ''
        mkdir all
        echo "all:" > all/Makefile
        echo "install:" >> all/Makefile
      '';
      derivation =
        (mkCoqDerivation (
          {
            inherit
              version
              pname
              defaultVersion
              release
              releaseRev
              repo
              owner
              ;

            mlPlugin = true;
            propagatedBuildInputs = [
              equations
              stdlib
              coq.ocamlPackages.zarith
              coq.ocamlPackages.stdlib-shims
            ] ++ metacoq-deps;

            patchPhase =
                ''
                  patchShebangs ./configure.sh
                  patchShebangs ./template-coq/update_plugin.sh
                  patchShebangs ./template-coq/gen-src/to-lower.sh
                  patchShebangs ./safechecker-plugin/clean_extraction.sh
                  patchShebangs ./erasure-plugin/clean_extraction.sh
                  echo "CAMLFLAGS+=-w -60 # Unused module" >> ./safechecker/Makefile.plugin.local
                  sed -i -e 's/mv $i $newi;/mv $i tmp; mv tmp $newi;/' ./template-coq/gen-src/to-lower.sh ./safechecker-plugin/clean_extraction.sh ./erasure-plugin/clean_extraction.sh
                '';

            configurePhase =
              lib.optionalString (package == "all") pkgallMake
              + ''
                touch ${pkgpath}/metacoq-config
              ''
              +
                lib.optionalString
                  (lib.elem package [
                    "erasure"
                    "template-pcuic"
                    "quotation"
                    "safechecker-plugin"
                    "erasure-plugin"
                    "translations"
                  ])
                  ''
                    echo  "-I ${template-coq}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/Template/" > ${pkgpath}/metacoq-config
                  ''
              + lib.optionalString (package == "single") ''
                ./configure.sh local
              '';

            preBuild = ''
              cd ${pkgpath}
            '';

            meta = {
              homepage = "https://metarocq.github.io/";
              license = lib.licenses.mit;
              maintainers = with lib.maintainers; [ cohencyril ];
            };
          }
          // lib.optionalAttrs (package != "single") {
            passthru = lib.mapAttrs (package: deps: metacoq_ package) packages;
          }
        ));
    in
    derivation;
in
metacoq_ (if single then "single" else "all")
