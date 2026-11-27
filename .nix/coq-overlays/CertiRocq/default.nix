{
  lib,
  pkgs,
  mkRocqDerivation,
  rocq-core,
  wasmcert,
  compcert,
  metarocq-erasure,
  metarocq-safechecker,
  ExtLib,
  version ? null,
  # Whether to build and test the bootstrapped compiler and checker instead of the
  # packages (only in the bootstrap bundle of .nix/config.nix)
  bootstrap ? false,
}:

with lib;
let
  # The theories, the optimized plugin and its runtime, and the vanilla plugin
  packages = concatStringsSep "," [ "rocq-certirocq" "rocq-certirocq-vanilla" ];
  # With the bootstrapped compiler and checker, which are only built by the tests
  allPackages = concatStringsSep "," [
    "rocq-certirocq" "rocq-certirocq-vanilla" "rocq-certirocqc" "rocq-certirocqchk"
  ];
  # A dune command, printed in the log, with the progress of the builds, but each
  # command of the tests and of the bootstrap (to see what a long one is running)
  dune = display: args: ''
    ( set -x; dune ${args} --display=${display} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES} )
  '';
  # A dune command printing each Rocq file and C compilation as it finishes, with the
  # output and errors of the commands, but not the OCaml commands
  dune-rocq = args: ''
    ( set -x -o pipefail
      dune ${args} --display=short ''${enableParallelBuilding:+-j $NIX_BUILD_CORES} 2>&1 \
        | { grep --line-buffered -vE \
              '^ +(ocamldep|ocamlc|ocamlopt|ocamlmklib|ocamlfind|ocaml-index|ocamllex|menhir|ppx|odoc) ' \
            || true; } )
  '';
in
(mkRocqDerivation {
  pname = "CertiRocq";
  owner = "CertiRocq";
  repo = "certirocq";
  opam-name = "rocq-certirocq";
  useDune = true;
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  propagatedBuildInputs = [
    # Used by the runtime, and by the programs compiled with its GMP bindings
    pkgs.gmp
    wasmcert
    compcert
    ExtLib
    metarocq-erasure
    metarocq-safechecker
  ];

  # The plugin invokes a C compiler to build the code it generates,
  # so dependents need one too.
  propagatedNativeBuildInputs = [
    pkgs.clang
  ];

  meta = {
    description = "CertiRocq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}).overrideAttrs (o: {
  # With the bootstrap, only the theories of the compiler, without its proofs (the
  # default bundle builds them), the plugins and the runtime
  buildPhase = ''
    runHook preBuild
  '' + (if bootstrap then dune-rocq "build -p ${allPackages} @@compiler"
        else dune-rocq "build -p ${packages}") + ''
    runHook postBuild
  '';
  doCheck = true;
  # For the Wasm tests
  nativeCheckInputs = [ pkgs.nodejs_22 pkgs.python3 ];
  # The tests under tests/, or with the bootstrap those of the bootstrapped compiler
  # and checker (the default bundle runs the others), which dune runs with the plugins
  # of the build directory
  checkPhase = ''
    runHook preCheck
  '' + (if bootstrap then dune "short" "build -p ${allPackages} @bootstrap/runtest"
        else dune "short" "build -p ${packages} @runtest") + ''
    runHook postCheck
  '';
  # The bootstrap bundle only tests: there is nothing to install
  installPhase = ''
    runHook preInstall
  '' + (if bootstrap then ''
    mkdir -p $out
  '' else ''
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR ${replaceStrings [","] [" "] packages}
    mkdir $out/lib/coq/
    mv $OCAMLFIND_DESTDIR/coq $out/lib/coq/${rocq-core.rocq-version}
  '') + ''
    runHook postInstall
  '';
})
