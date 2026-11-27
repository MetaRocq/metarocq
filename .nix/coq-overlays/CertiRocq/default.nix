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
  # Whether the check phase builds and tests the bootstrapped compiler and checker
  # (only in the bootstrap bundle of .nix/config.nix)
  bootstrap ? false,
}:

with lib;
let
  # The theories, the optimized plugin and its runtime, and the vanilla plugin
  packages = [ "rocq-certirocq" "rocq-certirocq-vanilla" ];
  # The bootstrapped compiler and checker, which are only built by the tests
  allPackages = packages ++ [ "rocq-certirocqc" "rocq-certirocqchk" ];
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
  buildPhase = ''
    runHook preBuild
    dune build -p ${concatStringsSep "," packages} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
    runHook postBuild
  '';
  doCheck = true;
  # For the Wasm tests
  nativeCheckInputs = [ pkgs.nodejs_22 pkgs.python3 ];
  checkPhase = ''
    runHook preCheck
  '' + optionalString bootstrap ''
    echo "running bootstrap"
    dune build -p ${concatStringsSep "," allPackages} @install @runtest ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '' + ''
    echo "running tests"
    # Some test programs recurse deeper than the default stack allows
    ulimit -Ss "$(ulimit -Hs)"
    patchShebangs tests
    installed=$PWD/_build/install/default/lib
    ROCQPATH=$installed/coq/user-contrib''${ROCQPATH:+:$ROCQPATH} \
      OCAMLPATH=$installed''${OCAMLPATH:+:$OCAMLPATH} make -C tests
    runHook postCheck
  '';
  installPhase = ''
    runHook preInstall
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR ${concatStringsSep " " packages}
    mkdir $out/lib/coq/
    mv $OCAMLFIND_DESTDIR/coq $out/lib/coq/${rocq-core.rocq-version}
    runHook postInstall
  '';
})
