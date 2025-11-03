{
  lib,
  mkRocqDerivation,
  rocq-core,
  coq,
  stdlib,
  version ? null,
}:

(mkRocqDerivation {
  pname = "equations";
  owner = "mattam82";
  repo = "Coq-Equations";
  opam-name = "rocq-equations";
  inherit version;
  defaultVersion = lib.switch rocq-core.rocq-version [
    { case = "9.0"; out = "1.3.1-9.0"; }
    { case = "9.1"; out = "1.3.1-9.1"; }
  ] null;
  release = {
    "1.3.1-9.0".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
    "1.3.1-9.1".sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";
  };
  releaseRev = v: "v${v}";

  mlPlugin = true;
  useDune = true;

  propagatedBuildInputs = [ coq rocq-core stdlib rocq-core.ocamlPackages.ppx_optcomp ];

  meta = with lib; {
    homepage = "https://mattam82.github.io/Coq-Equations/";
    description = "Plugin for Rocq to add dependent pattern-matching";
    maintainers = with maintainers; [ jwiegley ];
  };
})
