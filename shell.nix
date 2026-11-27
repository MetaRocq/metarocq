# Development shell for MetaRocq.
#
# `nix-shell` picks this file over default.nix.  It is the shell of the
# coq-nix-toolbox (see default.nix and .nix/config.nix: Rocq master, Stdlib,
# Equations, ExtLib from the rocq-dev bundle), extended with what is needed to
# build MetaRocq with dune and to work on it from VS Code:
#
#  - Equations and ExtLib themselves (the toolbox shell only has their
#    dependencies), so that `dune build` works in the shell;
#  - the VsRocq language server (`vsrocqtop`), built against the same Rocq.
#    The nixpkgs one is marked broken for Rocq master and the toolbox looks
#    it up under its former name (vscoq-language-server), so we build it
#    from the main branch of vsrocq here;
#  - rocq-lsp (`coq-lsp` and its `pet` Petanque server, used e.g. by
#    rocq-mcp), from its main branch, which follows Rocq master.
#
# VS Code can run `vsrocqtop` in this environment through .nix/vsrocqtop,
# by setting "vsrocq.path": ".nix/vsrocqtop" in .vscode/settings.json.
# More generally, `.nix/env-exec cmd args` runs any command in it.
#
# Only nix-shell uses this file: CI (nix-build) still goes through default.nix.
args@{ ... }:
let
  shell = import ./default.nix ({ inNixShell = true; } // args);
  pkgs = shell.passthru.pkgs;
  rocqPackages = pkgs.rocqPackages;
  ocamlPackages = rocqPackages.rocq-core.ocamlPackages;

  # vsrocq main needs memprof-limits, whose nixpkgs version (0.2.1) does not
  # support OCaml 5.
  memprof-limits = ocamlPackages.memprof-limits.overrideAttrs (o: {
    version = "0.3.0";
    src = pkgs.fetchFromGitLab {
      owner = "gadmm";
      repo = "memprof-limits";
      tag = "v0.3.0";
      hash = "sha256-k/uB1jDQtE/PkVPU8zg8cpOmlPttTWVpKerQ0HuWfuI=";
    };
    nativeBuildInputs = (o.nativeBuildInputs or [ ]) ++ [ ocamlPackages.cppo ];
    meta = o.meta // { broken = false; };
  });

  vsrocq-language-server =
    (rocqPackages.vsrocq-language-server.override { version = "main"; })
    .overrideAttrs (o: {
      # vsrocq main no longer uses lablgtk, and is built against rocq-core
      # directly rather than through the coq compatibility package.
      nativeBuildInputs = [
        rocqPackages.rocq-core
        ocamlPackages.ocaml
        ocamlPackages.findlib
        ocamlPackages.dune_3
      ];
      buildInputs = [ rocqPackages.rocq-core memprof-limits ]
        ++ (with ocamlPackages; [
          findlib
          base
          zarith
          yojson
          sexplib
          ppx_sexp_conv
          ppx_deriving
          ppx_import
          ppx_yojson_conv
          ppx_optcomp
          ppx_blob
          ppx_inline_test
          ppx_assert
          result
          jsonrpc
          lsp
          sel
        ]);
      doCheck = false;
      meta = o.meta // { broken = false; };
    });

  # The opam package of rocq-lsp is still named coq-lsp.  The vendored Rocq
  # is a git submodule, absent from the archive: the installed one is used.
  rocq-lsp = ocamlPackages.buildDunePackage {
    pname = "coq-lsp";
    version = "main";
    src = builtins.fetchTarball
      "https://github.com/rocq-community/rocq-lsp/archive/main.tar.gz";
    nativeBuildInputs = [
      rocqPackages.rocq-core
      ocamlPackages.menhir
      pkgs.makeWrapper
    ];
    buildInputs = [ rocqPackages.rocq-core memprof-limits ]
      ++ (with ocamlPackages; [
        findlib
        zarith
        cmdliner
        yojson
        uri
        dune-build-info
        tyxml
        menhirLib
        logs
        lwt
        zipc
        sexplib
        ppx_deriving
        ppx_deriving_yojson
        ppx_import
        ppx_sexp_conv
        ppx_compare
        ppx_hash
        ppx_inline_test
      ]);
    doCheck = false;
    # The binaries load their libraries and dependencies with findlib at run
    # time, as in nixpkgs' coq-lsp.
    postInstall = ''
      for bin in $out/bin/*; do
        wrapProgram "$bin" --prefix OCAMLPATH : "$OCAMLFIND_DESTDIR" \
          --prefix OCAMLPATH : "$OCAMLPATH"
      done
    '';
  };
in
shell.overrideAttrs (o: {
  nativeBuildInputs = (o.nativeBuildInputs or [ ]) ++ [
    vsrocq-language-server
    rocq-lsp
  ];
  buildInputs = (o.buildInputs or [ ]) ++ [
    rocqPackages.stdlib
    rocqPackages.equations
    rocqPackages.ExtLib
  ];
  passthru = (o.passthru or { }) // {
    inherit vsrocq-language-server rocq-lsp;
  };
})
