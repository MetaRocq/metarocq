# Installation instructions

## Installing with OPAM

The easiest way to get all packages is through [`opam`](http://opam.ocaml.org).
See [Rocq's opam documentation](https://coq.inria.fr/opam-using.html)
for installing an `opam` switch for Rocq.
See [releases](https://github.com/MetaRocq/metarocq/releases) and
[Rocq's Package Index](https://coq.inria.fr/opam/www/) for information on
the available releases and opam packages.

To add the Rocq repository to available `opam` packages, use:

    # opam repo add coq-released https://coq.inria.fr/opam/released

To update the list of available packages at any point use:

    # opam update

Then, simply issue:

    # opam install rocq-metarocq

MetaRocq is split into multiple packages that get all installed using the
`rocq-metarocq` meta-package:

 - `rocq-metarocq-utils` for a general library used by all MetaRocq packages
 - `rocq-metarocq-common` for definitions used both by Template-Rocq and PCUIC packages
 - `rocq-metarocq-template` for the Template Monad and quoting plugin
 - `rocq-metarocq-pcuic` for the PCUIC metatheory development
 - `rocq-metarocq-template-pcuic` for the verified Template-Rocq <-> PCUIC translations
 - `rocq-metarocq-safechecker` for the verified checker on PCUIC terms
   and the extracted verified checker plugin
 - `rocq-metarocq-erasure` for the verifed erasure from PCUIC to
   untyped lambda-calculus and the extracted verified erasure plugin
 - `rocq-metarocq-translations` for example translations from type theory
   to type theory: e.g. variants of parametricity.
 - `rocq-metarocq-quotation` for a quotation library, allowing to
   quote MetaRocq terms and typing derivations as MetaRocq terms,
   with a work-in-progress proof of Löb's theorem.

There are also `.dev` packages available in the `extra-dev` repository
of Rocq, to get those you will need to activate the following repositories:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev


## Installing from source code

### Requirements

To compile the library, you need:

- The `Rocq` version corrsponding to your branch (you can use the `coq.dev` package
  for the `main` branch).
- `OCaml` (tested with `4.14.0`)
- [`dune`](https://dune.build) 3.22 or later
- [`Equations 1.3`](http://mattam82.github.io/Rocq-Equations/)

The recommended way to build a development environment for MetaRocq is
to have a dedicated `opam` switch (see below). Alternatively, a Nix shell
provides all of them (see [Using Nix](#using-nix)).

### Getting the sources

To get the source code:

    # git clone https://github.com/MetaRocq/metarocq.git
    # git checkout -b main origin/main
    # git status

This checks that you are indeed on the `main` branch.

### Setting up an `opam` switch

To setup a fresh `opam` installation, you might want to create a
"switch" (an environment of `opam` packages) for `Rocq` if you don't have
one yet. You need to use **opam 2** to obtain the right version of
`Equations`.

    # opam switch create rocq.dev --packages="ocaml-variants.4.14.0+options,ocaml-option-flambda"
    # eval $(opam env)

This creates the `rocq.dev` switch which initially contains only the
basic `OCaml` `4.14.0` compiler with the `flambda` option enabled,
and puts you in the right environment (check with `ocamlc -v`).

Once in the right switch, you can install `Rocq` and the `Equations` package.
For that, you need to first add the Rocq packages repository, using:

    # opam repo add rocq-released https://rocq-prover.org/opam/released

Then, to install the dependencies, it suffices to do:

    # opam install . --deps-only

If the commands are successful you should have `rocq` available (check with `rocq -v`).


**Remark:** You can create a [local switch](https://opam.ocaml.org/blog/opam-20-tips/#Local-switches) for
developing using (in the root directory of the sources):

    # opam switch create . --packages="ocaml-variants.4.14.0+options,ocaml-option-flambda"

Or use `opam switch link foo` to link an existing opam switch `foo` with
the sources directory.


### Using Nix

Instead of an `opam` switch, you can use the Nix shell of the repository
(this requires [Nix](https://nixos.org/download/)). In the root directory of
the sources:

    # nix-shell

This builds the `rocq-dev` bundle of `.nix/config.nix` (Rocq `master`,
Stdlib, Equations and ExtLib, as in the Nix CI) along with the VsRocq
language server `vsrocqtop` of the `main` branch of
[VsRocq](https://github.com/rocq-prover/vsrocq) and
[rocq-lsp](https://github.com/rocq-community/rocq-lsp) (`coq-lsp` and its
`pet` server) of its `main` branch, and opens a shell where `rocq`, `dune`,
`vsrocqtop` and `pet` are available. The first run builds Rocq
`master` and the other dependencies, which takes a while (the `metacoq`
Cachix cache filled by the Nix CI may provide some of them, see
`cachix use metacoq`). Then build MetaRocq with `dune build` in that
shell, as described below.

The Nix shell and an `opam` switch build different Rocq binaries, but both
use the `_build` directory: switching from one to the other requires a full
rebuild of MetaRocq.

Tools started by an editor or an agent cannot run in a `nix-shell`
themselves: `.nix/env-exec cmd args` runs a command in the environment of
the Nix shell, e.g. `.nix/env-exec dune build`. It saves this environment
in `.nix/shell-env` the first time, and reuses it to start quickly. It
recomputes it when `shell.nix` or `.nix/config.nix` change. To pick up newer
versions of Rocq `master`, VsRocq `main` or rocq-lsp `main`, run
`.nix/env-exec --update-env`. The environment leaves out the variables of
the `opam` switch active when it is computed or used, if any.

For instance, a Rocq [MCP](https://modelcontextprotocol.io) server based on
`pet` can be started with `.nix/env-exec` as its command, followed by the
command starting the server.

### Compiling from sources

MetaRocq is built with [`dune`](https://dune.build) (see `dune-project`):

- `dune build` (or `make`) compiles the `template-rocq` plugins, the `pcuic`
  development, the `safechecker` and `erasure` libraries and plugins,
  and the `translations` and `quotation` libraries.
  You can also selectively build a part, e.g. `dune build theories/PCUIC`.
  The Rocq sources are in `theories/<Name>`, for the `MetaRocq.<Name>`
  libraries, and the OCaml sources of the plugins in `src`.

- `dune test` (or `make test`) builds and checks the `test-suite` and the
  `examples`, as well as the output of the `translations`. The output of a
  file `foo.v` is written to `_build/default/.../foo.output` rather than to the
  terminal, and compared with the expected output in `foo.expected`, which
  `dune promote` updates. Only the files that print something have a
  `.expected` file. The output of the `demo` and `metarocq_tour` examples
  and of the `loop-checking` test depends on generated universe names: it is
  kept off the terminal in the same way, but not checked (their `.expected`
  files are generated as copies of their output).

- `dune install` (or `make install`) installs the libraries in `Rocq`'s
  `user-contrib` library and the plugins as findlib libraries. Then the
  `MetaRocq` namespace can be used for `Require Import` statements, e.g.
  `From MetaRocq.Template Require Import All.`.

- `dune uninstall` (or `make uninstall`) to undo the last line.

The plugins are the findlib libraries `rocq-metarocq-template.plugin` (the
quoting and template monad plugin), `rocq-metarocq-template.extractable` (the
plugin running extracted template programs),
`rocq-metarocq-safechecker.plugin` and `rocq-metarocq-erasure.plugin`.

### Develop with Vs Code

There is a workspace file directly available with the project.
To use it:
1. Run `opam switch link name_switch`
2. Open vscode with `code .vscode/metarocq.code-workspace`

To use the Nix shell (see [Using Nix](#using-nix)) from VS Code, set the
path of the VsRocq language server to the `.nix/vsrocqtop` wrapper, e.g. in
`.vscode/settings.json`:

    {
        "vsrocq.path": ".nix/vsrocqtop"
    }

and build MetaRocq with `nix-shell --run 'dune build'` (or
`.nix/env-exec dune build`). The wrapper runs `vsrocqtop` in the environment
of the Nix shell, through `.nix/env-exec`.

