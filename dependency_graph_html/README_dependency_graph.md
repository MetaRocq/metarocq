# Rocq dependency-graph generator

Turn any Rocq/Coq library into an **interactive HTML dependency graph** — one
node per source file, an arrow `A → B` meaning *B `Require`s A*, colored by
package or folder. It works for a single-package repo (like the Rocq stdlib)
and for a multi-package one (like MetaRocq, several sibling packages each with
its own `_RocqProject`).

`gen_graph.py` is the entry point. You tell it which packages to include
(`--lib`) and how to color them (`--group` / `--ref`); everything else is
auto-detected.

## What you get

Running the tool produces two files next to your chosen `-o` output:

- **`…_dependency_graph.html`** — a self-contained page (open it in a browser):
  pan/zoom, name search, click a node to highlight its full dependency cone,
  a legend whose checkboxes dim a group's files in place, a data table, and
  automatic light/dark mode.
- **`…_dependency_graph.d`** — the intermediate unified coqdep file it built
  (handy for debugging or feeding the lower-level scripts).

## Requirements

- **Python 3** — no third-party packages.
- **Graphviz** — the `dot` and `unflatten` executables (`sudo apt install graphviz`).
- **`rocq` on PATH** — *only* when a package has to be scanned fresh (see
  [How the dependency data is obtained](#how-the-dependency-data-is-obtained)).

> **The tool never compiles Rocq code.** It only *scans* `.v` sources with
> `rocq dep` (a dependency scanner, not a compiler) or reuses coqdep output a
> previous build already left on disk. The one build prerequisite is narrow:
> if a package loads a compiled **OCaml plugin** (`Declare ML Module`), that
> plugin must already be built — and only when that package is scanned fresh.
> Plugin directories are placed on `OCAMLPATH` automatically. A pristine,
> unbuilt single-package repo with a cached coqdep file (e.g. the stdlib)
> needs nothing beyond Python and Graphviz.

## Quick start

```bash
# Rocq stdlib (single package, uses its cached coqdep file — no build needed)
python3 gen_graph.py --repo ../stdlib --lib theories -o stdlib_graph.html

# MetaRocq (multi-package — run gen.sh, a saved invocation for its layout)
bash gen.sh                 # or: bash gen.sh /path/to/metacoq
```

## How coloring works

Every file is placed in a **folder** and every folder gets a color. Folders are
named after directories on disk, with each package's source sub-directory
(usually `theories/`) stripped, so the meaningful folders surface directly:

| On disk | Folder | Subfolder |
|---|---|---|
| `pcuic/theories/Syntax/PCUICCases.v` | `pcuic` | `pcuic/Syntax` |
| `theories/ZArith/BinInt.v` (stdlib) | `ZArith` | — |

The analyzed **root** — the common prefix stripped before folders are read — is
computed automatically: `""` for a multi-package repo (top folders = the
packages) and e.g. `theories/` for the stdlib (top folders = `Bool`, `ZArith`,
…). Override it with `--root` if needed.

You choose colors with one of two mutually exclusive options:

- **`--group NAME:F1,F2,…`** — give a set of folders one shared hue; each member
  folder gets its own shade. Use it to color **by package** (or to fold many
  folders into a few named groups). Repeatable, one hue per group.
  ```
  --group "Erasure:erasure,erasure-plugin" --group "PCUIC:pcuic"
  ```
- **`--ref FOLDER`** — give one folder a hue and shade **its subfolders**.
  Use it to color **one package by its internal structure**. Repeatable.
  ```
  --ref pcuic        # pcuic/Syntax, pcuic/Typing, pcuic/Conversion … each a shade
  ```

The palette has 8 distinct hues (blue, yellow, pink, green, violet, orange,
aqua, red); groups/refs beyond 8 and any file outside every group fall into a
neutral gray **"Other"**. So if a repo has more top-level folders than 8 (the
stdlib has ~40), fold them into ≤8 `--group`s.

## Options

| Option | Meaning | Default |
|---|---|---|
| `--lib DIR …` | package dirs to include (relative to `--repo`); **required** | — |
| `--repo PATH` | repo root | auto: current dir, else this script's parent dir, whichever holds the `--lib` dirs |
| `--group NAME:F1,F2,…` | folders sharing a hue, members shaded; repeatable | — |
| `--ref FOLDER` | a folder + its subfolders shaded; repeatable | — |
| `-o, --output FILE` | output HTML path (the `.d` is written alongside) | `<repo>_dependency_graph.html` |
| `--title TEXT` | page title | script default |
| `--root PREFIX` | override the analyzed root prefix | auto (common prefix) |
| `--ocamlpath DIR` | extra `OCAMLPATH` dir for `rocq dep`; repeatable | auto: plugin dirs are detected |
| `--project-file NAME` | project file name in each package | `_RocqProject`, then `_CoqProject` |
| `--fresh` | always run `rocq dep`, ignore cached coqdep files | off |

`--group` and `--ref` are mutually exclusive. With neither, every top-level
folder is colored on its own.

## How the dependency data is obtained

For each package the tool needs its coqdep output. Per package it either:

- **reuses a cached `.Makefile.*.d`** if the package directory contains exactly
  one such file (fast; no build or `rocq` needed), or
- **runs `rocq dep` fresh** otherwise — i.e. when there is no cached file, when
  there are several (ambiguous), or when you pass `--fresh`.

It always runs **per package** (never one global `coqdep` over everything):
sibling packages can define modules with the same short name (MetaRocq's
`quotation` copies `utils`' `MRCompare`), and a global load path would
mis-resolve those and invent wrong edges.

## Examples / setup

The script directory can live **anywhere** — beside the repos, or inside one of
them. `--repo` is auto-detected either way; the examples show both.

### stdlib — script outside the repo (sibling directory)

Layout `…/Projects/{dependency_script, stdlib}`. Run from `dependency_script/`:

```bash
python3 gen_graph.py --repo ../stdlib --lib theories \
  --group "Core:Init,ssr,ssrmatching,Program" \
  --group "Logic:Logic,Bool,Classes,Relations,Setoids" \
  --group "Data:Lists,Vectors,Streams,Strings,Unicode,Sorting" \
  --group "Arith:Arith,PArith,BinNums,NArith,ZArith,QArith" \
  --group "Numbers:Numbers,Zmod,Reals,Floats" \
  --group "Tactics:micromega,setoid_ring,btauto,rtauto,nsatz,omega" \
  --group "SetsMaps:Sets,FSets,MSets,Structures" \
  --group "Misc:extraction,funind,derive,Compat,Array,Wellfounded" \
  --title "Stdlib theories/ dependency graph" \
  -o stdlib_dependency_graph.html
```

The stdlib has one package (`theories/`, with `-R . Stdlib`) and ships a cached
`theories/.Makefile.coq.d`, so this runs with no build and no `rocq`. Its ~40
top-level folders are folded into 8 semantic `--group`s.

### stdlib — script inside the repo

If you drop this directory into the repo as `stdlib/dependency_script/`, run
from the repo root and omit `--repo` (it is found via the script's location):

```bash
cd /path/to/stdlib
python3 dependency_script/gen_graph.py --lib theories \
  --group "Arith:Arith,PArith,BinNums,NArith,ZArith,QArith" \
  … -o dependency_script/stdlib_dependency_graph.html
```

### MetaRocq — script outside the repo (sibling directory)

Layout `…/Projects/{dependency_script, metacoq}`. Run from `dependency_script/`:

```bash
python3 gen_graph.py --repo ../metacoq \
  --lib utils common template-rocq template-pcuic pcuic \
        safechecker safechecker-plugin erasure erasure-plugin \
        quotation translations \
  --group "Utils:utils" \
  --group "Common:common" \
  --group "Template:template-rocq,template-pcuic" \
  --group "PCUIC:pcuic" \
  --group "SafeChecker:safechecker,safechecker-plugin" \
  --group "Erasure:erasure,erasure-plugin" \
  --group "Quotation:quotation" \
  --group "Translations:translations" \
  --title "MetaRocq dependency graph" \
  -o metarocq_dependency_graph.html
```

MetaRocq's packages without a single cached coqdep file are scanned fresh, so
its OCaml plugins must be built first: `./configure.sh local && make` in the
repo. The three plugin directories are added to `OCAMLPATH` automatically — you
do not pass `--ocamlpath`. This is exactly what `gen.sh` runs.

### MetaRocq — script inside the repo

Same as above but placed as `metacoq/dependency_script/`; run from the repo
root and omit `--repo`:

```bash
cd /path/to/metacoq
python3 dependency_script/gen_graph.py \
  --lib utils common template-rocq template-pcuic pcuic \
        safechecker safechecker-plugin erasure erasure-plugin \
        quotation translations \
  --group "Utils:utils" --group "Common:common" \
  … -o dependency_script/metarocq_dependency_graph.html
```

### Color one package by its subfolders

Instead of coloring MetaRocq by package, spotlight a single package's internal
structure (its subfolders shaded from one hue):

```bash
python3 gen_graph.py --repo ../metacoq --lib pcuic --ref pcuic \
  -o pcuic_internal.html
# folders: pcuic/Syntax, pcuic/Typing, pcuic/Conversion, pcuic/Bidirectional, …
```

## Troubleshooting

- **`rocq dep` failed … Declare ML Module / OCAMLPATH** — a scanned package
  loads an OCaml plugin that is not built or not found. Build the project
  (MetaRocq: `./configure.sh local && make`) and/or pass the plugin directory
  with `--ocamlpath DIR` (relative to `--repo`).
- **`the dot and unflatten executables are required`** — install Graphviz
  (`sudo apt install graphviz`).
- **Empty graph / "no .vo rules"** — check `--lib` names a real package
  directory containing a `_RocqProject`/`_CoqProject`, and that `--root` (if you
  set it) matches the node paths.
- **Everything is gray / one color** — you have more folders than the 8 palette
  slots, or your `--group`/`--ref` folder names don't match the actual folders.
  The run prints the folders and their file counts; match those names.
- **A dependency looks missing** — a cross-package edge only appears if *both*
  packages are in `--lib`; edges to packages outside `--lib` (and to the Rocq
  standard library) are intentionally dropped.

---

## Advanced: the underlying scripts

`gen_graph.py` orchestrates two lower-level scripts you can also run directly on
an existing coqdep `.d` file.

### `dependency_graph_dot.py` — Graphviz (DOT) output

Computes the graph and emits plain DOT (no dependencies beyond Python). Also
the library `gen_graph.py` and the HTML script build on (coqdep parsing, path
contraction, transitive reduction, DOT emission).

```bash
python3 dependency_graph_dot.py -i some/.Makefile.coq.d --root "" > graph.dot
dot -Tsvg graph.dot -o graph.svg
```

| Option | Meaning | Default |
|---|---|---|
| `-i FILE` | coqdep dependency file | `verified-ocaml/.Makefile.coq.d` |
| `-o FILE` | output DOT file (`-` = stdout) | stdout |
| `--hide FOLDER` | hide a top-level folder (paths through it are **contracted**, not dropped); repeatable | none |
| `--root PREFIX` | analyzed subtree | `auto/` |
| `--no-disk-check` | skip reconciling the `.d` against `.v` files on disk | off |

Edges are **transitively reduced**: an arrow implied by a longer path is not
drawn. Hiding a folder contracts paths through its files so reachability is
preserved.

### `dependency_graph_html.py` — interactive HTML page

Renders the graph as the self-contained HTML page described above. Requires
Graphviz. `gen_graph.py` calls it after building the unified `.d`; call it
directly when you already have a repo-relative coqdep file.

| Option | Meaning | Default |
|---|---|---|
| `-i FILE` | coqdep dependency file | `verified-ocaml/.Makefile.coq.d` |
| `-o FILE` | output HTML file | `docs/auto_dependency_graph.html` |
| `--ref FOLDER` | reference folder (subfolders shaded); repeatable | top-level folders |
| `--group NAME:F1,F2,…` | named group of folders (members shaded); repeatable; mutually exclusive with `--ref` | none |
| `--title TITLE` | page title | `auto/ Coq dependency graph` |
| `--root PREFIX` | analyzed subtree | `auto/` |
| `--no-disk-check` | skip the on-disk `.v` reconciliation | off |

Coloring detail: each `--ref`/`--group` takes the next palette hue in the order
given (blue, yellow, pink, green, violet, orange, aqua, red; then gray).
Subfolders/members take lightness shades of that hue (darkest first). Files
under no reference/group form the gray "Other". Dark mode is automatic. The
layout is computed once — unchecking a legend group dims its files in place
without re-flowing the graph (use `dependency_graph_dot.py --hide` to actually
contract paths through a folder).
