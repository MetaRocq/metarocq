#!/usr/bin/env python3
"""Generate an interactive dependency-graph HTML page for any Rocq repo.

This is the entry point.  It works both for a multi-package library (several
sibling package directories, each with its own `_RocqProject`, e.g. MetaRocq)
and for a single-package one (a lone `_CoqProject`, e.g. the Rocq stdlib).

You name the packages with `--lib` and the folders to color with
`--group`/`--ref`; everything else is auto-detected.  The driver:

  1. reads each package's `_RocqProject`/`_CoqProject` load paths (`-R`/`-Q`),
  2. gets that package's coqdep output -- reusing a cached `.Makefile.*.d`
     when there is exactly one, else running `rocq dep` fresh (per package, so
     shared short module names never mis-resolve as a global run would),
  3. rewrites every `.vo` path to a repo-relative form keyed by the package
     directory, dropping the package's own source subdir (usually `theories`)
     so the meaningful subfolders (PCUIC/Syntax, Bool, ...) surface directly,
  4. concatenates them into one coqdep file and auto-computes the analyzed
     root (the common path prefix of all nodes), then
  5. hands off to dependency_graph_html.py to color and render the page.

The tool never compiles Rocq code: it only scans sources (or reuses cached
coqdep output).  The one build prerequisite is that OCaml *plugins* a package
loads via `Declare ML Module` must already be built, and only when that
package is scanned fresh -- their directories are put on OCAMLPATH
automatically (see --ocamlpath).

Requires: Python 3, Graphviz (`dot`, `unflatten`) for the render, and `rocq`
on PATH whenever a package is scanned fresh.
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
HTML_SCRIPT = SCRIPT_DIR / "dependency_graph_html.py"
PROJECT_FILES = ["_RocqProject", "_CoqProject"]


# ---------------------------------------------------------------------------
# Project files: load paths (-R/-Q) and OCaml include dirs (-I)
# ---------------------------------------------------------------------------

def find_project_file(lib_dir, override):
    """Return the path to lib_dir's project file (override name, else the
    first of _RocqProject / _CoqProject that exists)."""
    names = [override] if override else PROJECT_FILES
    for name in names:
        p = lib_dir / name
        if p.is_file():
            return p
    sys.exit(f"error: no project file ({' or '.join(names)}) in {lib_dir}")


def parse_load_paths(proj_file):
    """Parse a _RocqProject/_CoqProject.

    Returns (rq, idirs): `rq` is a list of (physical_dir, logical_name) from
    every `-R`/`-Q` entry (several may share a line, as MetaRocq does);
    `idirs` is the list of `-I` physical dirs.  Comments, blank lines,
    `-arg X`, and the `.v` file listing are skipped.
    """
    rq, idirs = [], []
    for line in proj_file.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        toks = line.split()
        i = 0
        while i < len(toks):
            t = toks[i]
            if t in ("-R", "-Q") and i + 3 <= len(toks):
                rq.append((toks[i + 1], toks[i + 2]))
                i += 3
            elif t == "-I" and i + 2 <= len(toks):
                idirs.append(toks[i + 1])
                i += 2
            elif t == "-arg" and i + 2 <= len(toks):
                i += 2
            else:
                i += 1
    return rq, idirs


def build_registry(repo, libs, proj_override):
    """Build the source-root registry used to rewrite coqdep paths, plus the
    set of OCaml include dirs.

    Registry entries are (absolute source dir, package dir) for each package's
    *own* `-R`/`-Q` lines (those resolving inside the package).  A package's
    cross-references to another package resolve against that other package's
    own entry, so the mapping is owner-defined and consistent.  Entries are
    sorted longest-first so the most specific source root wins.
    """
    registry, idirs = [], []
    for d in libs:
        lib_dir = repo / d
        lib_abs = os.path.normpath(str(lib_dir))
        proj = find_project_file(lib_dir, proj_override)
        rq, ids = parse_load_paths(proj)
        for phys, _logical in rq:
            src_abs = os.path.normpath(str(lib_dir / phys))
            if src_abs == lib_abs or src_abs.startswith(lib_abs + os.sep):
                registry.append((src_abs, d))
        for phys in ids:
            idirs.append(os.path.normpath(str(lib_dir / phys)))
    registry = sorted(set(registry), key=lambda e: -e[0].count(os.sep))
    return registry, sorted(set(idirs))


# ---------------------------------------------------------------------------
# Coqdep path rewriting
# ---------------------------------------------------------------------------

def rewrite_token(token, lib_abs, registry):
    """Rewrite one coqdep token.  A `.vo` path (relative to the package the
    coqdep ran in) becomes `<pkg dir>/<path under its source root>`; the
    trailing rule colon is preserved.  Non-`.vo` tokens (`.glob`, `.v`,
    absolute plugin/runtime paths) and `.vo` paths outside every registered
    source root are returned unchanged (the latter are dropped downstream)."""
    core, colon = (token[:-1], ":") if token.endswith(":") else (token, "")
    if not core.endswith(".vo"):
        return token
    t_abs = os.path.normpath(os.path.join(lib_abs, core))
    for src_abs, pkg in registry:
        if t_abs == src_abs or t_abs.startswith(src_abs + os.sep):
            rel = os.path.relpath(t_abs, src_abs).replace(os.sep, "/")
            return f"{pkg}/{rel}{colon}"
    return token


def rewrite_dep_text(text, lib_abs, registry, targets):
    """Rewrite a whole coqdep output for one package; append every rewritten
    rule target (the token before the first colon) to `targets`."""
    out = []
    for line in text.splitlines():
        toks = line.split()
        if not toks:
            out.append(line)
            continue
        rewritten = [rewrite_token(t, lib_abs, registry) for t in toks]
        out.append(" ".join(rewritten))
        first = rewritten[0]
        if first.endswith(".vo:") or first.endswith(".vo"):
            targets.append(first.rstrip(":")[: -len(".vo")] + ".v")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Coqdep source: cached .d or a fresh `rocq dep` run
# ---------------------------------------------------------------------------

def coqdep_output(repo, d, proj_override, fresh, ocamlpath):
    """Return (text, note) for package `d`: reuse the sole cached
    `.Makefile.*.d` if present and not `--fresh`, otherwise run `rocq dep`."""
    lib_dir = repo / d
    if not fresh:
        cached = sorted(lib_dir.glob(".Makefile.*.d"))
        if len(cached) == 1:
            return cached[0].read_text(encoding="utf-8"), f"cached {cached[0].name}"
    proj = find_project_file(lib_dir, proj_override)
    env = dict(os.environ)
    if ocamlpath:
        env["OCAMLPATH"] = ocamlpath
    proc = subprocess.run(
        ["rocq", "dep", "-f", proj.name],
        cwd=str(lib_dir), env=env, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        sys.exit(
            f"error: `rocq dep` failed in {lib_dir} (exit {proc.returncode}).\n"
            f"If this package loads an OCaml plugin (Declare ML Module), the "
            f"plugin must be built and on OCAMLPATH; pass --ocamlpath DIR or "
            f"build the project first.\n--- rocq dep stderr ---\n{proc.stderr}"
        )
    return proc.stdout, "fresh rocq dep"


# ---------------------------------------------------------------------------
# Auto-detection: repo root, OCAMLPATH, analyzed root
# ---------------------------------------------------------------------------

def resolve_repo(explicit, libs):
    """Locate the repo root: the explicit value, else the current directory if
    it contains all --lib dirs, else this script's parent directory (the
    "script lives inside the repo" layout)."""
    if explicit:
        return Path(explicit).resolve()
    for cand in (Path.cwd(), SCRIPT_DIR.parent):
        if all((cand / d).is_dir() for d in libs):
            return cand.resolve()
    sys.exit("error: could not auto-detect the repo root; pass --repo PATH "
             "(the directory containing the --lib packages)")


def _looks_like_plugin_dir(path):
    """True if `path` holds a built findlib plugin (a META file or a .cmxs)."""
    if not path.is_dir():
        return False
    for entry in path.iterdir():
        n = entry.name
        if n == "META" or n.startswith("META.") or n.endswith(".cmxs"):
            return True
    return False


def auto_ocamlpath(repo, libs, idirs, extra):
    """Assemble OCAMLPATH so `rocq dep` can resolve `Declare ML Module`:
    the packages' `-I` dirs, plus any `<pkg>`, `<pkg>/src`, `<pkg>/gen-src`
    holding a built plugin, plus user `--ocamlpath` dirs; then the inherited
    OCAMLPATH.  Only existing directories are kept."""
    dirs = []
    for d in extra:
        dirs.append(os.path.normpath(str((repo / d))))
    dirs.extend(idirs)
    for d in libs:
        for sub in ("", "src", "gen-src"):
            p = repo / d / sub if sub else repo / d
            if _looks_like_plugin_dir(p):
                dirs.append(os.path.normpath(str(p)))
    seen, ordered = set(), []
    for p in dirs:
        if p not in seen and os.path.isdir(p):
            seen.add(p)
            ordered.append(p)
    inherited = os.environ.get("OCAMLPATH", "")
    if inherited:
        ordered.append(inherited)
    return os.pathsep.join(ordered)


def auto_root(targets):
    """Analyzed root = common path prefix of all node dirs, with a trailing
    slash (or "" when they share none), so dependency_graph_dot.folder_of
    strips it to expose the meaningful top-level folders."""
    dirs = [os.path.dirname(t) for t in targets if os.path.dirname(t)]
    if not dirs:
        return ""
    common = os.path.commonpath(dirs).replace(os.sep, "/")
    return common + "/" if common else ""


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--lib", nargs="+", required=True, metavar="DIR",
                    help="package directories (relative to --repo), each with "
                         "a _RocqProject/_CoqProject; repeatable")
    ap.add_argument("--repo", default=None,
                    help="repo root (auto: current dir, else this script's "
                         "parent, whichever contains the --lib dirs)")
    ap.add_argument("--ocamlpath", action="append", default=[], metavar="DIR",
                    help="extra dir (relative to --repo) for OCAMLPATH when "
                         "running `rocq dep`; plugin dirs are auto-detected, "
                         "this only supplements them; repeatable")
    ap.add_argument("--project-file", default=None, metavar="NAME",
                    help="project file name to use in every package "
                         "(default: _RocqProject then _CoqProject)")
    ap.add_argument("--ref", action="append", default=[], metavar="FOLDER",
                    help="reference folder to color, its subfolders shaded "
                         "(passed to the renderer); repeatable")
    ap.add_argument("--group", action="append", default=[],
                    metavar="NAME:F1,F2,...",
                    help="named group of folders sharing a hue, members "
                         "shaded (passed to the renderer); repeatable")
    ap.add_argument("--root", default=None,
                    help="override the auto-computed analyzed root prefix")
    ap.add_argument("--title", default=None, help="page title")
    ap.add_argument("-o", "--output", default=None,
                    help="output HTML file (default: <repo>_dependency_graph.html)")
    ap.add_argument("--fresh", action="store_true",
                    help="always run `rocq dep`, ignoring cached .Makefile.*.d")
    args = ap.parse_args()

    repo = resolve_repo(args.repo, args.lib)
    for d in args.lib:
        if not (repo / d).is_dir():
            sys.exit(f"error: --lib {d} is not a directory under {repo}")
    print(f"repo: {repo}", file=sys.stderr)

    registry, idirs = build_registry(repo, args.lib, args.project_file)
    ocamlpath = auto_ocamlpath(repo, args.lib, idirs, args.ocamlpath)

    output = Path(args.output) if args.output \
        else Path.cwd() / f"{repo.name}_dependency_graph.html"
    dep_file = output.with_suffix(".d")

    targets, chunks = [], []
    for d in args.lib:
        text, note = coqdep_output(repo, d, args.project_file, args.fresh,
                                   ocamlpath)
        lib_abs = os.path.normpath(str(repo / d))
        chunks.append(rewrite_dep_text(text, lib_abs, registry, targets))
        print(f"  {d}: {note}", file=sys.stderr)
    if not targets:
        sys.exit("error: no .vo rules found in any package")
    dep_file.write_text("\n".join(chunks) + "\n", encoding="utf-8")
    print(f"wrote {dep_file} ({len(targets)} files from {len(args.lib)} "
          f"package(s))", file=sys.stderr)

    root = args.root if args.root is not None else auto_root(targets)
    print(f"analyzed root: {root!r}", file=sys.stderr)

    cmd = [sys.executable, str(HTML_SCRIPT), "-i", str(dep_file),
           "--root", root, "--no-disk-check", "-o", str(output)]
    if args.title:
        cmd += ["--title", args.title]
    for r in args.ref:
        cmd += ["--ref", r]
    for g in args.group:
        cmd += ["--group", g]
    subprocess.run(cmd, check=True)


if __name__ == "__main__":
    main()
