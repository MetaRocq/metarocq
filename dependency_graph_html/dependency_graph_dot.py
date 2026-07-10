#!/usr/bin/env python3
"""Compute the Graphviz (DOT) input for the intra-auto/ Coq dependency graph.

Parses the coqdep output verified-ocaml/.Makefile.coq.d, keeps the .vo rules
for files under auto/ and their dependencies on other auto/ files, and emits a
transitively reduced DOT graph (an arrow implied by a longer path is not
drawn, with a reachability check that the reduction is faithful).

Folders can be hidden with --hide; hiding contracts dependency paths that run
through the hidden files instead of dropping them, so A -> B survives iff a
dependency path A -> ... -> B exists whose intermediate nodes are all hidden.

Runs standalone (writes DOT to stdout or -o) and doubles as the library used
by dependency_graph_html.py, which supplies node colors via the `attrs`
callback of to_dot().
"""

import argparse
import sys
from pathlib import Path

ROOT = "auto/"
MAX_LABEL = 46


def folder_of(path, root=ROOT):
    """Main folder of a node: first path component under the root, or
    "(root)" for files sitting directly in it."""
    parts = path[len(root):].split("/")
    return parts[0] if len(parts) > 1 else "(root)"


def subfolder_of(path, root=ROOT):
    """Sub-cluster of a node: "Folder/Sub" for files at depth >= 2 (deeper
    nesting collapses into the depth-2 subfolder), "Folder" for files
    directly in a main folder, "(root)" at the root."""
    parts = path[len(root):].split("/")
    if len(parts) > 2:
        return parts[0] + "/" + parts[1]
    return folder_of(path, root)


def parse_coqdep(dep_file, root=ROOT):
    """Return {node .v path: sorted [dep .v path]} for files under root.

    Each coqdep rule is a single line "T1 T2 ...: D1 D2 ..." where the
    targets include X.vo, X.glob, X.v.beautified, and X.required_vo (a
    parallel .vos rule exists per file and is skipped).  Dependencies are
    kept only when they are .vo files under the root.
    """
    deps = {}
    for line in dep_file.read_text(encoding="utf-8").splitlines():
        tokens = line.split()
        try:
            colon = next(i for i, t in enumerate(tokens) if t.endswith(":"))
        except StopIteration:
            continue
        targets = [t.rstrip(":") for t in tokens[: colon + 1]]
        if not targets or not targets[0].endswith(".vo"):
            continue
        node = targets[0][: -len(".vo")] + ".v"
        if not node.startswith(root):
            continue
        node_deps = sorted(
            t[: -len(".vo")] + ".v"
            for t in tokens[colon + 1:]
            if t.endswith(".vo") and t.startswith(root)
            and t != targets[0]
        )
        deps[node] = node_deps
    return deps


def check_against_disk(deps, src_dir, root=ROOT):
    """Warn when the coqdep data and the .v files on disk disagree."""
    on_disk = {
        root + p.relative_to(src_dir).as_posix()
        for p in src_dir.rglob("*.v")
    }
    stale = sorted(set(deps) - on_disk)
    missing = sorted(on_disk - set(deps))
    for path in stale:
        print(f"warning: {path} has a coqdep rule but is not on disk "
              f"(stale .Makefile.coq.d?)", file=sys.stderr)
    for path in missing:
        print(f"warning: {path} is on disk but has no coqdep rule; "
              f"added as an isolated node (stale .Makefile.coq.d?)",
              file=sys.stderr)
        deps[path] = []
    for path in stale:
        del deps[path]
    for node in deps:
        deps[node] = [d for d in deps[node] if d in deps]


def load_graph(dep_file, root=ROOT, disk_check=True):
    """Parse coqdep output, reconcile with the files on disk, and return
    {node: set(deps)}.

    With disk_check=False the on-disk reconciliation is skipped (useful when
    the .d file lives outside the analyzed subtree, or spans several roots via
    root=""); the graph is still closed by dropping deps that have no rule of
    their own, which check_against_disk would otherwise do."""
    deps = parse_coqdep(dep_file, root)
    if not deps:
        sys.exit(f"error: no {root} .vo rules parsed from {dep_file}")
    if disk_check:
        check_against_disk(deps, dep_file.parent / root.rstrip("/"), root)
    else:
        for node in deps:
            deps[node] = [d for d in deps[node] if d in deps]
    return {n: set(ds) for n, ds in deps.items()}


def project_edges(deps, visible):
    """Restrict the graph to `visible`, contracting paths through hidden
    nodes: A -> B survives iff a dependency path A -> ... -> B exists whose
    intermediate nodes are all hidden."""
    proj = {}
    for node in visible:
        frontier, seen = set(), set()
        stack = list(deps[node])
        while stack:
            d = stack.pop()
            if d in seen:
                continue
            seen.add(d)
            if d in visible:
                frontier.add(d)
            else:
                stack.extend(deps[d])
        proj[node] = frontier
    return proj


def topo_order(deps):
    """Nodes ordered so that every dependency precedes its dependents."""
    order, state = [], {}

    def visit(node):
        stack = [(node, iter(deps[node]))]
        while stack:
            n, it = stack[-1]
            if state.get(n) == 2:
                stack.pop()
                continue
            state[n] = 1
            for d in it:
                if state.get(d) == 1:
                    sys.exit(f"error: dependency cycle through {d}")
                if state.get(d) != 2:
                    stack.append((d, iter(deps[d])))
                    break
            else:
                state[n] = 2
                order.append(n)
                stack.pop()

    for node in deps:
        if state.get(node) != 2:
            visit(node)
    return order


def transitive_reduction(deps):
    """Drop every edge implied by a longer path; verify reachability is
    unchanged.  Descendant sets are bitmasks over the topological order."""
    order = topo_order(deps)
    bit = {n: 1 << i for i, n in enumerate(order)}
    closure = {}
    for n in order:
        mask = 0
        for d in deps[n]:
            mask |= bit[d] | closure[d]
        closure[n] = mask
    reduced = {}
    for n in order:
        direct = deps[n]
        reduced[n] = {
            d for d in direct
            if not any(bit[d] & closure[o] for o in direct if o is not d)
        }
    check = {}
    for n in order:
        mask = 0
        for d in reduced[n]:
            mask |= bit[d] | check[d]
        check[n] = mask
        assert check[n] == closure[n], f"reduction changed reachability at {n}"
    return reduced


def reduced_edges(deps, visible=None):
    """Project the graph onto `visible` (default: everything), transitively
    reduce, and return a sorted [(dep, dependent)] edge list."""
    if visible is None:
        visible = set(deps)
    proj = project_edges(deps, visible)
    reduced = transitive_reduction(proj)
    return [(d, n) for n, ds in sorted(reduced.items()) for d in sorted(ds)]


def display_name(path):
    stem = Path(path).stem
    label = stem.replace("CompressRoundtrip", "CR.")
    if len(label) > MAX_LABEL:
        label = label[: MAX_LABEL - 16] + "…" + label[-15:]
    return label


def to_dot(nodes, edges, attrs=None):
    """Render nodes/edges as a DOT digraph.  `attrs` maps a node path to a
    dict of extra Graphviz node attributes (fill and font colors, class);
    every node always gets its display label."""
    lines = [
        "digraph auto {",
        '  rankdir=TB;',
        '  bgcolor="transparent";',
        '  node [shape=ellipse, style=filled, fontname="Helvetica",'
        ' fontsize=10, penwidth=0, fillcolor="#c3c2b7"];',
        '  edge [color="#898781", arrowsize=0.6];',
    ]
    for n in sorted(nodes):
        extra = attrs(n) if attrs else {}
        pairs = "".join(f', {k}="{v}"' for k, v in extra.items())
        lines.append(f'  "{n}" [label="{display_name(n)}"{pairs}];')
    for a, b in sorted(edges):
        lines.append(f'  "{a}" -> "{b}";')
    lines.append("}")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("-i", "--input", default="verified-ocaml/.Makefile.coq.d",
                    help="coqdep dependency file "
                         "(default: verified-ocaml/.Makefile.coq.d)")
    ap.add_argument("-o", "--output", default="-",
                    help="output DOT file (default: stdout)")
    ap.add_argument("--hide", action="append", default=[], metavar="FOLDER",
                    help="hide a main folder (e.g. Examples/Generated hides "
                         "nothing: use the first-level name, e.g. Bytecode); "
                         "repeatable; paths through hidden files are "
                         "contracted, not dropped")
    ap.add_argument("--root", default=ROOT,
                    help=f"path prefix of the analyzed library "
                         f"(default: {ROOT})")
    ap.add_argument("--no-disk-check", action="store_true",
                    help="skip reconciling the .d file against the .v files on "
                         "disk (use when the .d lives outside the analyzed "
                         "subtree or spans several roots via --root \"\")")
    args = ap.parse_args()

    dep_file = Path(args.input)
    if not dep_file.exists():
        sys.exit(f"error: {dep_file} not found; run 'make Makefile.coq' in "
                 f"verified-ocaml/ to regenerate coqdep output")
    deps = load_graph(dep_file, args.root, disk_check=not args.no_disk_check)

    folders = {folder_of(n, args.root) for n in deps}
    unknown = set(args.hide) - folders
    if unknown:
        sys.exit(f"error: unknown folder(s) {sorted(unknown)}; "
                 f"available: {sorted(folders)}")
    visible = {n for n in deps if folder_of(n, args.root) not in args.hide}

    edges = reduced_edges(deps, visible)
    dot = to_dot(visible, edges)
    if args.output == "-":
        print(dot)
    else:
        Path(args.output).write_text(dot + "\n", encoding="utf-8")
    direct = sum(len(project_edges(deps, visible)[n]) for n in visible)
    print(f"{len(visible)} nodes, {direct} direct/contracted edges "
          f"-> {len(edges)} after transitive reduction", file=sys.stderr)


if __name__ == "__main__":
    main()
