# MetaRocq interactive HTML dependency graph

This folder holds a generator for an **interactive HTML dependency graph** of the
MetaRocq packages, and the graph it produces. It supersedes the static
`.dot/.svg/.png` graph in `../dependency-graph/`.

- `metarocq_dependency_graph.html` — the generated graph (open in a browser:
  pan/zoom, name search, click a node to highlight its dependency cone, a legend
  that dims groups, a data table, light/dark mode). Regenerated automatically on
  every push to `main` by `.github/workflows/dependency_graph_html.yml`.
- `gen_graph.py`, `dependency_graph_html.py`, `dependency_graph_dot.py` — the
  generator (pure Python; the HTML render shells out to Graphviz).
- `README_dependency_graph.md` — full documentation of the generator and options.

## Regenerating by hand

Requirements: Python 3, Graphviz (`dot`, `unflatten`), and `rocq` on `PATH`. The
graph is built by `coqdep` (a source scanner) — **no compilation is needed** — but
each package's generated `_RocqProject` must exist, so configure the repo first:

```
./configure.sh local
# regenerate the generated _RocqProject files (utils ships a static one)
for d in common template-rocq template-pcuic pcuic \
         safechecker safechecker-plugin erasure erasure-plugin \
         quotation translations; do make -C "$d" _RocqProject; done

python3 dependency_graph_html/gen_graph.py --repo . --fresh \
  --lib utils common template-rocq template-pcuic pcuic \
        safechecker safechecker-plugin erasure erasure-plugin \
        quotation translations \
  --title "MetaRocq dependency graph" \
  -o dependency_graph_html/metarocq_dependency_graph.html \
  --group "Utils:utils" --group "Common:common" \
  --group "Template:template-rocq,template-pcuic" --group "PCUIC:pcuic" \
  --group "SafeChecker:safechecker,safechecker-plugin" \
  --group "Erasure:erasure,erasure-plugin" \
  --group "Quotation:quotation" --group "Translations:translations"
```

See `README_dependency_graph.md` for the full option reference (coloring by
`--group`/`--ref`, single-package repos, etc.).
