#!/usr/bin/env python3
"""Render the intra-auto/ Coq dependency graph as a self-contained HTML page.

Builds on dependency_graph_dot.py (coqdep parsing, path contraction,
transitive reduction, DOT emission) and adds the interactive UI: pan/zoom,
name search, click-to-highlight dependency cones, a legend, and a data table.

Coloring is driven by *reference folders* passed with --ref (default: the
top-level folders under auto/).  Each reference folder takes the next slot
of a validated categorical palette, in the order given (fixed order, never
cycled; references beyond the 8 slots fold into a neutral gray).  Its
immediate subfolders each take a strong lightness shade of that hue,
computed in OKLCH inside each color scheme's lightness band, darkest for
the folder's own files.  Files under no reference folder are drawn in a
neutral gray "Other" group.  Every legend group — and each folder inside
it — is togglable: unchecking dims its files and their edges in place on
the single pre-rendered layout.

Requires the `dot` and `unflatten` executables (apt install graphviz).
"""

import argparse
import datetime
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dependency_graph_dot as core

# Validated categorical palette (reference instance of the dataviz method);
# the dark column is the same hues re-stepped for the dark surface.
# Reference folders take slots in the order they are given; the slot order
# spreads hue families apart (blue, yellow, pink, green, ...) so a handful
# of references never lands on two hues of the same family.
LIGHT_SLOTS = ["#2a78d6", "#eda100", "#e87ba4", "#008300",
               "#4a3aa7", "#eb6834", "#1baf7a", "#e34948"]
DARK_SLOTS = ["#3987e5", "#c98500", "#d55181", "#008300",
              "#9085e9", "#d95926", "#199e70", "#e66767"]
GRAY_LIGHT, GRAY_DARK = "#8a8a84", "#8a8a84"  # overflow beyond 8 references
NEUTRAL_LIGHT, NEUTRAL_DARK = "#c3c2b7", "#52514e"  # the "Other" group

LIGHT_SURFACE, DARK_SURFACE = "#fcfcfb", "#1a1a19"
# OKLCH lightness bands per scheme (categorical marks stay inside them).
# Bands sit high so most fills take dark ink: nodes carry text labels, so
# fills are kept soft (see MAX_CHROMA) and the label is the foreground.
LIGHT_BAND, DARK_BAND = (0.62, 0.92), (0.50, 0.75)
MAX_CHROMA = 0.09  # cap on fill chroma; full-chroma fills drown the labels
SHADE_STEP = 0.13  # target OKLCH delta-L between sibling subfolder shades
SHADE_FLOOR = 0.08  # warn when siblings squeeze the delta-L below this


# ---------------------------------------------------------------------------
# Color math: sRGB <-> OKLCH, WCAG contrast
# ---------------------------------------------------------------------------

def _hex_to_rgb(h):
    return tuple(int(h[i:i + 2], 16) / 255 for i in (1, 3, 5))


def _rgb_to_hex(rgb):
    return "#" + "".join(f"{round(max(0.0, min(1.0, c)) * 255):02x}"
                         for c in rgb)


def _srgb_to_linear(c):
    return c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4


def _linear_to_srgb(c):
    c = max(0.0, c)
    return 12.92 * c if c <= 0.0031308 else 1.055 * c ** (1 / 2.4) - 0.055


def _rgb_to_oklab(rgb):
    r, g, b = (_srgb_to_linear(c) for c in rgb)
    l = 0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b
    m = 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b
    s = 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b
    l, m, s = l ** (1 / 3), m ** (1 / 3), s ** (1 / 3)
    return (0.2104542553 * l + 0.7936177850 * m - 0.0040720468 * s,
            1.9779984951 * l - 2.4285922050 * m + 0.4505937099 * s,
            0.0259040371 * l + 0.7827717662 * m - 0.8086757660 * s)


def _oklab_to_rgb(lab):
    L, a, b = lab
    l = (L + 0.3963377774 * a + 0.2158037573 * b) ** 3
    m = (L - 0.1055613458 * a - 0.0638541728 * b) ** 3
    s = (L - 0.0894841775 * a - 1.2914855480 * b) ** 3
    return (_linear_to_srgb(4.0767416621 * l - 3.3077115913 * m
                            + 0.2309699292 * s),
            _linear_to_srgb(-1.2684380046 * l + 2.6097574011 * m
                            - 0.3413193965 * s),
            _linear_to_srgb(-0.0041960863 * l - 0.7034186147 * m
                            + 1.7076147010 * s))


def shade(hex_color, target_l):
    """The same hue at OKLCH lightness `target_l`, chroma capped at
    MAX_CHROMA and reduced further only as far as needed to stay inside
    the sRGB gamut."""
    L, a, b = _rgb_to_oklab(_hex_to_rgb(hex_color))
    raw = (a * a + b * b) ** 0.5
    if raw < 1e-9:
        return _rgb_to_hex(_oklab_to_rgb((target_l, 0, 0)))
    chroma = min(raw, MAX_CHROMA)
    ua, ub = a / raw, b / raw
    for _ in range(24):
        rgb = _oklab_to_rgb((target_l, ua * chroma, ub * chroma))
        if all(-1e-4 <= c <= 1 + 1e-4 for c in rgb):
            return _rgb_to_hex(rgb)
        chroma *= 0.9
    return _rgb_to_hex(_oklab_to_rgb((target_l, 0, 0)))


def _rel_lum(hex_color):
    r, g, b = (_srgb_to_linear(c) for c in _hex_to_rgb(hex_color))
    return 0.2126 * r + 0.7152 * g + 0.0722 * b


def contrast(a, b):
    la, lb = sorted((_rel_lum(a), _rel_lum(b)), reverse=True)
    return (la + 0.05) / (lb + 0.05)


def ink_on(fill):
    """Text color for a filled node: whichever ink contrasts more."""
    return max(("#0b0b0b", "#ffffff"), key=lambda ink: contrast(fill, ink))


def shade_ls(base_hex, count, band):
    """`count` monotone OKLCH lightness targets inside `band`, centered on
    the base color's own lightness."""
    lo, hi = band
    base_l = min(max(_rgb_to_oklab(_hex_to_rgb(base_hex))[0], lo), hi)
    if count == 1:
        return [base_l]
    step = min(SHADE_STEP, (hi - lo) / (count - 1))
    if step < SHADE_FLOOR:
        print(f"warning: {count} subfolder shades squeeze delta-L to "
              f"{step:.3f} (< {SHADE_FLOOR}); shades may be hard to tell "
              f"apart", file=sys.stderr)
    span = step * (count - 1)
    start = min(max(base_l - span / 2, lo), hi - span)
    return [start + i * step for i in range(count)]


# ---------------------------------------------------------------------------
# Folder discovery and cluster coloring
# ---------------------------------------------------------------------------

def _finish_clusters(deps, folders, clusters, cluster_index):
    """Shared tail of the cluster builders: collect the leftover nodes into
    the neutral "Other" group."""
    others = [n for n in deps if n not in cluster_index]
    if others:
        gi = len(clusters)
        clusters.append({
            "name": "Other", "short": "Other", "folder": "Other",
            "count": len(others),
            "light": NEUTRAL_LIGHT, "dark": NEUTRAL_DARK,
            "light_ink": ink_on(NEUTRAL_LIGHT),
            "dark_ink": ink_on(NEUTRAL_DARK),
        })
        for n in others:
            cluster_index[n] = gi
        folders.append({"name": "Other", "count": len(others),
                        "clusters": [gi]})

    return folders, clusters, cluster_index


def build_clusters(deps, root, refs):
    """Derive the color groups from the reference folders.

    `refs` are folder paths relative to the root, in CLI order (which fixes
    the palette slot order).  A node belongs to the deepest reference folder
    containing it; within a reference, its sub-cluster is the reference's
    immediate subfolder holding the node (deeper nesting collapses into it),
    or the reference itself for its direct files.  Nodes under no reference
    form a neutral "Other" group.

    Returns (folders, clusters, cluster_index) where `folders` is
    [{name, count, clusters: [gi]}] in slot order, `clusters` is
    [{name, short, folder, count, light, dark, light_ink, dark_ink}], and
    `cluster_index` maps a node path to its cluster gi.
    """
    if len(refs) > len(LIGHT_SLOTS):
        print(f"warning: {len(refs)} reference folders exceed the "
              f"{len(LIGHT_SLOTS)} palette slots; the overflow is drawn "
              f"gray", file=sys.stderr)
    by_depth = sorted(refs, key=lambda r: -r.count("/"))

    def ref_of(node):
        rel = node[len(root):]
        return next((r for r in by_depth if rel.startswith(r + "/")), None)

    def sub_of(node, ref):
        rest = node[len(root) + len(ref) + 1:]
        return ref + "/" + rest.split("/")[0] if "/" in rest else ref

    folders, clusters, cluster_index = [], [], {}
    for fi, ref in enumerate(refs):
        members = [n for n in deps if ref_of(n) == ref]
        if not members:
            sys.exit(f"error: reference folder {ref} contains no .v files "
                     f"(after deeper references claimed theirs)")
        subnames = sorted({sub_of(n, ref) for n in members})
        # The folder's own files come first, then subfolders; shades darken
        # to light along that order.
        subnames.sort(key=lambda s: (s != ref, s))
        in_palette = fi < len(LIGHT_SLOTS)
        base_light = LIGHT_SLOTS[fi] if in_palette else GRAY_LIGHT
        base_dark = DARK_SLOTS[fi] if in_palette else GRAY_DARK
        ls_light = shade_ls(base_light, len(subnames), LIGHT_BAND)
        ls_dark = shade_ls(base_dark, len(subnames), DARK_BAND)
        gis = []
        for si, sub in enumerate(subnames):
            light = shade(base_light, ls_light[si])
            dark = shade(base_dark, ls_dark[si])
            gi = len(clusters)
            clusters.append({
                "name": sub,
                "short": "(files)" if sub == ref else sub[len(ref) + 1:],
                "folder": ref,
                "count": sum(1 for n in members if sub_of(n, ref) == sub),
                "light": light, "dark": dark,
                "light_ink": ink_on(light), "dark_ink": ink_on(dark),
            })
            gis.append(gi)
            for n in members:
                if sub_of(n, ref) == sub:
                    cluster_index[n] = gi
        folders.append({"name": ref, "count": len(members),
                        "clusters": gis})

    return _finish_clusters(deps, folders, clusters, cluster_index)


def build_clusters_from_groups(deps, root, groups):
    """Derive the color groups from named groups of top-level folders.

    `groups` is [(name, [folder, ...])] in CLI order (which fixes the
    palette slot order).  Each group takes one hue; each member folder takes
    its own lightness shade of it, darkest first in the order given.  Nodes
    whose top-level folder is in no group form a neutral "Other" group.

    Returns the same (folders, clusters, cluster_index) shape as
    build_clusters, with the group as the legend/toggle unit and the member
    folder as the cluster.
    """
    if len(groups) > len(LIGHT_SLOTS):
        print(f"warning: {len(groups)} groups exceed the "
              f"{len(LIGHT_SLOTS)} palette slots; the overflow is drawn "
              f"gray", file=sys.stderr)
    seen = {}
    for name, members in groups:
        for m in members:
            if m in seen:
                sys.exit(f"error: folder {m} is listed in two groups "
                         f"({seen[m]} and {name})")
            seen[m] = name

    by_folder = {}
    for n in deps:
        by_folder.setdefault(core.folder_of(n, root), []).append(n)

    folders, clusters, cluster_index = [], [], {}
    for fi, (name, members) in enumerate(groups):
        empty = [m for m in members if not by_folder.get(m)]
        if empty:
            sys.exit(f"error: group {name}: folder(s) "
                     f"{', '.join(empty)} contain no .v files; available: "
                     f"{', '.join(sorted(by_folder))}")
        in_palette = fi < len(LIGHT_SLOTS)
        base_light = LIGHT_SLOTS[fi] if in_palette else GRAY_LIGHT
        base_dark = DARK_SLOTS[fi] if in_palette else GRAY_DARK
        ls_light = shade_ls(base_light, len(members), LIGHT_BAND)
        ls_dark = shade_ls(base_dark, len(members), DARK_BAND)
        gis = []
        for si, m in enumerate(members):
            light = shade(base_light, ls_light[si])
            dark = shade(base_dark, ls_dark[si])
            gi = len(clusters)
            clusters.append({
                "name": m, "short": m, "folder": name,
                "count": len(by_folder[m]),
                "light": light, "dark": dark,
                "light_ink": ink_on(light), "dark_ink": ink_on(dark),
            })
            gis.append(gi)
            for n in by_folder[m]:
                cluster_index[n] = gi
        folders.append({"name": name,
                        "count": sum(len(by_folder[m]) for m in members),
                        "clusters": gis})

    return _finish_clusters(deps, folders, clusters, cluster_index)


# ---------------------------------------------------------------------------
# SVG rendering
# ---------------------------------------------------------------------------

def render_svg(dot_src, variant_key):
    # unflatten staggers wide sibling ranks (hundreds of leaf certificates
    # would otherwise share one rank and stretch the drawing)
    flat = subprocess.run(
        ["unflatten", "-f", "-l", "6", "-c", "6"], input=dot_src,
        capture_output=True, text=True, check=True,
    ).stdout
    svg = subprocess.run(
        ["dot", "-Tsvg"], input=flat, capture_output=True, text=True,
        check=True,
    ).stdout
    # keep only the <svg> element, sized by the viewer instead of dot
    svg = svg[svg.index("<svg"):]
    svg = re.sub(r'(<svg[^>]*?) width="[^"]*" height="[^"]*"', r"\1", svg,
                 count=1)
    # inline SVGs share one document: keep ids unique per variant
    svg = re.sub(r'\bid="', f'id="{variant_key}-', svg)
    return svg


def cluster_css(clusters):
    """Fill/text/legend-chip rules per cluster, for both color schemes."""
    light, dark = [], []
    for gi, c in enumerate(clusters):
        light.append(f"  .cluster-{gi} ellipse {{ fill: {c['light']}; }}")
        light.append(f"  .cluster-{gi} text {{ fill: {c['light_ink']}; }}")
        light.append(f"  .chip-{gi} {{ background: {c['light']}; }}")
        dark.append(f"    .cluster-{gi} ellipse {{ fill: {c['dark']}; }}")
        dark.append(f"    .cluster-{gi} text {{ fill: {c['dark_ink']}; }}")
        dark.append(f"    .chip-{gi} {{ background: {c['dark']}; }}")
    return "\n".join(light), "\n".join(dark)


HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__</title>
<style>
  .viz-root {
    --surface-1: #fcfcfb;
    --page: #f9f9f7;
    --text-primary: #0b0b0b;
    --text-secondary: #52514e;
    --text-muted: #898781;
    --grid: #e1e0d9;
    --border: rgba(11,11,11,0.10);
  }
  @media (prefers-color-scheme: dark) {
    .viz-root {
      --surface-1: #1a1a19;
      --page: #0d0d0d;
      --text-primary: #ffffff;
      --text-secondary: #c3c2b7;
      --text-muted: #898781;
      --grid: #2c2c2a;
      --border: rgba(255,255,255,0.10);
    }
  }
__GROUP_CSS__
  @media (prefers-color-scheme: dark) {
__GROUP_CSS_DARK__
  }
  html, body { margin: 0; padding: 0; }
  .viz-root {
    background: var(--page);
    color: var(--text-primary);
    font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
    min-height: 100vh;
    padding: 24px;
    box-sizing: border-box;
  }
  .card {
    background: var(--surface-1);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 20px 24px;
    max-width: 1400px;
    margin: 0 auto;
  }
  h1 { font-size: 18px; font-weight: 600; margin: 0 0 4px; }
  .subtitle { font-size: 13px; color: var(--text-secondary); margin: 0 0 12px; }
  .controls {
    display: flex; flex-wrap: wrap; gap: 12px 20px; align-items: center;
    margin-bottom: 12px; font-size: 12px;
  }
  .controls input[type="search"] {
    background: var(--page); color: var(--text-primary);
    border: 1px solid var(--border); border-radius: 6px;
    padding: 5px 10px; font: inherit; width: 260px;
  }
  .legend { display: flex; flex-wrap: wrap; gap: 4px 18px; }
  .legend .folder {
    display: inline-flex; align-items: center; gap: 8px;
    color: var(--text-secondary); user-select: none;
  }
  .legend label { display: inline-flex; align-items: center; gap: 6px;
    cursor: pointer; }
  .legend .sub {
    display: inline-flex; align-items: center; gap: 4px;
    color: var(--text-muted); cursor: pointer;
  }
  .legend .sub input { width: 11px; height: 11px; margin: 0; }
  .legend .chip { width: 10px; height: 10px; border-radius: 3px; }
  .hint { color: var(--text-muted); font-size: 11px; }
  .chart-wrap {
    position: relative; border: 1px solid var(--grid); border-radius: 6px;
    overflow: hidden; background: var(--surface-1);
  }
  .chart-wrap svg { display: block; width: 100%; height: 76vh; cursor: grab; }
  .chart-wrap svg.panning { cursor: grabbing; }
  .node { cursor: pointer; }
  .edge path { stroke: var(--text-muted); }
  .edge polygon { stroke: var(--text-muted); fill: var(--text-muted); }
  .node.match ellipse { stroke: var(--text-primary); stroke-width: 2.5; }
  .node.sel ellipse { stroke: var(--text-primary); stroke-width: 3; }
  svg.searching .node:not(.match) { opacity: 0.15; }
  svg.focused .node:not(.cone):not(.sel) { opacity: 0.12; }
  svg.focused .edge { opacity: 0.06; }
  svg.focused .edge.cone { opacity: 1; }
  /* hidden-group ghosting wins over search/cone highlighting */
  svg .node.ghost, svg.focused .node.cone.ghost { opacity: 0.12; }
  svg .edge.ghost, svg.focused .edge.cone.ghost { opacity: 0.06; }
  details { margin-top: 16px; font-size: 13px; }
  summary { cursor: pointer; color: var(--text-secondary); }
  table { border-collapse: collapse; margin-top: 8px; width: 100%; }
  th, td {
    text-align: left; padding: 3px 10px; font-size: 12px;
    border-bottom: 1px solid var(--grid);
  }
  th { color: var(--text-secondary); font-weight: 600; }
  td { color: var(--text-primary); }
  td.num, th.num { text-align: right; font-variant-numeric: tabular-nums; }
  .footnote { font-size: 11px; color: var(--text-muted); margin-top: 12px; }
</style>
</head>
<body class="viz-root">
<div class="card">
  <h1>__TITLE__</h1>
  <p class="subtitle">__SUBTITLE__</p>
  <div class="controls">
    <input id="search" type="search" placeholder="Search file names&hellip;"
           aria-label="Search file names">
    <span id="search-count" class="hint"></span>
    <span class="legend" id="legend"></span>
    <span class="hint">drag to pan &middot; wheel to zoom &middot; click a node
      for its dependency cone &middot; Esc to reset</span>
  </div>
  <div class="chart-wrap" id="chart-wrap">__SVGS__</div>
  <details>
    <summary>Data table (all files, direct in-library dependencies)</summary>
    <table>
      <thead><tr><th>File</th><th>Cluster</th>
        <th class="num">Imports</th><th class="num">Imported by</th></tr></thead>
      <tbody id="table-body"></tbody>
    </table>
  </details>
  <p class="footnote">Nodes are the library&rsquo;s .v files; an arrow means
    the target file Requires the source (in-library deps only). Each legend
    group has its own hue, shaded dark to light within the group; gray files
    belong to no group. Edges are
    transitively reduced: an arrow implied by a longer path is not drawn.
    Unchecking a legend group or a folder inside it dims those files and
    their edges; the layout does not change. Layout by Graphviz dot.
    Generated on __DATE__
    from <code>__INPUT__</code> by
    <code>dependency_graph_html.py</code>.</p>
</div>
<script>
const EDGES = __EDGES__;         // [[from, to], ...]
const TABLE = __TABLE__;
const FOLDERS = __FOLDERS__;     // [{name, count, clusters}]
const CLUSTERS = __CLUSTERS__;   // [{name, short, folder, count}]

const wrap = document.getElementById("chart-wrap");
const svg = wrap.querySelector("svg");

// ---- static maps over the single layout ----
const nodes = new Map(), clusterOf = new Map();
for (const g of svg.querySelectorAll("g.node")) {
  const path = g.querySelector("title").textContent;
  nodes.set(path, g);
  const cls = [...g.classList].find(c => c.startsWith("cluster-"));
  clusterOf.set(path, +cls.slice("cluster-".length));
}
const deps = new Map(), rdeps = new Map(), edgeEls = new Map();
for (const p of nodes.keys()) { deps.set(p, []); rdeps.set(p, []); }
for (const [a, b] of EDGES) {
  deps.get(b).push(a);
  rdeps.get(a).push(b);
}
for (const g of svg.querySelectorAll("g.edge"))
  edgeEls.set(g.querySelector("title").textContent, g);

let selected = null;
const fullVB = svg.getAttribute("viewBox").split(" ").map(Number);
let vb = [...fullVB];

function applyVB() { svg.setAttribute("viewBox", vb.join(" ")); }

// ---- pan / zoom (getScreenCTM handles viewBox letterboxing exactly) ----
function clientToSvg(x, y, inv) {
  inv = inv || svg.getScreenCTM().inverse();
  return new DOMPoint(x, y).matrixTransform(inv);
}
wrap.addEventListener("wheel", ev => {
  ev.preventDefault();
  const p = clientToSvg(ev.clientX, ev.clientY);
  const k = ev.deltaY > 0 ? 1.2 : 1 / 1.2;
  const w = Math.min(fullVB[2] * 1.5, Math.max(100, vb[2] * k));
  const h = w * vb[3] / vb[2];
  vb = [p.x - (p.x - vb[0]) * w / vb[2], p.y - (p.y - vb[1]) * h / vb[3], w, h];
  applyVB();
}, {passive: false});
let pan = null;
wrap.addEventListener("pointerdown", ev => {
  pan = {x: ev.clientX, y: ev.clientY, vx: vb[0], vy: vb[1], moved: false,
         inv: svg.getScreenCTM().inverse(), target: ev.target};
  svg.classList.add("panning");
  wrap.setPointerCapture(ev.pointerId);
});
wrap.addEventListener("pointermove", ev => {
  if (!pan) return;
  const p0 = clientToSvg(pan.x, pan.y, pan.inv);
  const p1 = clientToSvg(ev.clientX, ev.clientY, pan.inv);
  if (Math.abs(ev.clientX - pan.x) + Math.abs(ev.clientY - pan.y) > 3)
    pan.moved = true;
  vb[0] = pan.vx - (p1.x - p0.x); vb[1] = pan.vy - (p1.y - p0.y);
  applyVB();
});
wrap.addEventListener("pointerup", () => {
  const wasClick = pan && !pan.moved;
  const target = pan && pan.target;
  pan = null;
  svg.classList.remove("panning");
  if (wasClick) clickOn(target);
});

// ---- click: dependency cone ----
function reach(start, adj) {
  const seen = new Set([start]), queue = [start];
  while (queue.length) {
    for (const m of adj.get(queue.pop()))
      if (!seen.has(m)) { seen.add(m); queue.push(m); }
  }
  return seen;
}
function clearFocus() {
  selected = null;
  svg.classList.remove("focused");
  for (const g of nodes.values()) g.classList.remove("sel", "cone");
  for (const g of edgeEls.values()) g.classList.remove("cone");
}
function clickOn(target) {
  const g = target && target.closest && target.closest("g.node");
  if (!g) { clearFocus(); return; }
  const path = g.querySelector("title").textContent;
  if (path === selected) { clearFocus(); return; }
  clearFocus();
  selected = path;
  const cone = new Set([...reach(path, deps), ...reach(path, rdeps)]);
  svg.classList.add("focused");
  g.classList.add("sel");
  for (const p of cone) if (p !== path) nodes.get(p).classList.add("cone");
  for (const [a, b] of EDGES) {
    if (cone.has(a) && cone.has(b)) {
      const e = edgeEls.get(`${a}->${b}`);
      if (e) e.classList.add("cone");
    }
  }
}
document.addEventListener("keydown", ev => {
  if (ev.key === "Escape") {
    clearFocus();
    document.getElementById("search").value = "";
    runSearch("");
    vb = [...fullVB];
    applyVB();
  }
});

// ---- search ----
const searchCount = document.getElementById("search-count");
function runSearch(q) {
  q = q.trim().toLowerCase();
  let hits = 0;
  for (const [path, g] of nodes) {
    const match = !!q && !hiddenClusters.has(clusterOf.get(path))
      && path.toLowerCase().includes(q);
    g.classList.toggle("match", match);
    if (match) hits++;
  }
  svg.classList.toggle("searching", !!q);
  searchCount.textContent = q ? `${hits} match${hits === 1 ? "" : "es"}` : "";
}
document.getElementById("search").addEventListener("input",
  ev => runSearch(ev.target.value));

// ---- legend: dim toggles per group and per folder inside it; unchecking
// ghosts the corresponding nodes and edges in place ----
const hiddenClusters = new Set();
function applyHidden() {
  for (const [path, g] of nodes)
    g.classList.toggle("ghost", hiddenClusters.has(clusterOf.get(path)));
  for (const [a, b] of EDGES) {
    const e = edgeEls.get(`${a}->${b}`);
    if (e) e.classList.toggle("ghost",
      hiddenClusters.has(clusterOf.get(a))
      || hiddenClusters.has(clusterOf.get(b)));
  }
  runSearch(document.getElementById("search").value);
}
const legend = document.getElementById("legend");
for (const f of FOLDERS) {
  const entry = document.createElement("span");
  entry.className = "folder";
  const groupCb = document.createElement("input");
  groupCb.type = "checkbox";
  groupCb.checked = true;
  const subCbs = [];
  const syncGroupCb = () => {
    const hid = f.clusters.filter(gi => hiddenClusters.has(gi)).length;
    groupCb.checked = hid === 0;
    groupCb.indeterminate = hid > 0 && hid < f.clusters.length;
  };
  groupCb.addEventListener("change", () => {
    for (const gi of f.clusters) {
      if (groupCb.checked) hiddenClusters.delete(gi);
      else hiddenClusters.add(gi);
    }
    for (const cb of subCbs) cb.checked = groupCb.checked;
    applyHidden();
  });
  const label = document.createElement("label");
  label.append(groupCb,
               document.createTextNode(`${f.name} (${f.count})`));
  entry.appendChild(label);
  for (const gi of f.clusters) {
    const c = CLUSTERS[gi];
    const sub = document.createElement("label");
    sub.className = "sub";
    sub.title = `${c.name} (${c.count})`;
    if (f.clusters.length > 1) {
      const cb = document.createElement("input");
      cb.type = "checkbox";
      cb.checked = true;
      cb.addEventListener("change", () => {
        if (cb.checked) hiddenClusters.delete(gi);
        else hiddenClusters.add(gi);
        syncGroupCb();
        applyHidden();
      });
      subCbs.push(cb);
      sub.appendChild(cb);
    }
    const chip = document.createElement("span");
    chip.className = `chip chip-${gi}`;
    sub.appendChild(chip);
    if (f.clusters.length > 1) {
      sub.appendChild(document.createTextNode(c.short));
    }
    entry.appendChild(sub);
  }
  legend.appendChild(entry);
}

// ---- data table (full graph, direct edges) ----
const tbody = document.getElementById("table-body");
for (const row of TABLE) {
  const tr = document.createElement("tr");
  row.forEach((v, k) => {
    const td = document.createElement("td");
    if (k >= 2) td.className = "num";
    td.textContent = v;
    tr.appendChild(td);
  });
  tbody.appendChild(tr);
}
</script>
</body>
</html>
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("-i", "--input", default="verified-ocaml/.Makefile.coq.d",
                    help="coqdep dependency file "
                         "(default: verified-ocaml/.Makefile.coq.d)")
    ap.add_argument("-o", "--output", default="docs/auto_dependency_graph.html",
                    help="output HTML file "
                         "(default: docs/auto_dependency_graph.html)")
    ap.add_argument("--root", default=core.ROOT,
                    help=f"path prefix of the analyzed library "
                         f"(default: {core.ROOT})")
    ap.add_argument("--ref", action="append", default=[], metavar="FOLDER",
                    help="reference folder (relative to the root, "
                         "repeatable), e.g. --ref Examples/Generated; each "
                         "gets its own hue, its immediate subfolders get "
                         "shades of it, everything else is gray (default: "
                         "the top-level folders)")
    ap.add_argument("--group", action="append", default=[],
                    metavar="NAME:F1,F2,...",
                    help="named group of top-level folders (repeatable, "
                         "mutually exclusive with --ref); each group gets "
                         "its own hue, its member folders get shades of it, "
                         "ungrouped folders are gray")
    ap.add_argument("--title", default="auto/ Coq dependency graph",
                    help="page title (default: auto/ Coq dependency graph)")
    ap.add_argument("--no-disk-check", action="store_true",
                    help="skip reconciling the .d file against the .v files on "
                         "disk (use when the .d lives outside the analyzed "
                         "subtree or spans several roots via --root \"\")")
    args = ap.parse_args()

    if not shutil.which("dot") or not shutil.which("unflatten"):
        sys.exit("error: the `dot` and `unflatten` executables are required "
                 "(sudo apt install graphviz)")
    dep_file = Path(args.input)
    if not dep_file.exists():
        sys.exit(f"error: {dep_file} not found; run 'make Makefile.coq' in "
                 f"verified-ocaml/ to regenerate coqdep output")
    deps = core.load_graph(dep_file, args.root,
                           disk_check=not args.no_disk_check)
    direct_edges = sum(len(ds) for ds in deps.values())

    groups = []
    for spec in args.group:
        name, sep, rest = spec.partition(":")
        members = [m.strip().strip("/") for m in rest.split(",") if m.strip()]
        if not sep or not name.strip() or not members:
            sys.exit(f"error: --group expects NAME:Folder1,Folder2,... "
                     f"(got {spec!r})")
        groups.append((name.strip(), members))

    if groups:
        if args.ref:
            sys.exit("error: --group and --ref are mutually exclusive")
        folders, clusters, cluster_index = build_clusters_from_groups(
            deps, args.root, groups)
        color_desc = (f"One hue per group "
                      f"({', '.join(name for name, _ in groups)}), shaded "
                      f"by folder; gray = ungrouped.")
    else:
        refs = [r.strip("/") for r in args.ref]
        if not refs:
            refs = sorted({core.folder_of(n, args.root) for n in deps}
                          - {"(root)"})
        folders, clusters, cluster_index = build_clusters(
            deps, args.root, refs)
        color_desc = (f"One hue per reference folder ({', '.join(refs)}), "
                      f"shaded by subfolder; gray = outside every "
                      f"reference.")
    def attrs(node):
        gi = cluster_index[node]
        return {"class": f"cluster-{gi}",
                "fillcolor": clusters[gi]["light"],
                "fontcolor": clusters[gi]["light_ink"]}

    # a single pre-rendered layout; the legend checkboxes dim groups in
    # place instead of re-laying-out the graph
    edges = core.reduced_edges(deps)
    svg = render_svg(core.to_dot(deps, edges, attrs), "v")
    print(f"{len(deps)} nodes -> {len(edges)} edges after transitive "
          f"reduction")

    rdeps_count = {n: 0 for n in deps}
    for ds in deps.values():
        for d in ds:
            rdeps_count[d] += 1
    table = [[n, clusters[cluster_index[n]]["name"], len(deps[n]),
              rdeps_count[n]]
             for n in sorted(deps)]

    subtitle = (f"{len(deps)} .v files; {direct_edges} direct in-library "
                f"Require edges, drawn transitively reduced "
                f"({len(edges)} arrows). {color_desc} "
                f"Unchecking a legend group or folder dims its files.")
    css_light, css_dark = cluster_css(clusters)
    html = (HTML_TEMPLATE
            .replace("__GROUP_CSS__", css_light)
            .replace("__GROUP_CSS_DARK__", css_dark)
            .replace("__SVGS__", svg)
            .replace("__EDGES__", json.dumps(edges))
            .replace("__TABLE__", json.dumps(table))
            .replace("__FOLDERS__", json.dumps(folders))
            .replace("__CLUSTERS__", json.dumps(
                [{"name": c["name"], "short": c["short"],
                  "folder": c["folder"], "count": c["count"]}
                 for c in clusters]))
            .replace("__TITLE__", args.title)
            .replace("__SUBTITLE__", subtitle)
            .replace("__DATE__", datetime.date.today().isoformat())
            .replace("__INPUT__", args.input))
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(html, encoding="utf-8")
    for f in folders:
        subs = ", ".join(f"{clusters[gi]['name']} ({clusters[gi]['count']})"
                         for gi in f["clusters"])
        print(f"  {f['name']}: {f['count']} files [{subs}]")
    print(f"graph written to {out}")


if __name__ == "__main__":
    main()
