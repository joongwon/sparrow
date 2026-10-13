# Sparrow

Sparrow is a state-of-the-art static analyzer that aims to verify the absence
of fatal bugs in C source. Sparrow is designed based on the Abstract Interpretation
framework and the analysis is sound in design. Sparrow adopts a number of well-founded
static analysis techniques for scalability, precision, and user convenience.
This is the academic version of Sparrow that is different from the [commercial version][fasoo].

### How to Build
1. Initialize an Opam switch and install dependencies.
2. Build using Dune: `dune build`.

### Browse saved analysis results

Install Graphviz (`sudo apt-get install graphviz` on Ubuntu), then generate an
offline report from snapshots written by Sparrow's `-marshal_out` option:

```sh
sparrow-vis --marshal-dir /path/to/analysis --prefix merged --analysis itv
```

Open `/path/to/analysis/merged.itv.vis/index.html` in a browser. The index lists
and filters functions. Each function page contains a Graphviz CFG:

The page header shows the saved C function declaration, including its return
type, parameter names and types, and variadic arguments where applicable.

- Click a node's body (or select it from the Node menu) to inspect its saved
  input and output abstract states. Keyboard users can focus a node and press
  Enter or Space.
- `skip` labels identify entries, exits, call return points, and CFG joins or
  connectors. Return points describe implicit return-value updates where applicable.
- Click an underlined blue function name inside a call node to navigate to
  that function's page. This does **not** select the call node. Resolved
  indirect-call targets are also linked; external functions without a CFG
  are marked explicitly.
- Filter state text by variable/location, zoom the graph, or download its DOT
  and SVG. Selected nodes have bookmarkable URL fragments.
- Choose **Diff** to compare the selected node's input and output. Red `−`
  lines occur only in the input; green `+` lines occur only in the output.
  Unchanged lines and trivial self-bindings are omitted, and the search field
  filters changes too. This compares the displayed sparse-state text; it is
  unavailable if either saved state is missing.

State displays omit trivial function self-bindings such as
`f -> (bot, bot, bot, bot, {f})`, with a count of omitted bindings. Aliases,
multiple callees, and values with additional abstract information remain visible.

Use `--analysis oct` for octagon snapshots, `--output DIR` to choose a new output
directory, or `--dot PATH` to select Graphviz. The default prefix is `merged`;
otherwise use the basename preceding `.itv.global` / `.oct.global`. An existing
output directory is never overwritten. From the source checkout, replace
`sparrow-vis` with `dune exec src/vis.exe --`.

The report works directly over `file://`; keep its `states/`, `app.js`, and
`style.css` files together. State text is deduplicated and loaded on demand,
but exporting large snapshots can take time and disk space. States are the
saved **sparse** analysis tables, not reconstructed full memories. Missing
entries are marked “not recorded.” Snapshots must be compatible with this
Sparrow build; octagon snapshots must use the current portable serialization.
CFGs over 1,000 nodes use bounded Graphviz layout optimization to keep rendering
time practical, with all nodes and edges preserved.

The existing `sparrow-vis FILE.json` CFG/call-graph export remains available.
