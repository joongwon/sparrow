(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
(* The browser front end of sparrow-server: one static page over /api. *)

let html =
  {|<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Sparrow State</title>
<style>
:root {
  --bg: #fafaf9; --panel: #ffffff; --text: #1c1917; --muted: #78716c;
  --border: #e7e5e4; --accent: #2563eb; --accent-bg: #eff6ff;
  --bad: #b91c1c; --bad-bg: #fef2f2; --good: #15803d; --good-bg: #f0fdf4;
  --warn: #a16207; --warn-bg: #fefce8; --code: #f5f5f4;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #0c0a09; --panel: #1c1917; --text: #e7e5e4; --muted: #a8a29e;
    --border: #292524; --accent: #60a5fa; --accent-bg: #172554;
    --bad: #f87171; --bad-bg: #2a1212; --good: #4ade80; --good-bg: #0f2a18;
    --warn: #facc15; --warn-bg: #2a2410; --code: #292524;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--text);
  font: 14px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif; }
code, .mono { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12.5px; }
a { color: var(--accent); text-decoration: none; cursor: pointer; }
a:hover { text-decoration: underline; }
header { display: flex; align-items: baseline; gap: 16px; flex-wrap: wrap;
  padding: 10px 16px; border-bottom: 1px solid var(--border); background: var(--panel); }
header h1 { font-size: 16px; margin: 0; }
header .stats { color: var(--muted); font-size: 13px; }
.layout { display: grid; grid-template-columns: 320px 1fr; height: calc(100vh - 45px); }
nav { border-right: 1px solid var(--border); display: flex; flex-direction: column; min-height: 0; background: var(--panel); }
.tabs { display: flex; border-bottom: 1px solid var(--border); }
.tabs button { flex: 1; padding: 8px 4px; border: 0; background: none; color: var(--muted);
  font: inherit; font-size: 13px; cursor: pointer; border-bottom: 2px solid transparent; }
.tabs button.on { color: var(--text); border-bottom-color: var(--accent); }
.side-tools { padding: 8px; display: flex; gap: 6px; }
input, select { font: inherit; padding: 5px 8px; border: 1px solid var(--border);
  border-radius: 6px; background: var(--bg); color: var(--text); min-width: 0; }
.side-tools input { flex: 1; }
.list { overflow: auto; flex: 1; min-height: 0; }
.list .item { padding: 6px 10px; border-bottom: 1px solid var(--border); cursor: pointer; }
.list .item:hover { background: var(--accent-bg); }
.list .item .sub { color: var(--muted); font-size: 12px; }
main { overflow: auto; padding: 16px 20px; min-width: 0; }
h2 { font-size: 18px; margin: 0 0 4px; word-break: break-all; }
h3 { font-size: 14px; margin: 18px 0 6px; }
.meta { color: var(--muted); margin-bottom: 10px; }
.meta a { margin-right: 6px; }
table { border-collapse: collapse; width: 100%; }
th, td { text-align: left; padding: 4px 8px; border-bottom: 1px solid var(--border); vertical-align: top; }
th { color: var(--muted); font-weight: 500; font-size: 12px; position: sticky; top: 0; background: var(--bg); }
tr.click { cursor: pointer; }
tr.click:hover td { background: var(--accent-bg); }
.cmd { background: var(--code); padding: 1px 5px; border-radius: 4px; word-break: break-all; }
.pill { display: inline-block; padding: 0 6px; border-radius: 999px; font-size: 11.5px; font-weight: 600; }
.pill.unproven { color: var(--bad); background: var(--bad-bg); }
.pill.proven { color: var(--good); background: var(--good-bg); }
.pill.bot { color: var(--warn); background: var(--warn-bg); }
.cols { display: grid; grid-template-columns: 1fr 1fr; gap: 16px; }
.mem .val { word-break: break-all; }
.mem .part { display: block; color: var(--muted); }
.mem .part b { color: var(--text); font-weight: 500; }
.empty { color: var(--muted); padding: 12px 0; }
.err { color: var(--bad); }
.more { margin: 8px 0; }
@media (max-width: 900px) {
  .layout { grid-template-columns: 1fr; height: auto; }
  nav { max-height: 45vh; border-right: 0; border-bottom: 1px solid var(--border); }
  .cols { grid-template-columns: 1fr; }
  main { padding: 12px 16px; }
}
</style>
</head>
<body>
<header><h1>Sparrow state</h1><span class="stats" id="stats">loading…</span></header>
<div class="layout">
  <nav>
    <div class="tabs" id="tabs">
      <button data-tab="procs" class="on">Procedures</button>
      <button data-tab="alarms">Alarms</button>
      <button data-tab="locs">Locations</button>
    </div>
    <div class="side-tools" id="side-tools"></div>
    <div class="list" id="list"></div>
  </nav>
  <main id="main"><div class="empty">Pick a procedure, an alarm or a location.</div></main>
</div>
<script>
"use strict";
const $ = (id) => document.getElementById(id);
function el(tag, attrs, ...kids) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (k === "onclick") e.addEventListener("click", v);
    else if (k === "class") e.className = v;
    else e.setAttribute(k, v);
  }
  return fill(e, kids);
}
/* replace [target]'s children by [kids]: nested arrays flattened, null skipped */
function fill(target, ...kids) {
  target.replaceChildren(...kids.flat(Infinity).filter((k) => k != null)
    .map((k) => (k instanceof Node ? k : String(k))));
  return target;
}
async function api(path, params) {
  const qs = new URLSearchParams(params || {}).toString();
  const r = await fetch("/api/" + path + (qs ? "?" + qs : ""));
  if (!r.ok) throw new Error(await r.text());
  return r.json();
}
const go = (kind, value) => { location.hash = kind + "=" + encodeURIComponent(value); };
const link = (text, kind, value) => el("a", { onclick: (e) => { e.preventDefault(); go(kind, value); } }, text);
const nodeLink = (id) => link(id, "node", id);
const locText = (l) => (l.line < 0 ? "" : l.text || l.file + ":" + l.line);
function debounce(f, ms) { let t; return (...a) => { clearTimeout(t); t = setTimeout(() => f(...a), ms); }; }
function fail(target, e) { target.replaceChildren(el("div", { class: "err" }, String(e.message || e))); }

/* ---------- sidebar ---------- */
let tab = "procs";
const side = {
  procs: { tools: () => [search("procedure name")], load: loadProcs },
  alarms: { tools: () => [statusSelect(), search("file, procedure, expression")], load: loadAlarms },
  locs: { tools: () => [search("location name")], load: loadLocs },
};
function search(placeholder) {
  const i = el("input", { id: "q", type: "search", placeholder });
  i.addEventListener("input", debounce(() => side[tab].load(), 200));
  return i;
}
function statusSelect() {
  const s = el("select", { id: "status" },
    ["unproven", "proven", "bot", "all"].map((v) => el("option", { value: v }, v)));
  s.addEventListener("change", () => side[tab].load());
  return s;
}
function setTab(t) {
  tab = t;
  for (const b of $("tabs").children) b.classList.toggle("on", b.dataset.tab === t);
  $("side-tools").replaceChildren(...side[t].tools());
  side[t].load();
}
$("tabs").addEventListener("click", (e) => { if (e.target.dataset.tab) setTab(e.target.dataset.tab); });
const q = () => ($("q") ? $("q").value : "");

async function loadProcs() {
  const list = $("list");
  try {
    const procs = await api("procs", { q: q() });
    list.replaceChildren(...procs.map((p) =>
      el("div", { class: "item", onclick: () => go("proc", p.name) },
        el("div", { class: "mono" }, p.name), el("div", { class: "sub" }, p.nodes + " nodes"))));
    if (!procs.length) list.replaceChildren(el("div", { class: "empty item" }, "no match"));
  } catch (e) { fail(list, e); }
}
async function loadAlarms() {
  const list = $("list");
  try {
    const r = await api("alarms", { status: $("status").value, q: q(), limit: 300 });
    list.replaceChildren(
      el("div", { class: "item sub" }, r.matching + " alarms" + (r.matching > 300 ? " (first 300)" : "")),
      ...r.alarms.map((a) => el("div", { class: "item", onclick: () => go("node", a.node) },
        el("div", {}, el("span", { class: "pill " + a.status }, a.status), " ", el("span", { class: "mono" }, locText(a.location))),
        el("div", { class: "sub mono" }, a.exp),
        el("div", { class: "sub" }, a.proc + (a.allocsite ? " · " + a.allocsite : "")))));
  } catch (e) { fail(list, e); }
}
async function loadLocs() {
  const list = $("list");
  list.replaceChildren(el("div", { class: "item sub" }, "searching… (the first search builds the index)"));
  try {
    const locs = await api("locs", { q: q(), limit: 300 });
    list.replaceChildren(...locs.map((l) =>
      el("div", { class: "item", onclick: () => go("loc", l.loc) },
        el("div", { class: "mono" }, l.loc), el("div", { class: "sub" }, l.defs + " defs · " + l.uses + " uses"))));
    if (!locs.length) list.replaceChildren(el("div", { class: "empty item" }, "no match"));
  } catch (e) { fail(list, e); }
}

/* ---------- main views ---------- */
function cmdCell(cmd) {
  return [el("span", { class: "cmd mono" }, cmd.text), " ", el("span", { class: "sub mono" }, locText(cmd.location))];
}
async function showProc(name) {
  const main = $("main");
  main.replaceChildren(el("div", { class: "empty" }, "loading " + name + "…"));
  try {
    const p = await api("proc", { name });
    const rows = p.nodes.map((n) => el("tr", { class: "click", onclick: () => go("node", n.id) },
      el("td", { class: "mono" }, n.id),
      el("td", {}, el("span", { class: "cmd mono" }, n.cmd.text),
        n.callees && n.callees.length ? el("div", { class: "sub" }, "calls ", n.callees.join(", ")) : null),
      el("td", { class: "mono" }, locText(n.cmd.location)),
      el("td", {}, n.input_size == null ? "–" : n.input_size),
      el("td", {}, n.output_size == null ? "–" : n.output_size)));
    main.replaceChildren(
      el("h2", { class: "mono" }, p.name),
      el("div", { class: "meta" }, p.nodes.length + " nodes" + (p.undefined ? " · undefined procedure" : "")),
      el("table", {}, el("thead", {}, el("tr", {}, ["node", "command", "location", "in", "out"].map((h) => el("th", {}, h)))),
        el("tbody", {}, rows)));
  } catch (e) { fail(main, e); }
}
function cellView(c) {
  const parts = [];
  if (c.itv) parts.push(el("span", { class: "part" }, "itv ", el("b", { class: "mono" }, c.itv)));
  if (c.points_to) parts.push(el("span", { class: "part" }, "points to ",
    c.points_to.map((l, i) => [i ? ", " : "", link(l, "loc", l)])));
  if (c.array) parts.push(el("span", { class: "part" }, "array ", el("b", { class: "mono" }, c.array)));
  if (c.procs) parts.push(el("span", { class: "part" }, "procs ", el("b", { class: "mono" }, c.procs)));
  if (c.info) parts.push(el("span", { class: "part" }, "info ", el("b", { class: "mono" }, c.info)));
  return parts.length ? parts : [el("span", { class: "part" }, el("b", { class: "mono" }, c.value))];
}
function memoryPanel(title, nodeId, which, mem) {
  const box = el("div", { class: "mem" });
  if (!mem) { box.append(el("h3", {}, title), el("div", { class: "empty" }, "no memory at this node")); return box; }
  const filter = el("input", { type: "search", placeholder: "filter locations" });
  const body = el("tbody");
  const info = el("div", { class: "sub" });
  const more = el("div", { class: "more" });
  let shown = 0;
  const render = (m, append) => {
    if (!append) { body.replaceChildren(); shown = 0; }
    for (const c of m.entries) body.append(el("tr", {},
      el("td", { class: "mono" }, link(c.loc, "loc", c.loc)), el("td", { class: "val" }, cellView(c))));
    shown += m.entries.length;
    info.textContent = m.matching + " of " + m.size + " locations";
    more.replaceChildren(shown < m.matching ? el("a", { onclick: () => fetchMore(shown) }, "show more") : "");
  };
  const fetchMore = async (offset) => {
    try {
      const r = await api("node", { id: nodeId, q: filter.value, offset, limit: 500 });
      render(r[which], offset > 0);
    } catch (e) { fail(more, e); }
  };
  filter.addEventListener("input", debounce(() => fetchMore(0), 200));
  render(mem, false);
  box.append(el("h3", {}, title), filter, info,
    el("table", {}, el("thead", {}, el("tr", {}, el("th", {}, "location"), el("th", {}, "value"))), body), more);
  return box;
}
async function showNode(id) {
  const main = $("main");
  main.replaceChildren(el("div", { class: "empty" }, "loading " + id + "…"));
  try {
    const n = await api("node", { id, limit: 500 });
    const proc = await api("proc", { name: n.proc });
    const me = proc.nodes.find((x) => x.id === id) || {};
    const ids = (xs) => (xs && xs.length ? xs.map((x, i) => [i ? " " : "", nodeLink(x)]) : "–");
    fill(main,
      el("h2", { class: "mono" }, n.id),
      el("div", { class: "meta" }, "in ", link(n.proc, "proc", n.proc), " · ", locText(n.cmd.location)),
      el("div", {}, el("span", { class: "cmd mono" }, n.cmd.text)),
      el("div", { class: "meta", style: "margin-top:8px" }, "pred ", ids(me.pred), " · succ ", ids(me.succ),
        me.callees && me.callees.length ? [" · calls ", me.callees.map((c, i) => [i ? ", " : "", link(c, "proc", c)])] : null),
      n.alarms.length ? [el("h3", {}, "Alarms at this node"),
        el("table", {}, el("tbody", {}, n.alarms.map((a) => el("tr", {},
          el("td", {}, el("span", { class: "pill " + a.status }, a.status)),
          el("td", { class: "mono" }, a.exp),
          el("td", { class: "mono" }, a.allocsite || ""),
          el("td", { class: "mono" }, a.desc)))))] : null,
      el("div", { class: "cols" }, memoryPanel("Input memory", id, "input", n.input), memoryPanel("Output memory", id, "output", n.output)));
  } catch (e) { fail(main, e); }
}
async function showLoc(name) {
  const main = $("main");
  main.replaceChildren(el("div", { class: "empty" }, "loading " + name + "… (the first lookup builds the index)"));
  try {
    const l = await api("loc", { name, limit: 500 });
    const table = (part, title) => [
      el("h3", {}, title + " (" + part.count + (part.count > part.nodes.length ? ", first " + part.nodes.length : "") + ")"),
      part.nodes.length ? el("table", { class: "mem" }, el("thead", {}, el("tr", {}, ["node", "command", "value"].map((h) => el("th", {}, h)))),
        el("tbody", {}, part.nodes.map((n) => el("tr", {},
          el("td", { class: "mono" }, nodeLink(n.id)),
          el("td", {}, cmdCell(n.cmd)),
          el("td", { class: "val" }, n.cell ? cellView(n.cell) : "–"))))) : el("div", { class: "empty" }, "none")];
    fill(main, el("h2", { class: "mono" }, l.loc),
      el("div", { class: "meta" }, "defined in the output of " + l.defs.count + " nodes, used in the input of " + l.uses.count),
      table(l.defs, "Definitions (value after the node)"), table(l.uses, "Uses (value before the node)"));
  } catch (e) { fail(main, e); }
}
function route() {
  const h = location.hash.slice(1);
  const i = h.indexOf("=");
  if (i < 0) return;
  const kind = h.slice(0, i), value = decodeURIComponent(h.slice(i + 1));
  if (kind === "proc") showProc(value);
  else if (kind === "node") showNode(value);
  else if (kind === "loc") showLoc(value);
}
window.addEventListener("hashchange", route);

api("summary").then((s) => {
  $("stats").textContent = s.files.length + " files · " + s.procedures + " procedures · " + s.nodes + " nodes · "
    + s.alarms.unproven_points + " unproven of " + s.alarms.points + " alarm points ("
    + s.alarms.unproven_queries + " of " + s.alarms.queries + " queries)";
}).catch((e) => { $("stats").textContent = String(e.message || e); });
setTab("procs");
route();
</script>
</body>
</html>
|}
