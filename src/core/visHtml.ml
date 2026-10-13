(* Offline assets for the saved-analysis visualizer. *)
let css =
  {|
:root{font-family:system-ui,sans-serif;color:#182b3a;background:#f4f7fa;color-scheme:light}*{box-sizing:border-box}body{margin:0}a{color:#075fba}header{background:#142b40;color:white;padding:18px 24px;display:flex;gap:20px;align-items:center;flex-wrap:wrap}header a{color:#a9d9ff}h1{font-size:22px;margin:0}h2{font-size:18px}p{line-height:1.5}.badge{font-size:12px;text-transform:uppercase;letter-spacing:.08em;background:#29445b;padding:6px 10px;border-radius:20px}.index{max-width:1100px;margin:28px auto;padding:0 20px}input,select,button{font:inherit;padding:8px 12px;border:1px solid #bacbd7;border-radius:6px;background:white;color:#182b3a}input{width:100%}button{cursor:pointer}button:hover{background:#eaf3fc}a:focus-visible,button:focus-visible,input:focus-visible,select:focus-visible{outline:3px solid #dc8b00;outline-offset:3px}table{width:100%;border-collapse:collapse;background:white;margin-top:18px}th,td{text-align:left;padding:12px 16px;border-bottom:1px solid #e3eaf0}th{font-size:12px;color:#526b7d;text-transform:uppercase}code,pre{font-family:ui-monospace,monospace}.toolbar{padding:12px 20px;background:white;border-bottom:1px solid #d5e0e8;display:flex;align-items:center;gap:10px;flex-wrap:wrap}.toolbar p{margin:0;flex:1;min-width:250px;font-size:14px}.layout{display:grid;grid-template-columns:minmax(0, 1fr) minmax(340px, 38vw);height:calc(100vh - 145px)}.graph-view{overflow:auto;padding:24px;background:#f4f7fa}.graph-view svg{display:block;max-width:none;height:auto}.node{cursor:pointer}.node.selected>polygon,.node.selected>path,.node:focus>polygon,.node:focus>path{stroke:#d88600;stroke-width:3px}.node:focus{outline:none}.node a text{fill:#075fba;text-decoration:underline}.node a{cursor:pointer}.state-panel{overflow:auto;background:white;border-left:1px solid #d5e0e8;padding:20px}.muted{color:#536c7e;font-size:14px}.state-panel pre{font-size:12px;line-height:1.6;white-space:pre-wrap;overflow-wrap:anywhere;background:#f4f7fa;border:1px solid #e0e8ef;padding:12px;border-radius:6px}.state-panel .command{font-size:13px}.states{margin-top:16px}.states h3{font-size:14px;margin-bottom:6px}.error{color:#a62020}.empty{padding:20px;color:#536c7e}.state-panel nav{display:flex;gap:12px;flex-wrap:wrap}#node-picker{max-width:260px}@media(max-width:850px){.layout{display:block;height:auto}.graph-view{height:60vh}.state-panel{border-left:0;border-top:1px solid #d5e0e8}.toolbar{padding:10px}header{padding:16px}.index{margin-top:16px}}
.state-view{display:flex;gap:8px;margin-top:16px}.state-view button[aria-pressed="true"]{background:#142b40;color:white}.state-diff pre{padding:0}.diff-line{display:block;padding:3px 10px}.diff-remove{background:#fff0ee;color:#8c2424}.diff-add{background:#eaf7ef;color:#185b32}
|}

let js =
  {|
'use strict';
function omitTrivialFunctionBindings(text) {
  const trimmed = text.trim();
  if (!trimmed.startsWith('{') || !trimmed.endsWith('}')) return text;
  let omitted = 0;
  // Match complete global bindings, including pretty-printer line wrapping.
  // Keep aliases, multiple callees, locals, and any non-bottom component.
  const body = trimmed.slice(1, -1).trim().replace(
    /(^|\n)[ \t]*([A-Za-z_$][A-Za-z0-9_$]*)\s*->\s*\(\s*bot\s*,\s*bot\s*,\s*bot\s*,\s*bot\s*,\s*\{\s*\2\s*\}\s*\)[ \t]*(?=\n|$)/g,
    (_, prefix) => { omitted++; return prefix; }
  ).split('\n').filter(line => line.trim() !== '').join('\n').trim();
  if (!omitted) return text;
  const note = `${omitted} trivial function binding${omitted === 1 ? '' : 's'} omitted.`;
  return body ? `${note}\n{ ${body} }` : `${note}\nNo other bindings.`;
}
// Compare displayed lines, ignoring map delimiters and omission notices.
// Count duplicate lines; sets would incorrectly discard repeated constraints.
function stateDiffLines(text) {
  let body = text.replace(/^\d+ trivial function bindings? omitted\.\n/, '').trim();
  if (body === 'No other bindings.') return [];
  if (body.startsWith('{') && body.endsWith('}')) body = body.slice(1, -1);
  return body.split('\n').map(line => line.trim()).filter(Boolean);
}
function diffStates(input, output) {
  const before = stateDiffLines(input), after = stateDiffLines(output);
  function unmatched(lines, other) {
    const counts = new Map();
    other.forEach(line => counts.set(line, (counts.get(line) || 0) + 1));
    return lines.filter(line => {
      const count = counts.get(line) || 0;
      if (!count) return true;
      counts.set(line, count - 1); return false;
    });
  }
  return {removed: unmatched(before, after), added: unmatched(after, before)};
}
const search = document.getElementById('function-search');
if (search) search.addEventListener('input', () => {
  const q = search.value.toLowerCase(); let count = 0;
  document.querySelectorAll('[data-function]').forEach(row => {
    row.hidden = !row.dataset.function.toLowerCase().includes(q);
    if (!row.hidden) count++;
  });
  document.getElementById('function-count').textContent = `${count} functions`;
});
const metadata = document.getElementById('node-data');
if (metadata) {
  const nodes = JSON.parse(metadata.textContent);
  const picker = document.getElementById('node-picker');
  const stateSearch = document.getElementById('state-search');
  const cache = new Map(); const pending = new Map();
  let selected = null; let revision = 0; let texts = {input:'', output:''};
  let status = {input:'idle', output:'idle'};
  const fullStates = document.querySelector('.states');
  const viewControls = document.createElement('div');
  viewControls.className = 'state-view';
  viewControls.setAttribute('role', 'group');
  viewControls.setAttribute('aria-label', 'State view');
  const diffPanel = document.createElement('section');
  diffPanel.className = 'state-diff'; diffPanel.id = 'state-diff'; diffPanel.hidden = true;
  diffPanel.setAttribute('aria-live', 'polite');
  const diffTitle = document.createElement('h3'); diffTitle.textContent = 'Changes (input → output)';
  const diffSummary = document.createElement('p'); diffSummary.id = 'diff-summary'; diffSummary.className = 'muted';
  const diffBody = document.createElement('pre'); diffBody.id = 'diff-lines';
  diffPanel.append(diffTitle, diffSummary, diffBody);
  fullStates.before(viewControls); fullStates.after(diffPanel);
  const viewButtons = ['Full states', 'Diff'].map((label, index) => {
    const button = document.createElement('button'); button.textContent = label;
    button.id = index ? 'show-diff' : 'show-full-states';
    button.setAttribute('aria-pressed', String(index === 0));
    button.addEventListener('click', () => {
      fullStates.hidden = index === 1; diffPanel.hidden = index === 0;
      viewButtons.forEach((b, i) => b.setAttribute('aria-pressed', String(i === index)));
    });
    viewControls.appendChild(button); return button;
  });
  function renderDiff(q) {
    diffBody.replaceChildren();
    if (!selected) {diffSummary.textContent = 'Select a node to compare states.'; return;}
    if (Object.values(status).includes('loading')) {diffSummary.textContent = 'Loading states…'; return;}
    const unavailable = ['input', 'output'].filter(side => status[side] !== 'ready');
    if (unavailable.length) {
      diffSummary.textContent = `Diff unavailable: ${unavailable.join(' and ')} state is missing or could not be loaded.`;
      return;
    }
    const diff = diffStates(texts.input, texts.output);
    const total = diff.removed.length + diff.added.length;
    if (!total) {diffSummary.textContent = 'No changes in the displayed state bindings.'; return;}
    let shown = 0;
    for (const [kind, prefix] of [['removed', '−'], ['added', '+']]) {
      diff[kind].forEach(line => {
        if (q && !line.toLowerCase().includes(q)) return;
        const row = document.createElement('span');
        row.className = `diff-line ${kind === 'removed' ? 'diff-remove' : 'diff-add'}`;
        row.textContent = `${prefix} ${line}`; diffBody.appendChild(row); shown++;
      });
    }
    diffSummary.textContent = `${diff.removed.length} removed lines · ${diff.added.length} added lines. − input only; + output only.`
      + (q ? ` Showing ${shown} matching lines.` : '');
    if (!shown) diffBody.textContent = 'No matching changes.';
  }
  // Script files work over file:// as well as HTTP; fetch would require a server.
  window.sparrowState = (key, text) => { cache.set(key, omitTrivialFunctionBindings(text)); };
  function load(key) {
    if (!key) return Promise.resolve('Not recorded in the sparse analysis table. This is not a reconstructed full state.');
    if (cache.has(key)) return Promise.resolve(cache.get(key));
    if (pending.has(key)) return pending.get(key);
    const promise = new Promise((resolve, reject) => {
      const script = document.createElement('script');
      script.src = `states/${key}.js`;
      script.onload = () => { script.remove(); pending.delete(key);
        if (cache.has(key)) resolve(cache.get(key)); else reject(new Error('Invalid state file.')); };
      script.onerror = () => { script.remove(); pending.delete(key); reject(new Error('Could not load saved state. Keep the states directory beside this page.')); };
      document.head.appendChild(script);
    });
    pending.set(key, promise); return promise;
  }
  function renderStates() {
    const q = stateSearch.value.toLowerCase();
    for (const side of ['input', 'output']) {
      const text = texts[side];
      document.getElementById(`${side}-state`).textContent = q
        ? text.split('\n').filter(line => line.toLowerCase().includes(q)).join('\n') || 'No matching lines.' : text;
    }
    renderDiff(q);
  }
  renderDiff('');
  async function select(id, updateHash = true) {
    if (!nodes[id]) return;
    const ticket = ++revision; selected = id;
    document.querySelectorAll('g.node').forEach(group => {
      const active = group.id === id; group.classList.toggle('selected', active);
      group.setAttribute('aria-pressed', String(active));
    });
    picker.value = id;
    const node = nodes[id];
    document.getElementById('node-title').textContent = node.name;
    document.getElementById('node-command').textContent = node.command;
    const links = document.getElementById('callees'); links.replaceChildren();
    node.callees.forEach(callee => {
      const element = document.createElement(callee.href ? 'a' : 'span');
      element.textContent = callee.name + (callee.href ? '' : ' (external / no CFG)');
      if (callee.href) element.href = callee.href;
      links.appendChild(element);
    });
    texts = {input:'Loading…', output:'Loading…'};
    status = {input:'loading', output:'loading'}; renderStates();
    // Keep node URLs bookmarkable without triggering native anchor scrolling.
    if (updateHash && location.hash !== `#${id}`) history.pushState(null, '', `#${id}`);
    await Promise.all(['input','output'].map(async side => {
      try { const text = await load(node[side]); if (ticket === revision) {texts[side] = text; status[side] = node[side] ? 'ready' : 'missing'; renderStates();} }
      catch (error) { if (ticket === revision) {texts[side] = error.message; status[side] = 'error'; renderStates();} }
    }));
  }
  document.querySelectorAll('g.node').forEach(group => {
    if (!nodes[group.id]) return;
    group.setAttribute('tabindex', '0'); group.setAttribute('role', 'button');
    group.setAttribute('aria-label', `Show abstract state for ${nodes[group.id].name}`);
    group.addEventListener('click', event => {
      // A callee name is a navigation link, never a request to select this node.
      if (event.target.closest('a')) return;
      select(group.id);
    });
    group.addEventListener('keydown', event => {
      if (event.target.closest('a')) return;
      if (event.key === 'Enter' || event.key === ' ') {event.preventDefault(); select(group.id);}
    });
    group.querySelectorAll('a').forEach(link => {
      link.setAttribute('tabindex', '0');
      link.addEventListener('click', event => event.stopPropagation());
      link.addEventListener('keydown', event => event.stopPropagation());
    });
  });
  picker.addEventListener('change', () => select(picker.value));
  stateSearch.addEventListener('input', renderStates);
  const syncSelection = () => {const id = location.hash.slice(1); if (id !== selected) select(id, false);};
  window.addEventListener('hashchange', syncSelection);
  window.addEventListener('popstate', syncSelection);
  const svg = document.querySelector('.graph-view svg');
  let scale = 1;
  const width = svg.viewBox.baseVal.width;
  function zoom(value) {scale = Math.max(.1, Math.min(4, value)); svg.style.width = `${width * scale}px`;}
  document.getElementById('zoom-in').onclick = () => zoom(scale * 1.25);
  document.getElementById('zoom-out').onclick = () => zoom(scale / 1.25);
  document.getElementById('zoom-fit').onclick = () => zoom((document.querySelector('.graph-view').clientWidth - 48) / width);
  zoom(1);
  if (nodes[location.hash.slice(1)]) select(location.hash.slice(1), false);
}
|}
