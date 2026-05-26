/**
 * <pyana-delegation-graph> — SVG visualizer of the capability delegation graph.
 *
 * Attribute contract:
 *   uri   — optional pyana://federation/<idx> to annotate heading (v0: ignored for filtering)
 *   mode  — "default" | "compact" (compact: text summary + thumbnail SVG)
 *
 * Data source: runtime._wasm.get_delegation_graph(runtime._handle)
 * Returns: { nodes: [{ cell_id, agent_name }], edges: [{ from, to, slot, permissions }] }
 *
 * Visual design:
 *   - Nodes arranged on a circle (deterministic radial layout, no deps)
 *   - Named cells: filled green (#4ade80 on dark bg)
 *   - Anonymous cells: filled grey (#475569)
 *   - Edges: directed arrows, colored by permissions, labeled with one-letter abbrev
 *   - Hover node: tooltip with full cell_id
 *   - Hover edge: tooltip with full permissions + slot
 *   - Click node: emits pyana:navigate CustomEvent { uri: "pyana://cell/<id>" }
 *
 * Permission abbreviations (from Rust Debug fmt):
 *   Signature → S   Proof → P   None → N   Impossible → I   Either → E
 *   anything else → first char
 */

import { InspectorBase, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Permission palette
// ---------------------------------------------------------------------------
const PERM_COLORS = {
  S: '#4ade80', // green — Signature
  P: '#60a5fa', // blue  — Proof
  N: '#94a3b8', // slate — None
  I: '#f87171', // red   — Impossible
  E: '#facc15', // yellow — Either
};

function permAbbrev(permissions) {
  if (!permissions) return '?';
  const p = String(permissions).trim();
  if (p === 'Signature') return 'S';
  if (p === 'Proof')     return 'P';
  if (p === 'None')      return 'N';
  if (p === 'Impossible') return 'I';
  if (p === 'Either')    return 'E';
  return (p[0] || '?').toUpperCase();
}

function permColor(abbrev) {
  return PERM_COLORS[abbrev] || '#94a3b8';
}

// ---------------------------------------------------------------------------
// Radial layout: arrange N nodes evenly on a circle
// ---------------------------------------------------------------------------
function radialPositions(n, cx, cy, r) {
  const positions = [];
  for (let i = 0; i < n; i++) {
    const angle = (2 * Math.PI * i) / n - Math.PI / 2; // start from top
    positions.push({
      x: cx + r * Math.cos(angle),
      y: cy + r * Math.sin(angle),
    });
  }
  return positions;
}

// ---------------------------------------------------------------------------
// SVG rendering — pure function, returns an SVG string
// ---------------------------------------------------------------------------
function buildSVG(nodes, edges, opts = {}) {
  const {
    width = 560,
    height = 420,
    nodeR = 22,
    compact = false,
  } = opts;

  const cx = width / 2;
  const cy = height / 2;
  const layoutR = Math.min(cx, cy) - nodeR - 32;

  const n = nodes.length;
  // Build index map: cell_id → position index
  const idxMap = new Map(nodes.map((nd, i) => [nd.cell_id, i]));
  const positions = radialPositions(n, cx, cy, n === 1 ? 0 : layoutR);

  // Arrowhead marker defs per permission color
  const markerColors = [...new Set(edges.map(e => permColor(permAbbrev(e.permissions))))];
  const markerDefs = markerColors.map(color => {
    const mid = color.replace('#', 'm');
    return `<marker id="arr-${mid}" markerWidth="8" markerHeight="8" refX="7" refY="3"
        orient="auto" markerUnits="strokeWidth">
      <path d="M0,0 L8,3 L0,6 Z" fill="${color}" opacity="0.9"/>
    </marker>`;
  }).join('\n');

  // --- Edge SVG elements ---
  // For parallel edges (same from/to pair, different slots), we offset them
  // slightly using a curved path so they don't overlap.
  const edgeCountMap = new Map(); // key "from:to" → count so far

  const edgeSVG = edges.map((edge) => {
    const fi = idxMap.get(edge.from);
    const ti = idxMap.get(edge.to);
    if (fi == null || ti == null) return '';

    const fp = positions[fi];
    const tp = positions[ti];

    // Self-loop
    if (fi === ti) {
      const loopR = nodeR + 12;
      const lx = fp.x + nodeR + loopR * 0.6;
      const ly = fp.y - nodeR;
      const abbrev = permAbbrev(edge.permissions);
      const color = permColor(abbrev);
      const mid = color.replace('#', 'm');
      const label = abbrev;
      const tooltip = `slot ${edge.slot} · ${edge.permissions}`;
      return `<g class="pdg-edge" data-tooltip="${tooltip}">
        <ellipse cx="${lx}" cy="${ly}" rx="${loopR * 0.7}" ry="${loopR * 0.5}"
          fill="none" stroke="${color}" stroke-width="1.5" opacity="0.7"
          marker-end="url(#arr-${mid})"/>
        <text x="${lx}" y="${ly}" text-anchor="middle" dominant-baseline="middle"
          fill="${color}" font-size="10" font-family="ui-monospace,monospace">${label}</text>
      </g>`;
    }

    // Offset for parallel edges
    const pairKey = `${edge.from}:${edge.to}`;
    const prevCount = edgeCountMap.get(pairKey) || 0;
    edgeCountMap.set(pairKey, prevCount + 1);

    // Direction vector
    const dx = tp.x - fp.x;
    const dy = tp.y - fp.y;
    const dist = Math.sqrt(dx * dx + dy * dy) || 1;
    const nx = -dy / dist; // normal
    const ny = dx / dist;

    // Push source/target to circle boundary
    const sx = fp.x + (dx / dist) * nodeR;
    const sy = fp.y + (dy / dist) * nodeR;
    const ex = tp.x - (dx / dist) * (nodeR + 4); // +4 for arrowhead
    const ey = tp.y - (dy / dist) * (nodeR + 4);

    // Curve offset for parallel edges
    const offset = prevCount * 14;
    const midX = (sx + ex) / 2 + nx * offset;
    const midY = (sy + ey) / 2 + ny * offset;

    const abbrev = permAbbrev(edge.permissions);
    const color = permColor(abbrev);
    const mid = color.replace('#', 'm');
    const tooltip = `slot ${edge.slot} · ${edge.permissions}`;

    // Label at midpoint of the curve
    const lx = midX;
    const ly = midY;

    return `<g class="pdg-edge" data-tooltip="${tooltip}">
      <path d="M${sx},${sy} Q${midX},${midY} ${ex},${ey}"
        fill="none" stroke="${color}" stroke-width="1.5" opacity="0.75"
        marker-end="url(#arr-${mid})"/>
      <rect x="${lx - 8}" y="${ly - 8}" width="16" height="16" rx="3"
        fill="rgba(10,15,13,0.7)"/>
      <text x="${lx}" y="${ly}" text-anchor="middle" dominant-baseline="middle"
        fill="${color}" font-size="10" font-family="ui-monospace,monospace"
        font-weight="bold">${abbrev}</text>
    </g>`;
  }).join('\n');

  // --- Node SVG elements ---
  const nodeSVG = nodes.map((nd, i) => {
    const p = positions[i];
    const named = !!nd.agent_name;
    const fill = named ? '#166534' : '#1e293b';
    const stroke = named ? '#4ade80' : '#475569';
    const textColor = named ? '#4ade80' : '#94a3b8';
    const label = nd.agent_name ? nd.agent_name : shortHex(nd.cell_id, 6);
    const tooltip = nd.cell_id;
    const navigateUri = `pyana://cell/${nd.cell_id}`;
    return `<g class="pdg-node" data-tooltip="${tooltip}" data-uri="${navigateUri}"
        style="cursor:pointer">
      <circle cx="${p.x}" cy="${p.y}" r="${nodeR}"
        fill="${fill}" stroke="${stroke}" stroke-width="2"/>
      <text x="${p.x}" y="${p.y}" text-anchor="middle" dominant-baseline="middle"
        fill="${textColor}" font-size="${named ? 10 : 8}" font-family="ui-monospace,monospace"
        font-weight="600">${label}</text>
    </g>`;
  }).join('\n');

  // --- Legend ---
  const legendItems = [
    ['#4ade80', 'named cell'],
    ['#475569', 'anonymous cell'],
    ['', ''],
    ...Object.entries(PERM_COLORS).map(([k, v]) => [v, `perm:${k}`]),
  ].filter(([c]) => c);
  const legendSVG = legendItems.map(([color, label], idx) => {
    const lx = 12;
    const ly = height - 12 - (legendItems.length - idx - 1) * 16;
    return `<circle cx="${lx + 5}" cy="${ly - 4}" r="4" fill="${color}" opacity="0.8"/>
      <text x="${lx + 14}" y="${ly - 1}" fill="#94a3b8" font-size="9"
        font-family="ui-monospace,monospace">${label}</text>`;
  }).join('\n');

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}"
    viewBox="0 0 ${width} ${height}" style="background:#0a0f0d;border-radius:8px;display:block;">
  <defs>${markerDefs}</defs>
  <!-- edges (drawn first, under nodes) -->
  ${edgeSVG}
  <!-- nodes -->
  ${nodeSVG}
  <!-- legend -->
  ${legendSVG}
</svg>`;
}

// ---------------------------------------------------------------------------
// Thumbnail SVG for compact mode
// ---------------------------------------------------------------------------
function buildThumbnailSVG(nodes, edges) {
  const w = 80, h = 60;
  const cx = w / 2, cy = h / 2;
  const r = Math.min(cx, cy) - 8;
  const n = nodes.length;
  const positions = radialPositions(n, cx, cy, n === 1 ? 0 : r);
  const idxMap = new Map(nodes.map((nd, i) => [nd.cell_id, i]));

  const nodesSVG = nodes.map((nd, i) => {
    const p = positions[i];
    const named = !!nd.agent_name;
    const fill = named ? '#166534' : '#1e293b';
    const stroke = named ? '#4ade80' : '#475569';
    return `<circle cx="${p.x}" cy="${p.y}" r="5" fill="${fill}" stroke="${stroke}" stroke-width="1"/>`;
  }).join('');

  const edgesSVG = edges.map(edge => {
    const fi = idxMap.get(edge.from);
    const ti = idxMap.get(edge.to);
    if (fi == null || ti == null || fi === ti) return '';
    const fp = positions[fi], tp = positions[ti];
    const color = permColor(permAbbrev(edge.permissions));
    return `<line x1="${fp.x}" y1="${fp.y}" x2="${tp.x}" y2="${tp.y}" stroke="${color}" stroke-width="1" opacity="0.6"/>`;
  }).join('');

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${w}" height="${h}"
    viewBox="0 0 ${w} ${h}" style="background:#0a0f0d;border-radius:4px;vertical-align:middle;">
    ${edgesSVG}${nodesSVG}
  </svg>`;
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class PyanaDelegationGraph extends InspectorBase {
  static get observedAttributes() { return ['uri', 'mode']; }

  _render() {
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const mode = this.getAttribute('mode') || 'default';
    const compact = mode === 'compact';

    // Fetch graph from wasm directly (no per-object signal; full graph read)
    let graph = { nodes: [], edges: [] };
    try {
      graph = this._runtime._wasm.get_delegation_graph(this._runtime._handle) || graph;
    } catch (e) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">delegation-graph: ${e.message}</div>`;
      return;
    }

    const { nodes, edges } = graph;

    // --- Tooltip element (shared, appended to body) ---
    let tooltipEl = document.getElementById('pdg-tooltip');
    if (!tooltipEl) {
      tooltipEl = document.createElement('div');
      tooltipEl.id = 'pdg-tooltip';
      tooltipEl.style.cssText = [
        'position:fixed', 'z-index:9999', 'pointer-events:none',
        'background:#121b16', 'color:#e4ddd0', 'border:1px solid #2a302d',
        'border-radius:5px', 'padding:4px 10px', 'font:12px/1.5 ui-monospace,monospace',
        'white-space:nowrap', 'opacity:0', 'transition:opacity 0.1s',
        'max-width:340px', 'word-break:break-all',
      ].join(';');
      document.body.appendChild(tooltipEl);
    }

    if (compact) {
      // Compact: "N cells, M caps" + tiny SVG thumbnail
      const wrapper = document.createElement('span');
      wrapper.className = 'pyana-inspector pyana-inspector--compact pdg-compact';
      wrapper.style.cssText = 'display:inline-flex;align-items:center;gap:10px;';
      wrapper.innerHTML =
        buildThumbnailSVG(nodes, edges) +
        `<span style="font-size:0.85rem;color:var(--fg-dim,#8a948f);">` +
          `${nodes.length} cell${nodes.length !== 1 ? 's' : ''}, ` +
          `${edges.length} cap${edges.length !== 1 ? 's' : ''}` +
        `</span>`;
      this.appendChild(wrapper);
      return;
    }

    // --- Default mode: full SVG graph ---
    const container = document.createElement('div');
    container.className = 'pyana-inspector pyana-inspector--cell pdg-container';
    container.style.cssText = 'padding:0;overflow:hidden;';

    // Header bar
    const header = document.createElement('header');
    header.style.cssText = 'padding:10px 14px;display:flex;justify-content:space-between;align-items:baseline;';
    header.innerHTML =
      `<span class="pyana-inspector__kind" style="background:var(--accent,#5b8a5a);color:#0a0f0d;padding:2px 8px;border-radius:3px;font-size:0.75rem;text-transform:uppercase;letter-spacing:0.04em;">delegation graph</span>` +
      `<span style="font-size:0.8rem;color:var(--fg-dim,#8a948f);font-family:ui-monospace,monospace;">` +
        `${nodes.length} cell${nodes.length !== 1 ? 's' : ''} · ` +
        `${edges.length} cap${edges.length !== 1 ? 's' : ''}` +
      `</span>`;
    container.appendChild(header);

    if (nodes.length === 0) {
      const empty = document.createElement('div');
      empty.className = 'pyana-inspector pyana-inspector--empty';
      empty.style.cssText = 'margin:0;border-radius:0 0 6px 6px;';
      empty.textContent = 'no cells in this runtime';
      container.appendChild(empty);
      this.appendChild(container);
      return;
    }

    // Build SVG
    const svgStr = buildSVG(nodes, edges);
    const svgWrapper = document.createElement('div');
    svgWrapper.innerHTML = svgStr;
    const svgEl = svgWrapper.firstElementChild;
    svgEl.style.width = '100%';
    svgEl.style.height = 'auto';
    svgEl.setAttribute('preserveAspectRatio', 'xMidYMid meet');
    container.appendChild(svgEl);

    // --- Interactivity: tooltip + click ---
    function showTooltip(text, ev) {
      tooltipEl.textContent = text;
      tooltipEl.style.opacity = '1';
      moveTooltip(ev);
    }
    function moveTooltip(ev) {
      const x = Math.min(ev.clientX + 14, window.innerWidth - 360);
      const y = Math.max(ev.clientY - 28, 4);
      tooltipEl.style.left = x + 'px';
      tooltipEl.style.top = y + 'px';
    }
    function hideTooltip() {
      tooltipEl.style.opacity = '0';
    }

    // Delegate to SVG group elements
    svgEl.addEventListener('mouseover', ev => {
      const g = ev.target.closest('.pdg-node, .pdg-edge');
      if (!g) return hideTooltip();
      const tip = g.dataset.tooltip;
      if (tip) showTooltip(tip, ev);
    });
    svgEl.addEventListener('mousemove', ev => {
      if (tooltipEl.style.opacity === '1') moveTooltip(ev);
    });
    svgEl.addEventListener('mouseleave', () => hideTooltip());

    svgEl.addEventListener('click', ev => {
      const g = ev.target.closest('.pdg-node');
      if (!g || !g.dataset.uri) return;
      this.dispatchEvent(new CustomEvent('pyana:navigate', {
        bubbles: true,
        composed: true,
        detail: { uri: g.dataset.uri },
      }));
    });

    this.appendChild(container);

    // Subscribe to runtime version changes so we re-render on mutations.
    // We use a minimal effect: watch version.value, re-render if changed.
    const { effect } = this._api;
    let lastVersion = this._runtime.version.value;
    this._dispose = effect(() => {
      const v = this._runtime.version.value;
      if (v !== lastVersion) {
        lastVersion = v;
        this._render();
      }
    });
  }
}

if (!customElements.get('pyana-delegation-graph')) {
  customElements.define('pyana-delegation-graph', PyanaDelegationGraph);
}
