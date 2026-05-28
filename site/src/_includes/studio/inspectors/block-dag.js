/**
 * <dregg-block-dag uri="dregg://federation/<idx>"> or
 * <dregg-block-dag uri="dregg://block-dag/<idx>"> — DAG visualizer for a
 * federation's blocklace.
 *
 * Reads ACTUAL federation block data via the wasm bindings exposed by
 * InMemoryRuntime:
 *   - runtime.getFederation(fedIdx)        → federation state + height
 *   - runtime._wasm.list_federation_blocks(handle, fedIdx) → compact block list
 *   - runtime._wasm.get_federation_block(handle, fedIdx, height) → full block
 *
 * Visual design:
 *   - SVG layout: blocks as rectangles arranged top-to-bottom by height
 *     (newest at top, genesis at bottom). Multiple blocks at the same height
 *     stack horizontally (fork state).
 *   - Each block: small rectangle colored by proposer (deterministic from pubkey).
 *     Truncated block hash inside.
 *   - Edges: parent-pointer arrows from each block down to its parent.
 *   - QC threshold indicator ("3/4") with green outline when finalized, amber
 *     when pending, red when failed.
 *   - Hover: tooltip with full hash + proposer pubkey + signature count + events.
 *   - Click: emits dregg:navigate CustomEvent with
 *     detail: { uri: "dregg://block/<fed_idx>/<height>" }
 *
 * Compact mode: text summary "H=42 · 4 nodes · last-finalized=39" + small
 * thumbnail SVG of the DAG shape.
 *
 * Reactivity: subscribes to runtime.getFederation(fedIdx) signal so the DAG
 * re-renders when new blocks land. Uses effect(() => render(...)) per the
 * delegation-graph.js pattern.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, dreggHref, renderParseError, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Colour derivation — deterministic from proposer pubkey (or "genesis")
// ---------------------------------------------------------------------------
const PROPOSER_PALETTE = [
  '#5b8a5a', // green
  '#60a5fa', // blue
  '#f59e0b', // amber
  '#a78bfa', // violet
  '#34d399', // emerald
  '#f87171', // red
  '#fb923c', // orange
  '#38bdf8', // sky
  '#e879f9', // fuchsia
  '#a3e635', // lime
];

function proposerColor(proposer) {
  if (!proposer) return PROPOSER_PALETTE[0];
  // Simple hash: sum of char codes modulo palette length
  let h = 0;
  for (let i = 0; i < proposer.length; i++) h = (h * 31 + proposer.charCodeAt(i)) >>> 0;
  return PROPOSER_PALETTE[h % PROPOSER_PALETTE.length];
}

// ---------------------------------------------------------------------------
// QC status from a block
// ---------------------------------------------------------------------------
function qcStatus(block) {
  // get_federation_block returns { num_votes, qc_threshold }.
  // A block is considered finalized when num_votes >= qc_threshold.
  // proposeBlock returns { finalized: bool } but that's on the proposal
  // result, not on the enriched block object — we rely on num_votes here.
  if (!block) return 'unknown';
  if (block.finalized === true) return 'finalized';
  // Node blocklace surface: a block in /api/blocklace/blocks that carries a
  // finality_round has been finalized by consensus (solo heartbeat blocks are
  // final with num_votes 0 — finality there is by the single authority, not a
  // multi-vote QC). Honor that real signal.
  if (block.finality_round != null && Number(block.finality_round) >= 0 && block.kind != null) return 'finalized';
  const threshold = Number(block.qc_threshold ?? 0);
  const votes     = Number(block.num_votes ?? block.signature_count ?? block.signatures?.length ?? 0);
  if (threshold > 0 && votes >= threshold) return 'finalized';
  if (threshold > 0 && votes > 0) return 'pending';
  return 'pending';
}

function qcStatusColor(status) {
  if (status === 'finalized') return '#4ade80'; // green
  if (status === 'failed')    return '#f87171'; // red
  return '#fbbf24'; // amber — pending
}

function inspectorLink(uri, label) {
  return `<a class="dregg-inspector__link" href="${dreggHref(uri)}" data-dregg-uri="${uri}" title="${uri}"><code>${label}</code></a>`;
}

// ---------------------------------------------------------------------------
// Layout constants
// ---------------------------------------------------------------------------
const BLOCK_W    = 88;  // rectangle width
const BLOCK_H    = 32;  // rectangle height
const LANE_GAP   = 18;  // horizontal gap between blocks at same height
const HEIGHT_GAP = 54;  // vertical distance between height rows
const PAD        = 24;  // canvas padding

// ---------------------------------------------------------------------------
// Layout: compute (x,y) positions for each block
// Returns { positions: Map<hash, {x,y}>, svgW, svgH }
// ---------------------------------------------------------------------------
function computeLayout(blocks) {
  if (!blocks.length) return { positions: new Map(), svgW: 200, svgH: 80 };

  // Group by height
  const byHeight = new Map();
  for (const b of blocks) {
    const h = Number(b.height);
    if (!byHeight.has(h)) byHeight.set(h, []);
    byHeight.get(h).push(b);
  }

  const heights = [...byHeight.keys()].sort((a, b) => a - b);
  const maxHeight = heights[heights.length - 1];
  const minHeight = heights[0];

  // Canvas height: one row per integer height level (sparse is fine)
  const totalRows = maxHeight - minHeight + 1;
  const svgH = PAD * 2 + totalRows * HEIGHT_GAP + BLOCK_H;

  // Determine the maximum number of blocks at any height (for canvas width)
  let maxCount = 1;
  for (const grp of byHeight.values()) maxCount = Math.max(maxCount, grp.length);
  const svgW = PAD * 2 + maxCount * BLOCK_W + (maxCount - 1) * LANE_GAP;

  const positions = new Map();

  for (const [h, grp] of byHeight) {
    const rowCount = grp.length;
    const totalW   = rowCount * BLOCK_W + (rowCount - 1) * LANE_GAP;
    const startX   = (svgW - totalW) / 2;
    // newest at top: invert y so highest height is at the top
    const rowIdx   = maxHeight - h;
    const y        = PAD + rowIdx * HEIGHT_GAP;

    grp.forEach((b, i) => {
      const x = startX + i * (BLOCK_W + LANE_GAP);
      positions.set(String(b.block_hash || b.height), { x, y });
    });
  }

  return { positions, svgW, svgH, byHeight, maxHeight, minHeight };
}

// ---------------------------------------------------------------------------
// Arrow path from child block rect to parent block rect
// ---------------------------------------------------------------------------
function arrowPath(cx, cy, px, py) {
  // centre-bottom of child → centre-top of parent
  const x1 = cx + BLOCK_W / 2;
  const y1 = cy + BLOCK_H;
  const x2 = px + BLOCK_W / 2;
  const y2 = py;
  const mid = (y1 + y2) / 2;
  return `M${x1},${y1} C${x1},${mid} ${x2},${mid} ${x2},${y2}`;
}

// ---------------------------------------------------------------------------
// Full SVG (default mode)
// ---------------------------------------------------------------------------
function buildDAGSvg(blocks, fedIdx, opts = {}) {
  const { compact = false } = opts;

  if (!blocks.length) {
    const w = compact ? 80 : 300;
    const h = compact ? 50 : 80;
    return `<svg xmlns="http://www.w3.org/2000/svg" width="${w}" height="${h}"
      viewBox="0 0 ${w} ${h}" style="background:#0a0f0d;border-radius:${compact ? 4 : 8}px;display:block;">
      <text x="${w/2}" y="${h/2}" text-anchor="middle" dominant-baseline="middle"
        fill="#475569" font-size="${compact ? 9 : 12}" font-family="ui-monospace,monospace">no blocks</text>
    </svg>`;
  }

  const { positions, svgW, svgH } = computeLayout(blocks);

  // Build a hash→block lookup
  const byHash = new Map();
  for (const b of blocks) byHash.set(String(b.block_hash || b.height), b);

  // --- Arrowhead marker ---
  const markerDef = `<marker id="bdag-arr" markerWidth="7" markerHeight="7" refX="6" refY="3"
      orient="auto" markerUnits="strokeWidth">
    <path d="M0,0 L7,3 L0,6 Z" fill="#475569" opacity="0.8"/>
  </marker>`;

  // --- Edges ---
  const ZERO_HASH = '0'.repeat(64);
  const edgesSVG = blocks.map(b => {
    const childKey = String(b.block_hash || b.height);
    // wasm uses "prev_hash" for the parent pointer (not "parent_hash").
    // Genesis blocks have prev_hash = 000...0 — skip those (no parent in DAG).
    const prevHash = b.prev_hash || b.parent_hash || '';
    if (!prevHash || prevHash === ZERO_HASH) return '';
    const parentKey = String(prevHash);
    const cPos = positions.get(childKey);
    const pPos = positions.get(parentKey);
    if (!cPos || !pPos) return '';
    const d = arrowPath(cPos.x, cPos.y, pPos.x, pPos.y);
    return `<path d="${d}" fill="none" stroke="#2a302d" stroke-width="1.5"
      marker-end="url(#bdag-arr)" opacity="0.7"/>`;
  }).join('\n');

  // --- Blocks ---
  const blocksSVG = blocks.map(b => {
    const key     = String(b.block_hash || b.height);
    const pos     = positions.get(key);
    if (!pos) return '';
    const { x, y } = pos;

    // proposer is a numeric node index from wasm; convert to string for colour
    const proposer    = String(b.proposer ?? '');
    const fillColor   = proposerColor(proposer);
    const status      = qcStatus(b);
    const strokeColor = qcStatusColor(status);
    const threshold   = Number(b.qc_threshold ?? 0);
    const votes       = Number(b.num_votes ?? b.signature_count ?? b.signatures?.length ?? 0);
    const qcLabel     = threshold > 0 ? `${votes}/${threshold}` : '';
    const hashLabel   = shortHex(b.block_hash || '', 8);
    // num_events on compact summary; events.length on full block
    const eventCount  = Number(b.num_events ?? b.events?.length ?? b.event_count ?? 0);

    // Tooltip: escape double quotes for data attribute
    const tooltipParts = [
      `h=${b.height}`,
      `hash: ${b.block_hash || '?'}`,
      `proposer: node ${proposer || '?'}`,
      `votes: ${votes}${threshold ? '/' + threshold : ''}`,
      `events: ${eventCount}`,
      `status: ${status}`,
    ];
    const tooltip = tooltipParts.join(' | ').replace(/"/g, '&quot;');
    const navUri  = `dregg://block/${fedIdx}/${b.height}`;

    return `<g class="bdag-block" data-tooltip="${tooltip}" data-uri="${navUri}" style="cursor:pointer">
      <rect x="${x}" y="${y}" width="${BLOCK_W}" height="${BLOCK_H}" rx="4"
        fill="${fillColor}22" stroke="${strokeColor}" stroke-width="2"/>
      <text x="${x + BLOCK_W/2}" y="${y + BLOCK_H/2 - 5}"
        text-anchor="middle" dominant-baseline="middle"
        fill="${fillColor}" font-size="9" font-family="ui-monospace,monospace"
        font-weight="600">${hashLabel}</text>
      <text x="${x + BLOCK_W/2}" y="${y + BLOCK_H/2 + 7}"
        text-anchor="middle" dominant-baseline="middle"
        fill="#8a948f" font-size="8" font-family="ui-monospace,monospace">h=${b.height} ${qcLabel}</text>
    </g>`;
  }).join('\n');

  // --- Height labels (left gutter) ---
  const heightLabels = [...new Map(blocks.map(b => {
    const key  = String(b.block_hash || b.height);
    const pos  = positions.get(key);
    return [Number(b.height), pos];
  })).entries()].map(([h, pos]) => {
    if (!pos) return '';
    return `<text x="4" y="${pos.y + BLOCK_H/2 + 4}"
      dominant-baseline="middle" fill="#475569"
      font-size="9" font-family="ui-monospace,monospace">h=${h}</text>`;
  }).join('\n');

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${svgW}" height="${svgH}"
    viewBox="0 0 ${svgW} ${svgH}"
    style="background:#0a0f0d;border-radius:8px;display:block;min-width:200px;">
  <defs>${markerDef}</defs>
  ${edgesSVG}
  ${blocksSVG}
  ${heightLabels}
</svg>`;
}

// ---------------------------------------------------------------------------
// Thumbnail SVG for compact mode
// ---------------------------------------------------------------------------
function buildThumbnailSVG(blocks) {
  const W = 80, H = 60;

  if (!blocks.length) {
    return `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}"
      viewBox="0 0 ${W} ${H}" style="background:#0a0f0d;border-radius:4px;vertical-align:middle;">
      <text x="${W/2}" y="${H/2}" text-anchor="middle" dominant-baseline="middle"
        fill="#475569" font-size="8" font-family="ui-monospace,monospace">—</text>
    </svg>`;
  }

  // Minimal layout: dots arranged by height
  const byHeight = new Map();
  for (const b of blocks) {
    const h = Number(b.height);
    if (!byHeight.has(h)) byHeight.set(h, []);
    byHeight.get(h).push(b);
  }
  const heights = [...byHeight.keys()].sort((a, b) => a - b);
  const maxH = heights[heights.length - 1];
  const minH = heights[0];
  const levels = maxH - minH + 1;

  const dotR  = 4;
  const stepY = levels > 1 ? (H - PAD) / (levels - 1) : H / 2;

  const dotsSVG = [];
  const linesSVG = [];

  const posMap = new Map();
  for (const [h, grp] of byHeight) {
    const rowIdx = maxH - h;
    const y = PAD / 2 + rowIdx * stepY;
    const startX = (W - grp.length * (dotR * 2 + 2)) / 2 + dotR;
    grp.forEach((b, i) => {
      const x = startX + i * (dotR * 2 + 4);
      const key = String(b.block_hash || b.height);
      posMap.set(key, { x, y });
      const color = proposerColor(b.proposer || '');
      const status = qcStatus(b);
      const strokeC = qcStatusColor(status);
      dotsSVG.push(`<circle cx="${x}" cy="${y}" r="${dotR}"
        fill="${color}44" stroke="${strokeC}" stroke-width="1.2"/>`);
    });
  }

  // Draw parent edges as thin lines (skip genesis blocks with zero prev_hash)
  const ZERO_HASH_T = '0'.repeat(64);
  for (const b of blocks) {
    const childKey  = String(b.block_hash || b.height);
    const prevHash  = b.prev_hash || b.parent_hash || '';
    if (!prevHash || prevHash === ZERO_HASH_T) continue;
    const parentKey = String(prevHash);
    const cPos = posMap.get(childKey);
    const pPos = posMap.get(parentKey);
    if (cPos && pPos) {
      linesSVG.push(`<line x1="${cPos.x}" y1="${cPos.y}" x2="${pPos.x}" y2="${pPos.y}"
        stroke="#2a302d" stroke-width="1" opacity="0.7"/>`);
    }
  }

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}"
    viewBox="0 0 ${W} ${H}" style="background:#0a0f0d;border-radius:4px;vertical-align:middle;">
    ${linesSVG.join('')}${dotsSVG.join('')}
  </svg>`;
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class DreggBlockDag extends InspectorBase {
  static get observedAttributes() { return ['uri', 'mode']; }

  _render() {
    const { effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';
    const compact = mode === 'compact';

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (!parsed) {
      renderParseError(this, refAttr, parsed, 'federation');
      return;
    }
    if (parsed.kind !== 'federation' && parsed.kind !== 'block-dag') {
      renderParseError(this, refAttr, parsed, 'federation');
      return;
    }

    const fedIdx = Number(parsed.id);

    // Subscribe to federation signal so we re-render on new blocks. Also grab
    // the runtime's block-list signal (RemoteRuntime path) so we stay reactive
    // to new blocks arriving over HTTP polling.
    const fedSig = this._runtime.getFederation(fedIdx);
    const blocksSig = typeof this._runtime.listBlocks === 'function' ? this._runtime.listBlocks() : null;

    this._dispose = effect(() => {
      // Reading fedSig.value registers this effect as a dep.
      const fedState = fedSig.value;
      const blockList = blocksSig ? blocksSig.value : null; // dep for reactivity
      this._renderContent(fedIdx, fedState, compact, blockList);
    });
  }

  _renderContent(fedIdx, fedState, compact, blockList) {
    this.replaceChildren();

    if (!fedState) {
      this.innerHTML = `<div class="dregg-inspector dregg-inspector--empty">
        <div class="dregg-inspector__empty-title">Federation not found</div>
        <div class="dregg-inspector__empty-body">Federation <code>#${fedIdx}</code> is not registered in this runtime.</div>
      </div>`;
      return;
    }

    // Two real sources, no JS simulation either way:
    //  - in-memory runtime: wasm list_federation_blocks + get_federation_block
    //    (compact summaries enriched with QC data).
    //  - RemoteRuntime: the node's /api/blocklace/blocks (already enriched with
    //    block_hash / prev_hash / proposer / votes), via runtime.listBlocks().
    let blocks;
    const hasWasm = this._runtime._wasm && this._runtime._handle != null;
    if (hasWasm) {
      let rawBlocks = [];
      try {
        rawBlocks = this._runtime._wasm.list_federation_blocks(this._runtime._handle, fedIdx) || [];
      } catch (e) {
        this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">list_federation_blocks: ${e.message}</div>`;
        return;
      }
      blocks = rawBlocks.map(b => {
        try {
          const full = this._runtime._wasm.get_federation_block(this._runtime._handle, fedIdx, BigInt(b.height));
          return full ? { ...b, ...full, fed_index: fedIdx } : { ...b, fed_index: fedIdx };
        } catch {
          return { ...b, fed_index: fedIdx };
        }
      });
    } else {
      // Remote: filter the live block list to this federation (node is fed 0).
      const all = blockList || [];
      blocks = all
        .filter(b => Number(b.fed_index ?? b.federation_index ?? 0) === fedIdx)
        .map(b => ({ ...b, fed_index: fedIdx }));
    }

    // Sort ascending by height for layout
    blocks.sort((a, b) => Number(a.height) - Number(b.height));

    if (compact) {
      this._renderCompact(fedIdx, fedState, blocks);
    } else {
      this._renderDefault(fedIdx, fedState, blocks);
    }
  }

  _renderCompact(fedIdx, fedState, blocks) {
    const lastFinalized = blocks.filter(b => qcStatus(b) === 'finalized');
    const lastFinalHeight = lastFinalized.length
      ? lastFinalized[lastFinalized.length - 1].height
      : '—';

    const summaryText =
      `H=${fedState.height} · ${fedState.num_nodes} nodes · last-finalized=${lastFinalHeight}`;

    const wrapper = document.createElement('span');
    wrapper.className = 'dregg-inspector dregg-inspector--compact bdag-compact';
    wrapper.style.cssText = 'display:inline-flex;align-items:center;gap:10px;';
    wrapper.innerHTML =
      buildThumbnailSVG(blocks) +
      `<span style="font-size:0.85rem;color:var(--fg-dim,#8a948f);">${summaryText}</span>`;
    this.appendChild(wrapper);
  }

  _renderDefault(fedIdx, fedState, blocks) {
    const container = document.createElement('div');
    container.className = 'dregg-inspector dregg-inspector--cell bdag-container';
    container.style.cssText = 'padding:0;overflow:hidden;';

    // Header
    const header = document.createElement('header');
    header.style.cssText = 'padding:10px 14px;display:flex;justify-content:space-between;align-items:baseline;';
    const lastFinalized = blocks.filter(b => qcStatus(b) === 'finalized');
    const latest = blocks[blocks.length - 1];
    header.innerHTML =
      `<span class="dregg-inspector__kind">block DAG</span>` +
      `<code class="dregg-inspector__id">fed #${fedIdx}</code>` +
      `<span class="dregg-inspector__meta">` +
        `fed #${fedIdx} · h=${fedState.height} · ${fedState.num_nodes} nodes · ` +
        `${blocks.length} block${blocks.length !== 1 ? 's' : ''} · ` +
        `${lastFinalized.length} finalized` +
      `</span>`;
    container.appendChild(header);

    const summary = document.createElement('div');
    summary.className = 'dregg-inspector__summary';
    summary.style.margin = '0 12px 10px';
    summary.innerHTML = [
      `<div><span>Height</span><strong>${fedState.height ?? 0}</strong></div>`,
      `<div><span>Blocks</span><strong>${blocks.length}</strong></div>`,
      `<div><span>Finalized</span><strong>${lastFinalized.length}</strong></div>`,
      `<div><span>Head</span><strong title="${latest?.block_hash || ''}">${latest ? shortHex(latest.block_hash || '', 10) : 'none'}</strong></div>`,
    ].join('');
    container.appendChild(summary);

    if (blocks.length === 0) {
      const empty = document.createElement('div');
      empty.className = 'dregg-inspector dregg-inspector--empty';
      empty.style.cssText = 'margin:0;border-radius:0 0 6px 6px;';
      empty.innerHTML = `<div class="dregg-inspector__empty-title">No blocks in this DAG</div>
        <div class="dregg-inspector__empty-body">Federation <code>#${fedIdx}</code> exists, but the runtime has no block records to draw yet.</div>
        <div class="dregg-inspector__empty-actions">${inspectorLink(`dregg://federation/${fedIdx}`, 'open federation')}</div>`;
      container.appendChild(empty);
      this.appendChild(container);
      return;
    }

    // Build SVG string
    const svgStr = buildDAGSvg(blocks, fedIdx);
    const svgWrapper = document.createElement('div');
    svgWrapper.style.cssText = 'overflow-x:auto;padding:12px;';
    svgWrapper.innerHTML = svgStr;
    const svgEl = svgWrapper.querySelector('svg');
    if (svgEl) {
      svgEl.style.maxWidth = '100%';
      svgEl.style.height   = 'auto';

      // --- Tooltip ---
      let tooltipEl = document.getElementById('bdag-tooltip');
      if (!tooltipEl) {
        tooltipEl = document.createElement('div');
        tooltipEl.id = 'bdag-tooltip';
        tooltipEl.style.cssText = [
          'position:fixed', 'z-index:9999', 'pointer-events:none',
          'background:#121b16', 'color:#e4ddd0', 'border:1px solid #2a302d',
          'border-radius:5px', 'padding:4px 10px',
          'font:12px/1.5 ui-monospace,monospace',
          'white-space:pre', 'opacity:0', 'transition:opacity 0.1s',
          'max-width:380px', 'word-break:break-all',
        ].join(';');
        document.body.appendChild(tooltipEl);
      }

      function showTooltip(text, ev) {
        // Replace | separators with newlines for readability
        tooltipEl.textContent = text.replace(/ \| /g, '\n');
        tooltipEl.style.opacity = '1';
        moveTooltip(ev);
      }
      function moveTooltip(ev) {
        const x = Math.min(ev.clientX + 14, window.innerWidth - 400);
        const y = Math.max(ev.clientY - 28, 4);
        tooltipEl.style.left = x + 'px';
        tooltipEl.style.top  = y + 'px';
      }
      function hideTooltip() { tooltipEl.style.opacity = '0'; }

      svgEl.addEventListener('mouseover', ev => {
        const g = ev.target.closest('.bdag-block');
        if (!g) return hideTooltip();
        const tip = g.dataset.tooltip;
        if (tip) showTooltip(tip, ev);
      });
      svgEl.addEventListener('mousemove', ev => {
        if (tooltipEl.style.opacity === '1') moveTooltip(ev);
      });
      svgEl.addEventListener('mouseleave', () => hideTooltip());

      // Click → navigate
      svgEl.addEventListener('click', ev => {
        const g = ev.target.closest('.bdag-block');
        if (!g || !g.dataset.uri) return;
        this.dispatchEvent(new CustomEvent('dregg:navigate', {
          bubbles: true,
          composed: true,
          detail: { uri: g.dataset.uri },
        }));
      });
    }

    container.appendChild(svgWrapper);

    // --- Legend ---
    const legend = document.createElement('div');
    legend.style.cssText =
      'padding:6px 14px 10px;display:flex;gap:16px;flex-wrap:wrap;font-size:0.75rem;' +
      'color:var(--fg-dim,#8a948f);font-family:ui-monospace,monospace;border-top:1px solid var(--line,#2a302d);';
    legend.innerHTML = [
      `<span style="color:#4ade80;">&#9632; finalized</span>`,
      `<span style="color:#fbbf24;">&#9632; pending</span>`,
      `<span style="color:#f87171;">&#9632; failed</span>`,
      `<span style="color:#8a948f;">rect color = proposer</span>`,
      inspectorLink(`dregg://federation/${fedIdx}`, 'open federation'),
      latest ? inspectorLink(`dregg://block/${fedIdx}/${latest.height}`, 'open head block') : '',
    ].join('');
    container.appendChild(legend);

    this.appendChild(container);
  }
}

if (!customElements.get('dregg-block-dag')) {
  customElements.define('dregg-block-dag', DreggBlockDag);
}
