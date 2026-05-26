/**
 * <pyana-blocklace-sim node-count="4" block-rate="1" mode="default">
 *
 * Self-contained Cordial Miners DAG simulator — no wasm, no protocol calls.
 * Ported from playground/sections/blocklace-sim.js with signal-based state and
 * the InspectorBase custom-element pattern.
 *
 * Attributes:
 *   node-count        — number of nodes (default 4)
 *   block-rate        — blocks produced per manual tick (default 1)
 *   mode              — "default" (full SVG + controls) | "compact" (summary line + thumbnail)
 *   equivocator-index — integer index of Byzantine node (default: null = disabled)
 *
 * Programmatic API (for tests):
 *   el.tick(n)        — advance simulation by n ticks; returns array of new blocks
 *   el.reset()        — reset simulation to empty state
 *   el.getState()     — { blocks, tauOrder, equivocations, wave, ticks }
 *
 * Does NOT extend InspectorBase — it has no uri/runtime dependency.
 * Follows the same connected/disconnected/attributeChangedCallback pattern.
 */

// ── constants ─────────────────────────────────────────────────────────────────

const NODE_COLORS = ['#6ba3c7', '#d99a3f', '#9bb87a', '#c77ab8', '#7ac7b8'];
const EQUIVOCATOR_COLOR = '#d4685c';
const TAU_HIGHLIGHT = 'rgba(255,220,100,0.18)';

// ── inline styles ─────────────────────────────────────────────────────────────

const CSS = `
  .pbs { font-family: var(--font-mono, ui-monospace, monospace); font-size: 0.82rem;
    display: flex; flex-direction: column; gap: var(--s3, 8px); }

  .pbs__controls { display: flex; flex-wrap: wrap; align-items: center; gap: 6px;
    padding: 6px 8px; background: var(--bg-raised, #1a1a1a);
    border: 1px solid var(--line, #333); border-radius: 3px; }

  .pbs__btn { padding: 3px 10px; border-radius: 3px; border: 1px solid var(--line, #444);
    background: var(--bg-raised, #222); color: var(--fg, #eee); cursor: pointer;
    font-family: inherit; font-size: 0.8rem; }
  .pbs__btn:hover:not(:disabled) { background: var(--bg-hover, #2a2a2a); }
  .pbs__btn:disabled { opacity: 0.4; cursor: default; }
  .pbs__btn--accent { background: var(--accent-soft, rgba(100,200,255,0.12));
    border-color: var(--accent, #64c8ff); color: var(--accent, #64c8ff); }

  .pbs__label { display: flex; align-items: center; gap: 4px; color: var(--fg-dim, #888);
    font-size: 0.78rem; }
  .pbs__label input[type=number] { width: 52px; padding: 2px 4px; border-radius: 2px;
    border: 1px solid var(--line, #444); background: var(--bg, #111); color: var(--fg, #eee);
    font-family: inherit; font-size: 0.78rem; }
  .pbs__label input[type=checkbox] { accent-color: var(--accent, #64c8ff); }

  .pbs__stats { display: flex; gap: 12px; flex-wrap: wrap;
    padding: 4px 8px; font-size: 0.75rem; color: var(--fg-dim, #888); }
  .pbs__stat-val { color: var(--fg, #eee); font-weight: 600; }

  .pbs__svg-wrap { overflow-x: auto; border: 1px solid var(--line, #333);
    border-radius: 3px; background: var(--bg, #111); min-height: 120px; }
  .pbs__empty { padding: 24px; color: var(--fg-dim, #888); font-style: italic;
    text-align: center; }

  .pbs__tau { padding: 4px 8px; font-size: 0.75rem; color: var(--fg-dim, #888); }
  .pbs__tau code { color: var(--accent, #64c8ff); }

  .pbs__compact { font-size: 0.82rem; color: var(--fg-dim, #aaa); display: flex;
    align-items: center; gap: 8px; }
  .pbs__compact code { color: var(--accent, #64c8ff); }

  .pbs__log { border: 1px solid var(--line, #333); border-radius: 3px;
    max-height: 100px; overflow-y: auto; }
  .pbs__log-hdr { padding: 3px 8px; font-size: 0.7rem; text-transform: uppercase;
    letter-spacing: 0.07em; color: var(--fg-dim, #888);
    border-bottom: 1px solid var(--line, #333);
    background: var(--bg-raised, #1a1a1a); }
  .pbs__log-entry { padding: 2px 8px; font-size: 0.75rem; }
  .pbs__log-entry--info    { color: var(--fg-dim, #888); }
  .pbs__log-entry--success { color: var(--success, #4db85a); }
  .pbs__log-entry--danger  { color: var(--danger, #e05c5c); }
`;

// ── simulation core ───────────────────────────────────────────────────────────

function createSim(nodeCount, equivocatorIndex) {
  return {
    nodeCount,
    equivocatorIndex: equivocatorIndex != null ? parseInt(equivocatorIndex) : null,
    blocks: [],
    nodes: Array.from({ length: nodeCount }, () => ({
      height: 0,
      tip: null,
    })),
    ticks: 0,
    wave: 0,
    tauOrder: [],
    equivocations: 0,
    log: [],
  };
}

/**
 * Advance the simulation by one tick. In each tick every node has an equal
 * chance of being the block producer (we randomly pick one). The equivocator
 * occasionally produces a second competing block at the same height.
 *
 * Tau ordering: blocks become tau-ordered once they cross the 2f+1 finality
 * threshold (i.e. have been referenced by a quorum of nodes).
 */
function simTick(sim) {
  const { nodeCount, equivocatorIndex } = sim;
  const threshold = Math.floor((nodeCount * 2) / 3) + 1;
  const newBlocks = [];

  const creatorIdx = Math.floor(Math.random() * nodeCount);
  const creator = sim.nodes[creatorIdx];

  // Predecessors: latest tips from all other nodes this creator has seen
  const predecessors = [];
  sim.nodes.forEach((node, idx) => {
    if (idx !== creatorIdx && node.tip !== null) {
      predecessors.push(node.tip);
    }
  });

  const block = {
    id: sim.blocks.length,
    creator: creatorIdx,
    height: creator.height,
    predecessors: predecessors.map(b => b.id),
    wave: sim.wave,
    hash: Math.floor(Math.random() * 0xFFFFFFFF).toString(16).padStart(8, '0'),
    isEquivocator: false,
    isFinal: false,
    signatures: Math.min(nodeCount, 1 + predecessors.length),
  };

  // Equivocation injection: ~20% chance per equivocator tick
  const isEquivocatorCreator = equivocatorIndex != null && creatorIdx === parseInt(equivocatorIndex);
  if (isEquivocatorCreator && sim.blocks.length > 0 && Math.random() < 0.2) {
    block.isEquivocator = true;
    sim.equivocations++;
    // Also emit a sibling block at the same height (the "double sign")
    const sibling = {
      id: sim.blocks.length + 1,
      creator: creatorIdx,
      height: creator.height,
      predecessors: predecessors.map(b => b.id),
      wave: sim.wave,
      hash: Math.floor(Math.random() * 0xFFFFFFFF).toString(16).padStart(8, '0'),
      isEquivocator: true,
      isFinal: false,
      signatures: block.signatures,
    };
    sim.blocks.push(block, sibling);
    newBlocks.push(block, sibling);
    sim.log.push({ text: `Node ${creatorIdx} EQUIVOCATED at height ${block.height} (${block.hash} vs ${sibling.hash})`, kind: 'danger' });
  } else {
    sim.blocks.push(block);
    newBlocks.push(block);
  }

  // Finality check
  newBlocks.forEach(b => {
    if (b.signatures >= threshold) {
      b.isFinal = true;
      // Tau order: append if not already present
      if (!sim.tauOrder.includes(b.id)) {
        sim.tauOrder.push(b.id);
        sim.log.push({ text: `Block #${b.id} finalized by node ${b.creator} (h=${b.height})`, kind: 'success' });
      }
    }
  });

  creator.height++;
  creator.tip = block;

  // Propagate tips to other nodes
  sim.nodes.forEach((node, idx) => {
    if (idx !== creatorIdx && creator.tip) {
      // Simple gossip: nodes always see the latest non-equivocating tip
      if (!block.isEquivocator) {
        node.tip = block;
      }
    }
  });

  sim.ticks++;
  if (sim.blocks.length % Math.max(1, nodeCount) === 0) sim.wave++;

  if (!newBlocks.some(b => b.isEquivocator)) {
    const b = newBlocks[0];
    sim.log.push({ text: `Node ${b.creator} → block #${b.id} h=${b.height}${b.isFinal ? ' FINAL' : ''}`, kind: b.isFinal ? 'success' : 'info' });
  }

  return newBlocks;
}

// ── SVG rendering ─────────────────────────────────────────────────────────────

function renderDagSvg(sim, width = 520) {
  const { blocks, nodeCount, tauOrder } = sim;
  if (!blocks.length) return null;

  const maxHeight = Math.max(...blocks.map(b => b.height));
  const svgHeight = Math.max(180, (maxHeight + 2) * 48 + 40);
  const colWidth = nodeCount <= 1 ? width : (width - 120) / (nodeCount - 1);

  // positions indexed by block.id
  const pos = {};
  blocks.forEach(block => {
    const x = 60 + block.creator * colWidth;
    const y = svgHeight - 32 - block.height * 44;
    pos[block.id] = { x, y };
  });

  const tauSet = new Set(tauOrder);
  let svg = `<svg width="${width}" height="${svgHeight}" xmlns="http://www.w3.org/2000/svg" style="display:block;">`;

  // Tau highlight bands (behind everything)
  tauOrder.forEach(id => {
    const p = pos[id];
    if (p) {
      svg += `<circle cx="${p.x}" cy="${p.y}" r="17" fill="${TAU_HIGHLIGHT}" />`;
    }
  });

  // Edges
  blocks.forEach(block => {
    const to = pos[block.id];
    block.predecessors.forEach(predId => {
      const from = pos[predId];
      if (from && to) {
        svg += `<line x1="${from.x}" y1="${from.y}" x2="${to.x}" y2="${to.y}" `
          + `stroke="rgba(232,224,208,0.12)" stroke-width="1"/>`;
      }
    });
  });

  // Blocks
  blocks.forEach(block => {
    const p = pos[block.id];
    const color = block.isEquivocator ? EQUIVOCATOR_COLOR : NODE_COLORS[block.creator % NODE_COLORS.length];
    const r = block.isFinal ? 9 : 6;

    if (block.isFinal) {
      svg += `<circle cx="${p.x}" cy="${p.y}" r="${r + 5}" fill="none" stroke="${color}" stroke-width="1" opacity="0.3"/>`;
    }
    if (block.isEquivocator) {
      // Red diamond outline to highlight the equivocation
      const d = r + 3;
      svg += `<polygon points="${p.x},${p.y - d} ${p.x + d},${p.y} ${p.x},${p.y + d} ${p.x - d},${p.y}" `
        + `fill="none" stroke="${EQUIVOCATOR_COLOR}" stroke-width="1.5" opacity="0.7"/>`;
    }
    svg += `<circle cx="${p.x}" cy="${p.y}" r="${r}" fill="${color}" `
      + `opacity="${block.isFinal ? 1 : 0.6}" title="block #${block.id} h=${block.height}"/>`;
    // Tau order label
    if (tauSet.has(block.id)) {
      const rank = tauOrder.indexOf(block.id) + 1;
      svg += `<text x="${p.x}" y="${p.y + 3}" text-anchor="middle" `
        + `font-family="var(--font-mono,monospace)" font-size="7" fill="rgba(255,220,100,0.9)">${rank}</text>`;
    }
  });

  // Node column headers
  for (let i = 0; i < nodeCount; i++) {
    const x = 60 + i * colWidth;
    const color = NODE_COLORS[i % NODE_COLORS.length];
    const label = sim.equivocatorIndex != null && i === parseInt(sim.equivocatorIndex)
      ? `N${i} [BYZ]` : `N${i}`;
    svg += `<text x="${x}" y="14" text-anchor="middle" `
      + `font-family="var(--font-mono,monospace)" font-size="9" fill="${color}">${label}</text>`;
  }

  svg += `</svg>`;
  return svg;
}

function renderDagThumbnailSvg(sim) {
  return renderDagSvg(sim, 160);
}

// ── custom element ────────────────────────────────────────────────────────────

class PyanaBlocklaceSim extends HTMLElement {
  static get observedAttributes() {
    return ['node-count', 'block-rate', 'mode', 'equivocator-index'];
  }

  constructor() {
    super();
    this._sim = null;
    this._running = false;
    this._runHandle = null;
    this._styleInjected = false;
  }

  connectedCallback() {
    this._injectStyle();
    this._sim = this._makeSim();
    this._renderSelf();
  }

  attributeChangedCallback() {
    if (!this.isConnected) return;
    // Re-init sim when structural attributes change, preserve ticks if only
    // mode changed.
    const attrName = arguments[0];
    if (attrName === 'mode') {
      this._renderSelf();
    } else {
      this._stopLoop();
      this._sim = this._makeSim();
      this._renderSelf();
    }
  }

  disconnectedCallback() {
    this._stopLoop();
  }

  // ── public API ──────────────────────────────────────────────────────────────

  /** Advance simulation by n ticks. Returns array of all new blocks produced. */
  tick(n = 1) {
    if (!this._sim) this._sim = this._makeSim();
    const allNew = [];
    for (let i = 0; i < n; i++) {
      const produced = simTick(this._sim);
      allNew.push(...produced);
    }
    this._renderSelf();
    return allNew;
  }

  /** Reset simulation to empty state (keeps current attributes). */
  reset() {
    this._stopLoop();
    this._sim = this._makeSim();
    this._renderSelf();
  }

  /** Snapshot of current simulation state (non-reactive copy). */
  getState() {
    if (!this._sim) return { blocks: [], tauOrder: [], equivocations: 0, wave: 0, ticks: 0 };
    const { blocks, tauOrder, equivocations, wave, ticks } = this._sim;
    return { blocks: [...blocks], tauOrder: [...tauOrder], equivocations, wave, ticks };
  }

  // ── internal helpers ────────────────────────────────────────────────────────

  _makeSim() {
    const nodeCount = Math.max(2, Math.min(7, parseInt(this.getAttribute('node-count') || '4')));
    const eqIdx = this.getAttribute('equivocator-index');
    return createSim(nodeCount, eqIdx != null && eqIdx !== '' ? eqIdx : null);
  }

  _blockRate() {
    return Math.max(1, parseInt(this.getAttribute('block-rate') || '1'));
  }

  _mode() {
    return this.getAttribute('mode') || 'default';
  }

  _injectStyle() {
    if (this._styleInjected || document.getElementById('pyana-blocklace-sim-style')) {
      this._styleInjected = true;
      return;
    }
    const el = document.createElement('style');
    el.id = 'pyana-blocklace-sim-style';
    el.textContent = CSS;
    document.head.appendChild(el);
    this._styleInjected = true;
  }

  _startLoop() {
    if (this._running) return;
    this._running = true;
    const run = () => {
      if (!this._running) return;
      const rate = this._blockRate();
      for (let i = 0; i < rate; i++) simTick(this._sim);
      this._renderSelf();
      this._runHandle = setTimeout(run, 800);
    };
    run();
  }

  _stopLoop() {
    this._running = false;
    if (this._runHandle) { clearTimeout(this._runHandle); this._runHandle = null; }
  }

  _renderSelf() {
    const mode = this._mode();
    if (mode === 'compact') {
      this._renderCompact();
    } else {
      this._renderDefault();
    }
  }

  _renderCompact() {
    const sim = this._sim;
    const svgHtml = sim && sim.blocks.length ? renderDagThumbnailSvg(sim) : '';
    const tauLabel = sim && sim.tauOrder.length
      ? sim.tauOrder.slice(0, 6).map(id => {
          const b = sim.blocks[id];
          return b ? `N${b.creator}h${b.height}` : `#${id}`;
        }).join(' ') + (sim.tauOrder.length > 6 ? ' …' : '')
      : '(none)';
    const nc = sim ? sim.nodeCount : (parseInt(this.getAttribute('node-count') || '4'));
    const ticks = sim ? sim.ticks : 0;

    this.innerHTML = `<span class="pbs pbs__compact">
      <code>${nc} nodes · ${ticks} ticks · tau: ${tauLabel}</code>
      ${svgHtml ? `<span class="pbs__svg-thumb">${svgHtml}</span>` : ''}
    </span>`;
  }

  _renderDefault() {
    const sim = this._sim;
    const svgHtml = sim && sim.blocks.length ? renderDagSvg(sim) : null;
    const nc = sim ? sim.nodeCount : 4;

    // Tau order label
    const tauLabel = sim && sim.tauOrder.length
      ? sim.tauOrder.slice(0, 12).map(id => {
          const b = sim.blocks[id];
          return b ? `N${b.creator}·h${b.height}` : `#${id}`;
        }).join('  ') + (sim.tauOrder.length > 12 ? ' …' : '')
      : '(none yet)';

    // Build log HTML (last 12, newest-first)
    const logEntries = sim && sim.log.length
      ? sim.log.slice(-12).reverse()
          .map(e => `<div class="pbs__log-entry pbs__log-entry--${e.kind}">${e.text}</div>`)
          .join('')
      : '<div class="pbs__log-entry pbs__log-entry--info">No events yet.</div>';

    const isRunning = this._running;

    this.innerHTML = `<div class="pbs">
      <div class="pbs__controls">
        <button class="pbs__btn pbs__btn--accent" id="pbs-start"${isRunning ? ' disabled' : ''}>Start</button>
        <button class="pbs__btn" id="pbs-stop"${!isRunning ? ' disabled' : ''}>Stop</button>
        <button class="pbs__btn" id="pbs-step">Step</button>
        <button class="pbs__btn" id="pbs-reset">Reset</button>
        <label class="pbs__label">Nodes
          <input type="number" id="pbs-nc" value="${nc}" min="2" max="7" class="pbs__nc-input">
        </label>
        <label class="pbs__label">
          <input type="checkbox" id="pbs-equivocate"${sim && sim.equivocatorIndex != null ? ' checked' : ''}>
          Equivocator (N0)
        </label>
      </div>
      <div class="pbs__stats">
        <span>Blocks: <span class="pbs__stat-val" id="pbs-block-count">${sim ? sim.blocks.length : 0}</span></span>
        <span>Final: <span class="pbs__stat-val" id="pbs-final-count">${sim ? sim.tauOrder.length : 0}</span></span>
        <span>Wave: <span class="pbs__stat-val" id="pbs-wave">${sim ? sim.wave : 0}</span></span>
        <span>Equivocations: <span class="pbs__stat-val" id="pbs-equiv">${sim ? sim.equivocations : 0}</span></span>
        <span>Ticks: <span class="pbs__stat-val" id="pbs-ticks">${sim ? sim.ticks : 0}</span></span>
      </div>
      <div class="pbs__tau">
        Tau order: <code id="pbs-tau">${tauLabel}</code>
      </div>
      <div class="pbs__svg-wrap" id="pbs-dag">
        ${svgHtml || '<div class="pbs__empty">Press Step or Start to begin the simulation.</div>'}
      </div>
      <div class="pbs__log">
        <div class="pbs__log-hdr">Event log</div>
        <div id="pbs-log-body">${logEntries}</div>
      </div>
    </div>`;

    this._wireControls();
  }

  _wireControls() {
    const startBtn = this.querySelector('#pbs-start');
    const stopBtn = this.querySelector('#pbs-stop');
    const stepBtn = this.querySelector('#pbs-step');
    const resetBtn = this.querySelector('#pbs-reset');
    const ncInput = this.querySelector('#pbs-nc');
    const equivCheck = this.querySelector('#pbs-equivocate');

    startBtn?.addEventListener('click', () => {
      this._startLoop();
      this._renderSelf();
    });
    stopBtn?.addEventListener('click', () => {
      this._stopLoop();
      this._renderSelf();
    });
    stepBtn?.addEventListener('click', () => {
      const rate = this._blockRate();
      for (let i = 0; i < rate; i++) simTick(this._sim);
      this._renderSelf();
    });
    resetBtn?.addEventListener('click', () => {
      this.reset();
    });
    ncInput?.addEventListener('change', () => {
      this.setAttribute('node-count', ncInput.value);
      // attributeChangedCallback handles the re-init
    });
    equivCheck?.addEventListener('change', () => {
      if (equivCheck.checked) {
        this.setAttribute('equivocator-index', '0');
      } else {
        this.removeAttribute('equivocator-index');
      }
    });
  }
}

if (!customElements.get('pyana-blocklace-sim')) {
  customElements.define('pyana-blocklace-sim', PyanaBlocklaceSim);
}
