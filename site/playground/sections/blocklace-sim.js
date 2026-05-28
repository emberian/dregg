/**
 * Federation Consensus Section.
 *
 * NO in-browser simulation. This drives the canonical wasm runtime's real
 * `dregg_federation` consensus: a real BFT committee (threshold n − ⌊n/3⌋),
 * real BLAKE3 block hash-chaining (each block folds in its predecessor's
 * hash), real quorum certificates, and the ledger's real Merkle root captured
 * at block time. Every value rendered here comes back from the wasm runtime —
 * `create_federation` / `propose_block` / `list_federation_blocks` /
 * `get_federation_block` — exactly the surface the Explorer and Starbridge
 * <dregg-block-dag> inspector read.
 *
 * The full Cordial-Miners blocklace DAG (multi-proposer, equivocation
 * detection) runs in the `dregg-node`; explore it live in the Explorer.
 */

import { ensureStudioRuntime, deepLinkBanner } from '../studio-embed.js';

const NODE_COLORS = ['#6ba3c7', '#d99a3f', '#9bb87a', '#c77ab8', '#7ac7b8', '#b89b6b', '#9a7ac7'];

let ctx = null;          // { runtime, wasm }
let fed = null;          // { fed_index, num_nodes, threshold, max_faults, name }
let autoTimer = null;

export function initBlocklaceSim() {
  const section = document.getElementById('section-blocklace-sim');
  if (!section) return;

  section.innerHTML = `
    <div class="pg-section__header">
      <h2>Federation Consensus</h2>
      ${deepLinkBanner(
        [{ label: '<dregg-block-dag>', uri: 'dregg://block-dag/0' }],
        'real finalized blocks with cryptographic prev_hash linkage',
      )}
      <p>
        Drive the wasm runtime's real <code>dregg_federation</code> committee. Propose blocks and
        watch them finalize with a real quorum certificate (threshold = n − ⌊n/3⌋) and real
        BLAKE3 hash-chaining. Every block, hash, and root below comes straight from the wasm —
        no JavaScript simulation. The full multi-proposer Cordial-Miners blocklace runs in the
        node; explore it live in the <a href="/explorer/" style="color:var(--accent-bright);">Explorer</a>.
      </p>
    </div>

    <div class="bsim-controls">
      <div class="bsim-controls__row">
        <label class="bsim-label">
          Committee size
          <input type="number" id="bsim-node-count" value="4" min="2" max="7" class="bsim-input bsim-input--small">
        </label>
        <label class="bsim-label">
          Auto rate (ms)
          <input type="number" id="bsim-rate" value="900" min="200" max="5000" step="100" class="bsim-input bsim-input--small">
        </label>
      </div>
      <div class="bsim-controls__actions">
        <button class="pg-btn pg-btn--accent" id="bsim-propose">Propose Block</button>
        <button class="pg-btn pg-btn--ghost" id="bsim-auto">Auto</button>
        <button class="pg-btn pg-btn--ghost" id="bsim-stop" disabled>Stop</button>
        <button class="pg-btn pg-btn--ghost" id="bsim-reset">Reset committee</button>
      </div>
    </div>

    <div class="bsim-stats" id="bsim-stats">
      <div class="bsim-stat"><span class="bsim-stat__label">Blocks</span><span class="bsim-stat__value" id="bsim-block-count">0</span></div>
      <div class="bsim-stat"><span class="bsim-stat__label">Height</span><span class="bsim-stat__value" id="bsim-height">0</span></div>
      <div class="bsim-stat"><span class="bsim-stat__label">Quorum</span><span class="bsim-stat__value" id="bsim-quorum">--</span></div>
      <div class="bsim-stat"><span class="bsim-stat__label">Faults tol.</span><span class="bsim-stat__value" id="bsim-faults">--</span></div>
    </div>

    <div class="bsim-dag" id="bsim-dag">
      <div class="pg-empty">Booting the wasm runtime…</div>
    </div>

    <div class="bsim-log" id="bsim-log">
      <div class="bsim-log__header">Finalized blocks (real <code>block_hash</code> ← <code>prev_hash</code>)</div>
      <div class="bsim-log__body" id="bsim-log-body"></div>
    </div>
  `;

  document.getElementById('bsim-propose').addEventListener('click', proposeBlock);
  document.getElementById('bsim-auto').addEventListener('click', startAuto);
  document.getElementById('bsim-stop').addEventListener('click', stopAuto);
  document.getElementById('bsim-reset').addEventListener('click', () => { stopAuto(); resetCommittee(); });

  // Boot the shared runtime and create the committee.
  ensureStudioRuntime()
    .then(({ runtime, wasm }) => { ctx = { runtime, wasm }; return resetCommittee(); })
    .catch((e) => {
      const dag = document.getElementById('bsim-dag');
      if (dag) dag.innerHTML = `<div class="pg-empty" style="color:var(--danger);">runtime unavailable: ${escapeHtml(String(e && e.message || e))}</div>`;
    });
}

async function resetCommittee() {
  if (!ctx) return;
  const n = clampInt(document.getElementById('bsim-node-count')?.value, 2, 7, 4);
  try {
    // A real committee: create_federation builds a canonical Federation from a
    // deterministic Ed25519 committee with BFT threshold n − ⌊n/3⌋.
    const result = await ctx.runtime.createFederation(`consensus-demo-${n}-${heightSalt()}`, n);
    fed = {
      fed_index: Number(result?.fed_index ?? 0),
      num_nodes: Number(result?.num_nodes ?? n),
      threshold: Number(result?.threshold ?? 0),
      max_faults: Number(result?.max_faults ?? 0),
    };
    document.getElementById('bsim-quorum').textContent = `${fed.threshold}/${fed.num_nodes}`;
    document.getElementById('bsim-faults').textContent = String(fed.max_faults);
    render();
  } catch (e) {
    const dag = document.getElementById('bsim-dag');
    if (dag) dag.innerHTML = `<div class="pg-empty" style="color:var(--danger);">create_federation failed: ${escapeHtml(String(e && e.message || e))}</div>`;
  }
}

async function proposeBlock() {
  if (!ctx || !fed) return;
  // The revocation target is a real input to the canonical consensus round.
  // (A random 32-byte token id — a genuine input, not fabricated output.)
  const tokenId = randomHex(32);
  try {
    const result = await ctx.runtime.proposeBlock(fed.fed_index, [tokenId]);
    if (!result || result.finalized === false) {
      addLogRaw(`<span style="color:var(--danger);">round did not finalize (quorum ${fed.threshold}/${fed.num_nodes} not reached)</span>`);
      return;
    }
    render();
  } catch (e) {
    addLogRaw(`<span style="color:var(--danger);">propose_block failed: ${escapeHtml(String(e && e.message || e))}</span>`);
  }
}

function startAuto() {
  if (autoTimer || !fed) return;
  document.getElementById('bsim-auto').disabled = true;
  document.getElementById('bsim-stop').disabled = false;
  const rate = clampInt(document.getElementById('bsim-rate')?.value, 200, 5000, 900);
  const tick = async () => { await proposeBlock(); if (autoTimer) autoTimer = setTimeout(tick, rate); };
  autoTimer = setTimeout(tick, 0);
}

function stopAuto() {
  if (autoTimer) { clearTimeout(autoTimer); autoTimer = null; }
  const a = document.getElementById('bsim-auto'); if (a) a.disabled = false;
  const s = document.getElementById('bsim-stop'); if (s) s.disabled = true;
}

/** Read the real finalized chain from wasm and render it. */
function render() {
  if (!ctx || !fed) return;
  let blocks = [];
  try {
    blocks = ctx.wasm.list_federation_blocks(ctx.runtime._handle, fed.fed_index) || [];
  } catch (e) {
    const dag = document.getElementById('bsim-dag');
    if (dag) dag.innerHTML = `<div class="pg-empty" style="color:var(--danger);">list_federation_blocks failed: ${escapeHtml(String(e && e.message || e))}</div>`;
    return;
  }

  document.getElementById('bsim-block-count').textContent = String(blocks.length);
  document.getElementById('bsim-height').textContent = String(blocks.length ? blocks[blocks.length - 1].height : 0);

  renderDag(blocks);
  renderLog(blocks);
}

function renderDag(blocks) {
  const container = document.getElementById('bsim-dag');
  if (!container) return;
  if (!blocks.length) {
    container.innerHTML = '<div class="pg-empty">Propose a block to finalize the genesis-most block (links to all-zeros).</div>';
    return;
  }
  const width = container.clientWidth || 640;
  const rowH = 46;
  const svgHeight = Math.max(120, blocks.length * rowH + 40);
  const cx = Math.min(width / 2, 320);

  let svg = `<svg width="${width}" height="${svgHeight}" xmlns="http://www.w3.org/2000/svg">`;
  const pos = (i) => ({ x: cx, y: 24 + i * rowH });

  // prev_hash edges (real cryptographic linkage)
  for (let i = 1; i < blocks.length; i++) {
    const a = pos(i - 1), b = pos(i);
    svg += `<line x1="${a.x}" y1="${a.y + 10}" x2="${b.x}" y2="${b.y - 10}" stroke="rgba(232,224,208,0.25)" stroke-width="1.5"/>`;
  }
  // Genesis link to all-zeros
  const g = pos(0);
  svg += `<text x="${cx + 26}" y="${g.y - 14}" font-family="'JetBrains Mono',monospace" font-size="8" fill="rgba(232,224,208,0.4)">prev = 0x000…000 (genesis)</text>`;

  blocks.forEach((b, i) => {
    const p = pos(i);
    const color = NODE_COLORS[(Number(b.height) - 1) % NODE_COLORS.length] || NODE_COLORS[0];
    svg += `<circle cx="${p.x}" cy="${p.y}" r="11" fill="none" stroke="${color}" stroke-width="1" opacity="0.4"/>`;
    svg += `<circle cx="${p.x}" cy="${p.y}" r="7" fill="${color}"/>`;
    svg += `<text x="${p.x - 22}" y="${p.y + 3}" text-anchor="end" font-family="'JetBrains Mono',monospace" font-size="9" fill="var(--text-dim)">h=${b.height}</text>`;
    svg += `<text x="${p.x + 22}" y="${p.y + 3}" font-family="'JetBrains Mono',monospace" font-size="9" fill="var(--text-dim)">${shortHash(b.block_hash)}</text>`;
  });

  svg += `</svg>`;
  container.innerHTML = svg;
}

function renderLog(blocks) {
  const body = document.getElementById('bsim-log-body');
  if (!body) return;
  if (!blocks.length) { body.innerHTML = ''; return; }
  // Newest first; pull full detail (votes/threshold/state root) for each.
  const rows = blocks.slice(-12).reverse().map((b) => {
    let detail = null;
    try { detail = ctx.wasm.get_federation_block(ctx.runtime._handle, fed.fed_index, BigInt(b.height)); } catch {}
    const votes = detail ? `${detail.num_votes}/${detail.qc_threshold} QC` : `${b.num_events} ev`;
    const root = detail ? shortHash(detail.post_state_root) : '';
    return `<div class="bsim-log__entry" style="color:var(--text-dim);">
      <span style="color:var(--accent-bright);">#${b.height}</span>
      block <code>${shortHash(b.block_hash)}</code> ← <code>${shortHash(b.prev_hash)}</code>
      <span style="color:var(--lantern);">${votes}</span>${root ? ` · state ${root}` : ''}
    </div>`;
  });
  body.innerHTML = rows.join('');
}

function addLogRaw(html) {
  const body = document.getElementById('bsim-log-body');
  if (!body) return;
  const div = document.createElement('div');
  div.className = 'bsim-log__entry';
  div.innerHTML = html;
  body.insertBefore(div, body.firstChild);
}

// --- helpers ----------------------------------------------------------------
function randomHex(n) {
  const bytes = new Uint8Array(n);
  crypto.getRandomValues(bytes);
  return Array.from(bytes).map((b) => b.toString(16).padStart(2, '0')).join('');
}
function shortHash(h) {
  if (!h) return '0x000…000';
  const s = String(h);
  return `0x${s.slice(0, 6)}…${s.slice(-4)}`;
}
function clampInt(v, lo, hi, dflt) {
  const n = parseInt(v, 10);
  if (Number.isNaN(n)) return dflt;
  return Math.max(lo, Math.min(hi, n));
}
let _salt = 0;
function heightSalt() { _salt += 1; return _salt; }
function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
