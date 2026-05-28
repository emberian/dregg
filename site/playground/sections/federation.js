// Federation & Sovereign Exchange section.
//
// NO JS simulation. Every value here comes from the canonical wasm runtime:
// - real BFT committees (create_federation → real threshold n−⌊n/3⌋),
// - real hash-chained finalized blocks (propose_block / list_federation_blocks),
// - real sovereign exit (make_cell_sovereign → real state commitment),
// - real peer exchange (peer_exchange_with_proof → real exchange id + proof
//   commitment) between two seeded cells.
//
// The old version animated a JS-tracked consensus with fabricated roots; that
// is gone. For the live multi-proposer blocklace, see the Explorer.

import { state, notifyStateChange, navigateTo } from '../playground.js';
import { ensureStudioRuntime, deepLinkBanner, onSeedReady } from '../studio-embed.js';

export function initFederation() {
  const container = document.getElementById('section-federation');
  container.innerHTML = `
    <div class="section-header">
      <h2>Federation &amp; Sovereign Exchange</h2>
      ${deepLinkBanner([
        { label: '<dregg-federation>', uri: 'dregg://federation/0' },
        { label: '<dregg-block-dag>', uri: 'dregg://block-dag/0' },
      ], 'real committees, real hash-chained blocks')}
      <p>
        Two real federations run side by side. Propose blocks and watch them finalize with a real
        quorum certificate (threshold = n − ⌊n/3⌋) and real BLAKE3 prev_hash chaining. Then exit a
        cell to sovereign mode and exchange value peer-to-peer with a real proof commitment — the
        protocol's actual answer to portable, off-chain cooperation. Every hash below is real wasm
        output.
      </p>
      <span class="next-hint" data-next="marketplace">Next: compute marketplace &rarr;</span>
    </div>

    <div class="fed-sim-container">
      <div class="fed-sim-group" id="fed-group-a">
        <div class="fed-sim-group__header">
          <span class="fed-sim-group__title">Federation Alpha</span>
          <span class="fed-sim-group__height" id="fed-a-height">height: 0</span>
        </div>
        <div class="fed-sim-state__body" id="fed-a-info">creating…</div>
        <div class="controls-row" style="margin-top:8px;">
          <button class="btn btn-primary" id="fed-a-propose" disabled>Propose block in Alpha</button>
        </div>
        <div id="fed-a-blocks" class="fed-sim-consensus"></div>
      </div>

      <div class="fed-sim-group" id="fed-group-b">
        <div class="fed-sim-group__header">
          <span class="fed-sim-group__title">Federation Beta</span>
          <span class="fed-sim-group__height" id="fed-b-height">height: 0</span>
        </div>
        <div class="fed-sim-state__body" id="fed-b-info">creating…</div>
        <div class="controls-row" style="margin-top:8px;">
          <button class="btn btn-primary" id="fed-b-propose" disabled>Propose block in Beta</button>
        </div>
        <div id="fed-b-blocks" class="fed-sim-consensus"></div>
      </div>
    </div>

    <div class="controls-row" style="margin-top:16px;">
      <button class="btn btn-secondary" id="fed-sovereign" disabled>Exit alice → sovereign</button>
      <button class="btn btn-primary" id="fed-exchange" disabled>Peer exchange alice → bob</button>
      <button class="btn btn-secondary" id="fed-reset">Reset</button>
    </div>

    <div id="fed-timeline"></div>
    <div id="fed-explainer"></div>
  `;

  onSeedReady((s) => {
    const links = container.querySelectorAll('.pg-sb-link');
    if (links[0] && s.fedIndex != null) links[0].href = `/starbridge/?at=${encodeURIComponent('dregg://federation/' + s.fedIndex)}`;
    if (links[1] && s.fedIndex != null) links[1].href = `/starbridge/?at=${encodeURIComponent('dregg://block-dag/' + s.fedIndex)}`;
  });

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('marketplace'));

  const timelineDiv = container.querySelector('#fed-timeline');
  const explainerDiv = container.querySelector('#fed-explainer');

  let ctx = null;          // { runtime, wasm }
  let alpha = null, beta = null;  // { fed_index, num_nodes, threshold, max_faults }
  let aliceCell = null, bobCell = null;
  let sovereign = null;    // last make_cell_sovereign result
  const log = [];

  function addLog(text, cls = 'info') {
    log.unshift({ text, cls });
    timelineDiv.innerHTML = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Federation Timeline (real wasm)</span></div><div class="result-panel__body">'
      + log.slice(0, 14).map(e => `<div class="output-entry ${e.cls}">${escapeHtml(e.text)}</div>`).join('')
      + '</div></div>';
  }

  function renderFed(fed, infoId, heightId, blocksId) {
    if (!fed) return;
    document.getElementById(infoId).innerHTML =
      `committee: <strong>${fed.num_nodes}</strong> nodes · quorum <strong>${fed.threshold}/${fed.num_nodes}</strong> · tolerates <strong>${fed.max_faults}</strong> fault(s)`;
    let blocks = [];
    try { blocks = ctx.wasm.list_federation_blocks(ctx.runtime._handle, fed.fed_index) || []; } catch {}
    document.getElementById(heightId).textContent = `height: ${blocks.length ? blocks[blocks.length - 1].height : 0}`;
    document.getElementById(blocksId).innerHTML = blocks.slice(-6).reverse().map(b =>
      `<div class="output-entry" style="font-family:var(--mono);font-size:11px;">#${b.height} <code>${short(b.block_hash)}</code> ← <code>${short(b.prev_hash)}</code></div>`
    ).join('') || '<div class="output-entry info">no blocks yet — propose one</div>';
  }

  function renderAll() {
    renderFed(alpha, 'fed-a-info', 'fed-a-height', 'fed-a-blocks');
    renderFed(beta, 'fed-b-info', 'fed-b-height', 'fed-b-blocks');
    state.federation.status = alpha ? 'consensus' : 'loading';
    state.federation.nodes = (alpha?.num_nodes || 0) + (beta?.num_nodes || 0);
    notifyStateChange();
  }

  async function proposeIn(fed, label) {
    if (!ctx || !fed) return;
    const tokenId = randomHex(32);
    try {
      const res = await ctx.runtime.proposeBlock(fed.fed_index, [tokenId]);
      if (!res || res.finalized === false) { addLog(`${label}: round did not finalize`, 'warning'); return; }
      if (ctx.runtime.version) ctx.runtime.version.value++;
      addLog(`${label}: finalized block #${res.height} (hash ${short(res.block_hash)})`, 'success');
      renderAll();
    } catch (e) { addLog(`${label}: propose_block failed — ${e && e.message || e}`, 'error'); }
  }

  container.querySelector('#fed-a-propose').addEventListener('click', () => proposeIn(alpha, 'Alpha'));
  container.querySelector('#fed-b-propose').addEventListener('click', () => proposeIn(beta, 'Beta'));

  container.querySelector('#fed-sovereign').addEventListener('click', () => {
    if (!ctx || !aliceCell) return;
    try {
      sovereign = ctx.wasm.make_cell_sovereign(aliceCell, BigInt(5000));
      addLog(`alice exited to sovereign mode — state commitment ${short(sovereign.state_commitment)}`, 'success');
      container.querySelector('#fed-exchange').disabled = false;
      showExplainer(explainerDiv, {
        left: `alice's cell ${short(aliceCell)} opted out of federation consensus.\nState commitment: ${sovereign.state_commitment.slice(0, 24)}...`,
        center: `make_cell_sovereign computed a real BLAKE3 commitment over (cell_id, balance).\nThe cell can now exchange peer-to-peer without a federation round.`,
        right: `Sovereignty is the protocol's exit: a cell carries a self-proving state commitment and cooperates off-chain via peer exchange + proofs.`,
      });
    } catch (e) { addLog(`make_cell_sovereign failed — ${e && e.message || e}`, 'error'); }
  });

  container.querySelector('#fed-exchange').addEventListener('click', () => {
    if (!ctx || !aliceCell || !bobCell) return;
    try {
      const ex = ctx.wasm.peer_exchange_with_proof(aliceCell, bobCell, BigInt(100));
      state.proofCount++; notifyStateChange();
      addLog(`peer exchange alice → bob (100): exchange ${short(ex.exchange_id)}, proof ${short(ex.proof_commitment)}`, 'success');
      showExplainer(explainerDiv, {
        left: `alice ${short(ex.sender_cell)} → bob ${short(ex.receiver_cell)}\nAmount: ${ex.amount}\nExchange id: ${ex.exchange_id.slice(0, 24)}...`,
        center: `peer_exchange_with_proof produced a real proof commitment binding the exchange id + amount: ${ex.proof_commitment.slice(0, 24)}...`,
        right: `Two sovereign cells cooperate directly — no federation round, no shared ledger. The proof commitment is what each party verifies. This is dregg's off-chain composition primitive.`,
      });
    } catch (e) { addLog(`peer_exchange_with_proof failed — ${e && e.message || e}`, 'error'); }
  });

  container.querySelector('#fed-reset').addEventListener('click', () => { log.length = 0; timelineDiv.innerHTML = ''; explainerDiv.innerHTML = ''; boot(true); });

  async function boot(reset) {
    if (!ctx) return;
    try {
      alpha = await ctx.runtime.createFederation(`alpha-${salt()}`, 4);
      alpha = { fed_index: Number(alpha.fed_index), num_nodes: Number(alpha.num_nodes), threshold: Number(alpha.threshold), max_faults: Number(alpha.max_faults) };
      beta = await ctx.runtime.createFederation(`beta-${salt()}`, 3);
      beta = { fed_index: Number(beta.fed_index), num_nodes: Number(beta.num_nodes), threshold: Number(beta.threshold), max_faults: Number(beta.max_faults) };
      container.querySelector('#fed-a-propose').disabled = false;
      container.querySelector('#fed-b-propose').disabled = false;
      container.querySelector('#fed-sovereign').disabled = !aliceCell;
      if (!reset) addLog(`created Alpha (4 nodes, quorum ${alpha.threshold}) + Beta (3 nodes, quorum ${beta.threshold})`, 'info');
      renderAll();
    } catch (e) { addLog(`create_federation failed — ${e && e.message || e}`, 'error'); }
  }

  ensureStudioRuntime()
    .then(({ runtime, wasm, seed }) => {
      ctx = { runtime, wasm };
      aliceCell = seed.aliceCell || null;
      bobCell = seed.bobCell || null;
      return boot(false);
    })
    .catch((e) => { addLog(`runtime unavailable — ${e && e.message || e}`, 'error'); });
}

function short(h) { if (!h) return '0x000…000'; const s = String(h); return `0x${s.slice(0, 6)}…${s.slice(-4)}`; }
function randomHex(n) { const b = new Uint8Array(n); crypto.getRandomValues(b); return Array.from(b).map(x => x.toString(16).padStart(2, '0')).join(''); }
let _salt = 0; function salt() { _salt += 1; return _salt; }

function showExplainer(el, { left, center, right }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover"><div class="explainer__cell-label">Actor</div><div class="explainer__cell-content">${escapeHtml(left)}</div></div>
        <div class="explainer__cell explainer__cell--verifier"><div class="explainer__cell-label">Protocol</div><div class="explainer__cell-content">${escapeHtml(center)}</div></div>
        <div class="explainer__cell explainer__cell--delta"><div class="explainer__cell-label">Why this matters</div><div class="explainer__cell-content">${escapeHtml(right)}</div></div>
      </div>
    </div>`;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
