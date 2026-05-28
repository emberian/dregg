// Notes section — private value transfer, double-spend prevention.
//
// NO JS hashing. Every commitment and nullifier is produced by the canonical
// wasm note API (create_note / spend_note / get_notes) against the shared
// in-memory runtime — the same `dregg_cell::Note` the <dregg-note> inspector
// reads. Double-spend rejection is the real runtime refusing to spend a note
// whose nullifier was already revealed, not a JS-tracked set.

import { state, notifyStateChange, navigateTo } from '../playground.js';
import { ensureStudioRuntime, deepLinkBanner, inspectorEmbed, onSeedReady } from '../studio-embed.js';

// Asset names are UI labels over the runtime's numeric u64 asset_type tag.
// First-seen name gets the next stable id (deterministic within a session).
const ASSET_IDS = new Map([['token', 0]]);
function assetTypeFor(name) {
  const key = (name || 'token').trim() || 'token';
  if (!ASSET_IDS.has(key)) ASSET_IDS.set(key, ASSET_IDS.size);
  return ASSET_IDS.get(key);
}
function assetNameFor(id) {
  for (const [k, v] of ASSET_IDS) if (v === id) return k;
  return `asset#${id}`;
}

const SELF = 0;      // alice (seeded)
const RECIPIENT = 1; // bob (seeded)

export function initNotes(wasm) {
  const container = document.getElementById('section-notes');
  container.innerHTML = `
    <div class="section-header">
      <h2>Private Notes</h2>
      ${deepLinkBanner(
        [{ label: '<dregg-note>', uri: 'dregg://note/feed' }],
        'real commitment + nullifier UTXO lifecycle',
      )}
      <p>
        Notes are dregg's UTXO-style private value transfer primitive. When you mint a note,
        a cryptographic commitment hides the amount. When you spend it, a nullifier is published
        that prevents double-spending — but reveals nothing about the note's contents.
        Transfers create new notes and consume old ones atomically. Every value below is real
        wasm output (<code>dregg_cell::Note</code>) — no JavaScript hashing.
      </p>
      ${inspectorEmbed(
        `<dregg-note id="nt-inspector" uri="dregg://note/seed" agent-index="0"></dregg-note>`,
        'Canonical note view (real seeded note)',
      )}
      <span class="next-hint" data-next="capabilities">Next: capability delegation &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Asset Type</label>
        <input type="text" id="nt-asset" value="token" spellcheck="false" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Amount</label>
        <input type="number" id="nt-amount" value="100" min="1" style="width: 100px;">
      </div>
      <button class="btn btn-primary" id="nt-mint" disabled>Mint Note</button>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Transfer Amount</label>
        <input type="number" id="nt-transfer-amount" value="50" min="1" style="width: 100px;">
      </div>
      <button class="btn btn-primary" id="nt-transfer" disabled>Transfer to bob</button>
      <button class="btn btn-danger" id="nt-doublespend" disabled>Double-Spend Attempt</button>
    </div>

    <div id="nt-timeline"></div>
    <div id="nt-explainer"></div>
  `;

  onSeedReady((s) => {
    const el = container.querySelector('#nt-inspector');
    if (el && s.note) el.setAttribute('data', JSON.stringify(s.note));
    if (s.noteCommitment) {
      const uri = `dregg://note/${s.noteCommitment}`;
      el?.setAttribute('uri', uri);
      const link = container.querySelector('.pg-sb-link');
      if (link) link.href = `/starbridge/?at=${encodeURIComponent(uri)}`;
    }
  });

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('capabilities'));

  const mintBtn = container.querySelector('#nt-mint');
  const transferBtn = container.querySelector('#nt-transfer');
  const doubleBtn = container.querySelector('#nt-doublespend');
  const timelineDiv = container.querySelector('#nt-timeline');
  const explainerDiv = container.querySelector('#nt-explainer');

  let ctx = null;          // { runtime, wasm }
  let lastSpent = null;    // { value, asset_type, nullifier } — for double-spend demo

  // Read the real note index for both agents.
  function allNotes() {
    if (!ctx) return [];
    const out = [];
    for (const [idx, owner] of [[SELF, 'self'], [RECIPIENT, 'bob']]) {
      let notes = [];
      try { notes = ctx.wasm.get_notes(ctx.runtime._handle, idx) || []; } catch {}
      for (const n of notes) out.push({ ...n, owner, agent_index: idx });
    }
    return out;
  }

  function syncBadgeState(notes) {
    // Mirror into the shared state so the nav badge + state panel reflect reality.
    state.notes = notes.map(n => ({
      id: n.commitment.slice(0, 8), asset: assetNameFor(n.asset_type),
      amount: Number(n.value), commitment: n.commitment,
      nullifier: n.nullifier || null, owner: n.owner, spent: !!n.spent,
    }));
    state.nullifiers = notes.filter(n => n.nullifier).map(n => n.nullifier);
    notifyStateChange();
  }

  function renderTimeline() {
    const notes = allNotes();
    syncBadgeState(notes);
    transferBtn.disabled = !notes.some(n => n.owner === 'self' && !n.spent);
    doubleBtn.disabled = !lastSpent;

    if (!notes.length) {
      timelineDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Mint a note to begin the lifecycle. (alice may already hold a seeded note.)</div>
      </div></div>`;
      return;
    }
    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Note Timeline (real ledger index)</span></div><div class="result-panel__body">';
    notes.forEach((note) => {
      const statusCls = note.spent ? 'warning' : 'success';
      const status = note.spent ? 'SPENT' : 'UNSPENT';
      html += `<div class="note-timeline-item">
        <span class="note-tl-type ${note.spent ? 'rejected' : 'mint'}">${status}</span>
        <div class="note-tl-body">
          <strong>${note.value} ${escapeHtml(assetNameFor(note.asset_type))}</strong> (owner: ${escapeHtml(note.owner)})
          <br><span class="note-tl-hash">commitment: ${note.commitment.slice(0, 32)}...</span>
          ${note.nullifier ? `<br><span class="note-tl-hash">nullifier: ${note.nullifier.slice(0, 32)}...</span>` : ''}
        </div>
      </div>`;
    });
    html += '</div></div>';
    timelineDiv.innerHTML = html;

    // Refresh the embedded inspector with the freshest unspent self note.
    const fresh = notes.find(n => n.owner === 'self' && !n.spent) || notes[0];
    const el = container.querySelector('#nt-inspector');
    if (el && fresh) el.setAttribute('data', JSON.stringify({ commitment: fresh.commitment, value: Number(fresh.value), asset_type: Number(fresh.asset_type) }));
  }

  mintBtn.addEventListener('click', () => {
    if (!ctx) return;
    const asset = container.querySelector('#nt-asset').value.trim() || 'token';
    const amount = parseInt(container.querySelector('#nt-amount').value) || 100;
    const at = assetTypeFor(asset);
    const t0 = performance.now();
    let res;
    try {
      res = ctx.wasm.create_note(ctx.runtime._handle, SELF, BigInt(amount), BigInt(at));
    } catch (e) {
      showExplainerError(explainerDiv, `create_note failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);
    if (ctx.runtime.version) ctx.runtime.version.value++;
    state.proofCount = state.proofCount; // (no proof minted here)
    renderTimeline();
    showExplainer(explainerDiv, {
      prover: `Minted a note\nAsset: ${asset}, Amount: ${amount}\nCommitment: ${String(res.commitment).slice(0, 28)}...\nKnows: the opening (value, blinding) — its spend authority`,
      verifier: `Sees: a new commitment in the agent's note index\nDoes NOT see: amount or asset (hidden inside the commitment)\nCommitment is binding + hiding (canonical dregg_cell::Note)`,
      delta: `The commitment is produced by the real wasm note constructor. The verifier learns a note exists but nothing about its value. Only the owner can later reveal the nullifier to spend it.`,
      timing: elapsed,
    });
  });

  transferBtn.addEventListener('click', () => {
    if (!ctx) return;
    const transferAmount = parseInt(container.querySelector('#nt-transfer-amount').value) || 50;
    const notes = allNotes();
    const source = notes.find(n => n.owner === 'self' && !n.spent && Number(n.value) >= transferAmount);
    if (!source) {
      showExplainerError(explainerDiv, `No unspent note of yours holds at least ${transferAmount}. Mint one first.`);
      return;
    }
    const at = Number(source.asset_type);
    const sourceValue = Number(source.value);
    const change = sourceValue - transferAmount;
    const t0 = performance.now();
    let nullifierRes;
    try {
      // Spend the whole source note: reveal its real nullifier.
      nullifierRes = ctx.wasm.spend_note(ctx.runtime._handle, SELF, BigInt(sourceValue), BigInt(at));
      // Mint recipient + change notes (real commitments). Conservation holds:
      // recipient + change == source value.
      ctx.wasm.create_note(ctx.runtime._handle, RECIPIENT, BigInt(transferAmount), BigInt(at));
      if (change > 0) ctx.wasm.create_note(ctx.runtime._handle, SELF, BigInt(change), BigInt(at));
    } catch (e) {
      showExplainerError(explainerDiv, `transfer failed: ${e && e.message || e}`);
      return;
    }
    lastSpent = { value: sourceValue, asset_type: at, nullifier: nullifierRes.nullifier };
    const elapsed = (performance.now() - t0).toFixed(2);
    if (ctx.runtime.version) ctx.runtime.version.value++;
    renderTimeline();
    showExplainer(explainerDiv, {
      prover: `Spent a note worth ${sourceValue} ${assetNameFor(at)}\nRevealed nullifier: ${String(nullifierRes.nullifier).slice(0, 24)}...\nCreated: ${transferAmount} to bob${change > 0 ? `, ${change} change to self` : ''}`,
      verifier: `Sees: nullifier published (this note can never be spent again)\nSees: ${change > 0 ? '2 new commitments' : '1 new commitment'}\nDoes NOT see: amounts, or linkage between consumed + created notes`,
      delta: `The nullifier is the real value from spend_note. Conservation (in = out) holds: ${transferAmount} + ${change} = ${sourceValue}. The transfer is unlinkable.`,
      timing: elapsed,
    });
  });

  doubleBtn.addEventListener('click', () => {
    if (!ctx || !lastSpent) return;
    const t0 = performance.now();
    let rejected = false, errMsg = '';
    try {
      // Attempt to spend the same note again. The runtime has no unspent note
      // matching (value, asset) anymore — its nullifier was already revealed.
      ctx.wasm.spend_note(ctx.runtime._handle, SELF, BigInt(lastSpent.value), BigInt(lastSpent.asset_type));
    } catch (e) {
      rejected = true; errMsg = String(e && e.message || e);
    }
    const elapsed = (performance.now() - t0).toFixed(2);
    renderTimeline();
    if (rejected) {
      const html = timelineDiv.innerHTML;
      timelineDiv.innerHTML = `<div class="result-panel" style="margin-bottom: 12px;"><div class="result-panel__body">
        <div class="output-entry error">DOUBLE-SPEND REJECTED by the runtime: ${escapeHtml(errMsg)}</div>
      </div></div>` + html;
      showExplainer(explainerDiv, {
        prover: `Attempted to re-spend the note worth ${lastSpent.value} ${assetNameFor(lastSpent.asset_type)}\nNullifier already revealed: ${String(lastSpent.nullifier).slice(0, 24)}...`,
        verifier: `The runtime found no unspent note matching that opening.\nResult: REJECTED — "${escapeHtml(errMsg).slice(0, 80)}"\nDouble-spend prevention is enforced by the canonical note index, not a JS set.`,
        delta: `Once a nullifier is revealed the note is consumed forever. This rejection comes straight from the wasm runtime refusing the second spend.`,
        timing: elapsed,
      });
    } else {
      // Should not happen — surface honestly rather than claiming success.
      showExplainerError(explainerDiv, 'Unexpected: the runtime accepted a second spend. This would be a soundness bug — please report.');
    }
  });

  // Boot the shared runtime, then enable controls + render the real index.
  ensureStudioRuntime()
    .then(({ runtime, wasm: w }) => { ctx = { runtime, wasm: w || wasm }; mintBtn.disabled = false; renderTimeline(); })
    .catch((e) => {
      timelineDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry error">runtime unavailable: ${escapeHtml(String(e && e.message || e))}</div>
      </div></div>`;
    });
}

function showExplainerError(el, message) {
  el.innerHTML = `<div class="result-panel"><div class="result-panel__body">
    <div class="output-entry error">${escapeHtml(message)}</div>
  </div></div>`;
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Sender knows</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Ledger sees</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Privacy delta</div>
          <div class="explainer__cell-content">${escapeHtml(delta)}</div>
        </div>
      </div>
      <div class="explainer__timing">Operation completed in <span>${timing}ms</span></div>
    </div>
  `;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
