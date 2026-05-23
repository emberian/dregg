// Cross-Federation section — note bridge, conditional turns (conceptual/animated)

import { state, notifyStateChange, navigateTo } from '../playground.js';

export function initCrossfed(wasm) {
  const container = document.getElementById('section-crossfed');
  container.innerHTML = `
    <div class="section-header">
      <h2>Cross-Federation</h2>
      <p>
        Pyana federations are independent authorization domains. Cross-federation operations
        bridge notes, tokens, and capabilities across boundaries using conditional turns and
        intent matching. This is how pyana composes — multiple organizations can cooperate
        without sharing their internal state.
      </p>
      <span class="next-hint" data-next="sovereign">Next: sovereign cells &#8594;</span>
    </div>

    <div class="crossfed-diagram" id="cf-diagram">
      <div class="crossfed-nodes">
        <div class="crossfed-node" id="cf-node-a">
          <strong>Federation A</strong>
          <br><span style="font-size:10px;color:var(--text-muted);">Origin domain</span>
          <br><span style="font-size:10px;" id="cf-a-state">Idle</span>
        </div>
        <div class="crossfed-arrow" id="cf-arrow-1">&#8594;</div>
        <div class="crossfed-node" id="cf-node-bridge">
          <strong>Bridge</strong>
          <br><span style="font-size:10px;color:var(--text-muted);">Intent pool</span>
          <br><span style="font-size:10px;" id="cf-bridge-state">Waiting</span>
        </div>
        <div class="crossfed-arrow" id="cf-arrow-2">&#8594;</div>
        <div class="crossfed-node" id="cf-node-b">
          <strong>Federation B</strong>
          <br><span style="font-size:10px;color:var(--text-muted);">Destination domain</span>
          <br><span style="font-size:10px;" id="cf-b-state">Idle</span>
        </div>
      </div>
      <div class="crossfed-status" id="cf-status">
        Click "Initiate Bridge" to simulate a cross-federation note transfer
      </div>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Note Amount</label>
        <input type="number" id="cf-amount" value="50" min="1" style="width: 100px;">
      </div>
      <div class="control-group">
        <label>Destination</label>
        <input type="text" id="cf-dest" value="fed-b.example" spellcheck="false" style="width: 160px;">
      </div>
      <button class="btn btn-primary" id="cf-initiate" ${wasm ? '' : 'disabled'}>Initiate Bridge</button>
      <button class="btn btn-secondary" id="cf-reset">Reset</button>
    </div>

    <div id="cf-timeline"></div>
    <div id="cf-explainer"></div>
  `;

  if (!wasm) return;

  const timelineDiv = container.querySelector('#cf-timeline');
  const explainerDiv = container.querySelector('#cf-explainer');
  let animating = false;

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('sovereign'));

  container.querySelector('#cf-reset').addEventListener('click', () => {
    resetDiagram();
    timelineDiv.innerHTML = '';
    explainerDiv.innerHTML = '';
  });

  function resetDiagram() {
    container.querySelectorAll('.crossfed-node').forEach(n => n.classList.remove('active'));
    container.querySelectorAll('.crossfed-arrow').forEach(a => a.classList.remove('active'));
    container.querySelector('#cf-a-state').textContent = 'Idle';
    container.querySelector('#cf-bridge-state').textContent = 'Waiting';
    container.querySelector('#cf-b-state').textContent = 'Idle';
    container.querySelector('#cf-status').textContent = 'Click "Initiate Bridge" to simulate a cross-federation note transfer';
    animating = false;
  }

  container.querySelector('#cf-initiate').addEventListener('click', async () => {
    if (animating) return;
    animating = true;

    const amount = parseInt(container.querySelector('#cf-amount').value) || 50;
    const dest = container.querySelector('#cf-dest').value.trim() || 'fed-b.example';
    const steps = [];

    // Step 1: Lock note on source federation
    setNodeActive('cf-node-a');
    setStatus('Step 1/5: Locking note on Federation A...');
    container.querySelector('#cf-a-state').textContent = 'Locking...';
    await delay(600);

    const lockData = `bridge:${amount}:${Date.now()}`;
    let intentId;
    try {
      intentId = wasm.compute_intent_id ? wasm.compute_intent_id(lockData) : localHash(lockData);
    } catch {
      intentId = localHash(lockData);
    }

    container.querySelector('#cf-a-state').textContent = 'Note locked';
    steps.push(`[A] Locked ${amount} tokens, intent: ${intentId.slice(0, 16)}...`);

    // Step 2: Submit intent to bridge
    await delay(400);
    setArrowActive('cf-arrow-1');
    setNodeActive('cf-node-bridge');
    setStatus('Step 2/5: Intent submitted to bridge pool...');
    container.querySelector('#cf-bridge-state').textContent = 'Processing';
    await delay(500);

    steps.push(`[Bridge] Intent ${intentId.slice(0, 16)}... received and matched`);
    container.querySelector('#cf-bridge-state').textContent = 'Matched';

    // Step 3: Conditional turn
    await delay(400);
    setStatus('Step 3/5: Conditional turn — verifying proof of lock...');
    await delay(600);

    steps.push('[Bridge] STARK proof of lock verified (conditional turn accepted)');

    // Step 4: Mint on destination
    await delay(400);
    setArrowActive('cf-arrow-2');
    setNodeActive('cf-node-b');
    setStatus('Step 4/5: Minting equivalent note on Federation B...');
    container.querySelector('#cf-b-state').textContent = 'Minting...';
    await delay(500);

    let destCommitment;
    try {
      const result = wasm.compute_merkle_root(JSON.stringify([`bridge-dest:${amount}:${dest}:${Date.now()}`]));
      destCommitment = result.root_hex;
    } catch {
      destCommitment = localHash(`dest:${amount}:${dest}`);
    }

    container.querySelector('#cf-b-state').textContent = 'Note minted';
    steps.push(`[B] Minted ${amount} tokens at ${dest}, commitment: ${destCommitment.slice(0, 16)}...`);

    // Step 5: Finalize
    await delay(400);
    setStatus('Step 5/5: Bridge complete. Both sides finalized.');
    container.querySelector('#cf-bridge-state').textContent = 'Finalized';
    steps.push('[Complete] Cross-federation transfer finalized atomically');

    // Render timeline
    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Bridge Timeline</span></div><div class="result-panel__body">';
    steps.forEach((step, i) => {
      const cls = i === steps.length - 1 ? 'success' : 'info';
      html += `<div class="output-entry ${cls}">${escapeHtml(step)}</div>`;
    });
    html += '</div></div>';
    timelineDiv.innerHTML = html;

    showExplainer(explainerDiv, {
      prover: `Locked ${amount} on Federation A\nIntent ID: ${intentId.slice(0, 20)}...\nSTARK proof of lock submitted\nConditional turn: "if lock verified, mint on B"`,
      verifier: `Federation B verifies:\n- STARK proof that note is locked on A\n- Intent matches expected parameters\n- Conditional turn is valid\n\nMints equivalent note only after verification`,
      delta: `Neither federation sees the other's internal state. The bridge protocol uses ZK proofs to verify cross-domain claims without revealing private data. The atomic swap ensures no value is created or destroyed — conservation is proven cryptographically.`,
      timing: 'simulated',
    });

    animating = false;
  });

  function setNodeActive(id) {
    container.querySelector(`#${id}`).classList.add('active');
  }

  function setArrowActive(id) {
    container.querySelector(`#${id}`).classList.add('active');
  }

  function setStatus(text) {
    container.querySelector('#cf-status').textContent = text;
  }

  function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  function localHash(str) {
    let h = 0x811c9dc5;
    for (let i = 0; i < str.length; i++) {
      h ^= str.charCodeAt(i);
      h = Math.imul(h, 0x01000193);
    }
    return (h >>> 0).toString(16).padStart(8, '0').repeat(8);
  }
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Source federation</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Destination federation</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Cross-domain privacy</div>
          <div class="explainer__cell-content">${escapeHtml(delta)}</div>
        </div>
      </div>
      <div class="explainer__timing">Bridge transfer <span>${timing}</span></div>
    </div>
  `;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
