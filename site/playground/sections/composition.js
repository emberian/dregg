// Proof Composition section — compose multiple proofs using AND/OR/Chain/Aggregate

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initComposition(wasm) {
  const container = document.getElementById('section-composition');
  container.innerHTML = `
    <div class="section-header">
      <h2>Proof Composition</h2>
      <p>
        Compose multiple independent proofs into a single composed proof. Supports AND (all must
        hold), OR (at least one), Chain (sequential dependency), and Aggregate (batch verification).
        This enables complex multi-step authorization with a single verification.
      </p>
      <span class="next-hint" data-next="gallery">Next: interactive gallery &#8594;</span>
    </div>

    <h3 style="font-family:var(--mono);font-size:12px;color:var(--accent-bright);margin-bottom:12px;">Generate Individual Proofs</h3>
    <div class="controls-row">
      <button class="btn btn-primary" id="comp-gen-membership" ${wasm ? '' : 'disabled'}>Membership Proof</button>
      <button class="btn btn-primary" id="comp-gen-range" ${wasm ? '' : 'disabled'}>Range Proof</button>
      <button class="btn btn-primary" id="comp-gen-conservation" ${wasm ? '' : 'disabled'}>Conservation Proof</button>
      <button class="btn btn-secondary" id="comp-clear">Clear All</button>
    </div>

    <h3 style="font-family:var(--mono);font-size:12px;color:var(--accent-bright);margin:16px 0 12px;">Compose</h3>
    <div class="controls-row">
      <div class="control-group">
        <label>Mode</label>
        <select id="comp-mode" style="font-family:var(--mono);font-size:11px;padding:6px 10px;background:var(--surface-2);border:1px solid var(--border-2);border-radius:var(--radius);color:var(--text);">
          <option value="and">AND (all must hold)</option>
          <option value="or">OR (at least one)</option>
          <option value="chain">Chain (sequential)</option>
          <option value="aggregate">Aggregate (batch)</option>
        </select>
      </div>
      <button class="btn btn-primary" id="comp-compose" disabled>Compose Proofs</button>
    </div>

    <div id="comp-proofs-display"></div>
    <div id="comp-result"></div>
    <div id="comp-explainer"></div>
  `;

  if (!wasm) return;

  let proofs = []; // { type, proof_json, public_inputs, description }
  let composedResult = null;
  const proofsDiv = container.querySelector('#comp-proofs-display');
  const resultDiv = container.querySelector('#comp-result');
  const explainerDiv = container.querySelector('#comp-explainer');
  const composeBtn = container.querySelector('#comp-compose');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('gallery'));

  function randomHex(n) {
    const bytes = new Uint8Array(n);
    crypto.getRandomValues(bytes);
    return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function renderProofs() {
    if (proofs.length === 0 && !composedResult) {
      proofsDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Generate individual proofs, then compose them into a single proof.</div>
      </div></div>`;
      return;
    }

    let html = '';

    if (proofs.length > 0) {
      html += '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Individual Proofs</span></div><div class="result-panel__body">';
      proofs.forEach((p, i) => {
        html += `<div class="output-entry info">
          Proof #${i + 1}: <strong>${p.type}</strong>
          <br>${p.description}
          <br><span style="color:var(--text-muted);">Public inputs: [${p.public_inputs.join(', ')}]</span>
        </div>`;
      });
      html += '</div></div>';
    }

    if (composedResult) {
      html += `<div class="result-panel" style="margin-top:12px;"><div class="result-panel__header"><span class="result-panel__title">Composed Proof</span><span class="result-panel__timing">${composedResult.mode.toUpperCase()}</span></div><div class="result-panel__body">
        <div class="output-entry ${composedResult.valid ? 'success' : 'error'}">
          Mode: ${composedResult.mode} | Inputs: ${composedResult.input_count} | Valid: ${composedResult.valid}
          <br>Composed proof: ${composedResult.composed_proof.slice(0, 40)}...
        </div>
      </div></div>`;
    }

    proofsDiv.innerHTML = html;
  }

  function updateButtons() {
    composeBtn.disabled = proofs.length < 2;
  }

  // Generate a membership proof
  container.querySelector('#comp-gen-membership').addEventListener('click', () => {
    const t0 = performance.now();
    const leafValue = Math.floor(Math.random() * 1000);
    let proofJson;
    try {
      const result = wasm.generate_demo_stark_proof(leafValue, 3);
      proofJson = JSON.stringify(result);
    } catch (e) {
      // No fabrication: a wasm proof failure is surfaced, not faked.
      showResult(resultDiv, 'error', `generate_demo_stark_proof failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    proofs.push({
      type: 'Merkle Membership',
      proof_json: proofJson,
      public_inputs: [leafValue, 3],
      description: `Proves leaf ${leafValue} exists in tree of depth 3`,
    });

    state.proofCount++;
    notifyStateChange();
    renderProofs();
    updateButtons();

    showResult(resultDiv, 'success', `Generated membership proof for leaf ${leafValue} (${elapsed}ms)`);
  });

  // Generate a range proof
  container.querySelector('#comp-gen-range').addEventListener('click', () => {
    const t0 = performance.now();
    const amount = Math.floor(Math.random() * 10000);
    const blindingBytes = new Uint8Array(32);
    crypto.getRandomValues(blindingBytes);
    const commitBytes = new Uint8Array(32);
    crypto.getRandomValues(commitBytes);

    let proofJson;
    try {
      const result = wasm.generate_range_proof(BigInt(amount), blindingBytes, commitBytes);
      proofJson = JSON.stringify(result);
    } catch (e) {
      showResult(resultDiv, 'error', `generate_range_proof failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    proofs.push({
      type: 'Range Proof',
      proof_json: proofJson,
      public_inputs: [amount % 256, 64], // public: commitment byte, bit-width
      description: `Range proof: placeholder pending real Bulletproofs (not yet a sound [0, 2^64) proof)`,
    });

    state.proofCount++;
    notifyStateChange();
    renderProofs();
    updateButtons();

    showResult(resultDiv, 'success', `Generated range proof (${elapsed}ms)`);
  });

  // Generate a conservation proof — REAL generate -> verify roundtrip.
  container.querySelector('#comp-gen-conservation').addEventListener('click', () => {
    const t0 = performance.now();
    // Balanced set: 1000 == 700 + 300, with real Pedersen commitments.
    const inputBlinding = randomHex(32);
    const outBlinding1 = randomHex(32);
    const outBlinding2 = randomHex(32);
    const messageHex = randomHex(32);

    let proofJson, verdict;
    try {
      const proved = wasm.prove_conservation(
        JSON.stringify([{ value: 1000, blinding_hex: inputBlinding }]),
        JSON.stringify([
          { value: 700, blinding_hex: outBlinding1 },
          { value: 300, blinding_hex: outBlinding2 },
        ]),
        messageHex
      );
      verdict = wasm.verify_conservation_proof(
        JSON.stringify(proved.input_commitments),
        JSON.stringify(proved.output_commitments),
        JSON.stringify(proved.proof),
        proved.message_hex
      );
      proofJson = JSON.stringify({ ...proved, verdict, type: 'conservation' });
    } catch (e) {
      // No fabrication: a wasm failure is surfaced, not faked as valid.
      showResult(resultDiv, 'error', `conservation prove/verify failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    proofs.push({
      type: 'Conservation',
      proof_json: proofJson,
      public_inputs: [1, 2], // input_count, output_count
      description: `REAL Schnorr excess proof: sum(1 input)==sum(2 outputs), valid=${verdict.valid}, range_proofs_checked=${verdict.range_proofs_checked}`,
    });

    state.proofCount++;
    notifyStateChange();
    renderProofs();
    updateButtons();

    const label = verdict.valid
      ? `valid=true (range_proofs_checked=false — placeholder pending real Bulletproofs)`
      : `valid=false${verdict.error ? ' (' + verdict.error + ')' : ''}`;
    showResult(resultDiv, verdict.valid ? 'success' : 'warning', `Generated + verified conservation proof: ${label} (${elapsed}ms)`);
  });

  // Compose proofs
  composeBtn.addEventListener('click', () => {
    if (proofs.length < 2) return;
    const mode = container.querySelector('#comp-mode').value;

    const t0 = performance.now();
    const proofsInput = proofs.map(p => ({
      proof_json: p.proof_json,
      public_inputs: p.public_inputs,
    }));

    // WASM-side audit fix: compose_proofs returns `valid: false` because it
    // doesn't actually verify input proofs (just BLAKE3-hashes their JSON).
    // The `composed_proof` field is an opaque content-addressable identifier,
    // not a verifiable proof.
    let result;
    try {
      result = wasm.compose_proofs(JSON.stringify(proofsInput), mode);
    } catch (e) {
      showResult(resultDiv, 'error', `compose_proofs failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    composedResult = result;
    state.proofCount++;
    notifyStateChange();
    renderProofs();

    const modeDescriptions = {
      and: 'ALL proofs must verify for the composition to be valid',
      or: 'At LEAST ONE proof must verify',
      chain: 'Proofs are verified in sequence; each depends on the previous',
      aggregate: 'All proofs are batch-verified in a single pass (amortized cost)',
    };

    const validityLabel = result.valid
      ? 'VALID'
      : 'STUB (compose_proofs does not yet verify input proofs)';
    showExplainer(explainerDiv, {
      prover: `Composed ${proofs.length} proofs in "${mode}" mode:\n${proofs.map((p, i) => `  ${i + 1}. ${p.type}`).join('\n')}\n\nContent identifier: ${result.composed_proof.slice(0, 24)}...`,
      verifier: `Verification mode: ${mode.toUpperCase()}\n${modeDescriptions[mode]}\n\nResult: ${validityLabel}\nInput proofs: ${result.input_count}`,
      delta: `Composition target: O(1) verification of the conjunction. Current WASM implementation only emits a content-addressable identifier; real composition (deserialize each proof, verify, return conjunction) is pending.`,
      timing: elapsed,
    });
  });

  // Clear
  container.querySelector('#comp-clear').addEventListener('click', () => {
    proofs = [];
    composedResult = null;
    renderProofs();
    updateButtons();
    resultDiv.innerHTML = '';
    explainerDiv.innerHTML = '';
  });

  renderProofs();
}

function showResult(el, type, message) {
  el.innerHTML = `<div class="result-panel">
    <div class="result-panel__body">
      <div class="output-entry ${type}">${escapeHtml(message)}</div>
    </div>
  </div>`;
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Composer</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Verifier</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Composition benefit</div>
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
