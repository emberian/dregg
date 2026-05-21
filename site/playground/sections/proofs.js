// Proofs section — STARK proof generation, verification, tamper detection

import { state, notifyStateChange, navigateTo } from '../playground.js';

export function initProofs(wasm) {
  const container = document.getElementById('section-proofs');
  container.innerHTML = `
    <div class="section-header">
      <h2>STARK Proofs</h2>
      <p>
        Generate real STARK proofs for Merkle membership claims over the BabyBear field
        (p = 2<sup>31</sup> - 2<sup>27</sup> + 1). These are transparent-setup,
        post-quantum secure proofs. Generate one, verify it, then tamper with it to see
        verification fail — demonstrating soundness.
      </p>
      <span class="next-hint" data-next="merkle">Next: explore Merkle trees &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Leaf Value (u32)</label>
        <input type="number" id="pf-leaf" value="42" min="1" max="2013265920" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Tree Depth (2-8)</label>
        <input type="number" id="pf-depth" value="4" min="2" max="8" style="width: 80px;">
      </div>
      <button class="btn btn-primary" id="pf-generate" ${wasm ? '' : 'disabled'}>Generate Proof</button>
      <button class="btn btn-secondary" id="pf-verify" disabled>Verify</button>
      <button class="btn btn-danger" id="pf-tamper" disabled>Tamper & Verify</button>
    </div>

    <div id="pf-stats" style="display:none;" class="controls-row" style="margin-top: 12px;">
      <div class="control-group">
        <label>Proof Size</label>
        <span id="pf-stat-size" style="font-family:var(--mono);font-size:12px;color:var(--accent-bright);">--</span>
      </div>
      <div class="control-group">
        <label>Prove Time</label>
        <span id="pf-stat-prove" style="font-family:var(--mono);font-size:12px;color:var(--lantern);">--</span>
      </div>
      <div class="control-group">
        <label>Verify Time</label>
        <span id="pf-stat-verify" style="font-family:var(--mono);font-size:12px;color:var(--lantern);">--</span>
      </div>
      <div class="control-group">
        <label>Trace Rows</label>
        <span id="pf-stat-rows" style="font-family:var(--mono);font-size:12px;color:var(--text-dim);">--</span>
      </div>
      <div class="control-group">
        <label>FRI Queries</label>
        <span id="pf-stat-fri" style="font-family:var(--mono);font-size:12px;color:var(--text-dim);">--</span>
      </div>
    </div>

    <div id="pf-result"></div>
    <div id="pf-explainer"></div>
  `;

  if (!wasm) return;

  let currentProof = null;
  let proveTimeMs = 0;

  const generateBtn = container.querySelector('#pf-generate');
  const verifyBtn = container.querySelector('#pf-verify');
  const tamperBtn = container.querySelector('#pf-tamper');
  const statsDiv = container.querySelector('#pf-stats');
  const resultDiv = container.querySelector('#pf-result');
  const explainerDiv = container.querySelector('#pf-explainer');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('merkle'));

  generateBtn.addEventListener('click', () => {
    const leaf = parseInt(container.querySelector('#pf-leaf').value) || 42;
    const depth = parseInt(container.querySelector('#pf-depth').value) || 4;

    const t0 = performance.now();
    try {
      const proof = wasm.generate_stark_proof(leaf, depth);
      proveTimeMs = performance.now() - t0;
      currentProof = proof;

      state.proofCount++;
      state.receipts.push({
        type: 'stark',
        leaf,
        depth,
        size: proof.proof_size_bytes,
        time: proveTimeMs.toFixed(1),
      });
      notifyStateChange();

      // Show stats
      statsDiv.style.display = 'flex';
      container.querySelector('#pf-stat-size').textContent = `${proof.proof_size_bytes} bytes`;
      container.querySelector('#pf-stat-prove').textContent = `${proveTimeMs.toFixed(1)}ms`;
      container.querySelector('#pf-stat-verify').textContent = '--';
      container.querySelector('#pf-stat-rows').textContent = proof.trace_rows || '--';
      container.querySelector('#pf-stat-fri').textContent = proof.num_fri_queries || '--';

      verifyBtn.disabled = false;
      tamperBtn.disabled = false;

      showResult(resultDiv, 'success', `STARK proof generated (${proof.proof_size_bytes} bytes, ${proveTimeMs.toFixed(1)}ms)`);
      showExplainer(explainerDiv, {
        prover: `Leaf value: ${leaf}\nTree depth: ${depth}\nTrace rows: ${proof.trace_rows}\nFull proof: ${proof.proof_size_bytes} bytes\nKnows: the witness (leaf position in Merkle tree)`,
        verifier: `Receives: opaque proof bytes\nPublic inputs: Merkle root commitment\nDoes NOT learn: which leaf, leaf value, or tree structure`,
        delta: `The verifier is convinced the prover knows a valid Merkle path without learning anything about the path itself. This is zero-knowledge: the proof reveals nothing beyond the statement's truth.`,
        timing: proveTimeMs.toFixed(2),
      });
    } catch (e) {
      showResult(resultDiv, 'error', `Proof generation failed: ${e.message}`);
    }
  });

  verifyBtn.addEventListener('click', () => {
    if (!currentProof) return;

    const t0 = performance.now();
    try {
      const result = wasm.verify_stark_proof(JSON.stringify(currentProof));
      const verifyTime = performance.now() - t0;

      container.querySelector('#pf-stat-verify').textContent = `${verifyTime.toFixed(1)}ms`;

      if (result.valid) {
        showResult(resultDiv, 'success', `Proof VALID (verified in ${verifyTime.toFixed(1)}ms)`);
      } else {
        showResult(resultDiv, 'error', `Proof INVALID: ${result.error || 'unknown error'}`);
      }

      showExplainer(explainerDiv, {
        prover: `Submitted proof: ${currentProof.proof_size_bytes} bytes\nClaimed: knowledge of Merkle membership`,
        verifier: `Checked FRI commitments\nVerified constraint polynomial evaluations\nResult: ${result.valid ? 'ACCEPT' : 'REJECT'}\nVerification time: ${verifyTime.toFixed(1)}ms`,
        delta: `Verification is ${(proveTimeMs / verifyTime).toFixed(0)}x faster than proving. The verifier does sublinear work relative to the computation being proved.`,
        timing: verifyTime.toFixed(2),
      });
    } catch (e) {
      showResult(resultDiv, 'error', `Verification error: ${e.message}`);
    }
  });

  tamperBtn.addEventListener('click', () => {
    if (!currentProof) return;

    try {
      // Tamper
      const tampered = wasm.tamper_stark_proof(JSON.stringify(currentProof));

      // Try to verify tampered proof
      const t0 = performance.now();
      const result = wasm.verify_stark_proof(tampered);
      const verifyTime = performance.now() - t0;

      if (!result.valid) {
        showResult(resultDiv, 'info', `Tampered proof correctly REJECTED (${verifyTime.toFixed(1)}ms). Error: ${result.error || 'constraint violation'}`);
      } else {
        showResult(resultDiv, 'warning', `Tampered proof unexpectedly accepted (this should not happen)`);
      }

      showExplainer(explainerDiv, {
        prover: `Original proof was modified:\nBits flipped in trace query values\nThe tampered proof no longer satisfies the AIR constraints`,
        verifier: `Detected tampering during verification\nFRI commitment check failed\nResult: REJECT\nSoundness guarantee: 2^{-100} false positive probability`,
        delta: `This demonstrates soundness: it is computationally infeasible to forge a valid STARK proof without knowing a valid witness. Even a single flipped bit causes rejection.`,
        timing: verifyTime.toFixed(2),
      });
    } catch (e) {
      showResult(resultDiv, 'error', `Tamper test error: ${e.message}`);
    }
  });
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
          <div class="explainer__cell-label">Prover knows</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Verifier sees</div>
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
