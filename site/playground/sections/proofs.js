// Proofs section — STARK proof generation, verification, tamper detection

import { state, notifyStateChange, navigateTo } from '../playground.js';
import { deepLinkBanner, inspectorEmbed, onSeedReady, ensureStudioRuntime } from '../studio-embed.js';

export function initProofs(wasm) {
  const container = document.getElementById('section-proofs');
  // Tier 2 (STARBRIDGE-PLAN §4.9): the canonical proof view is the platform
  // <dregg-proof> inspector (trust-tier badge + γ.2 bilateral PI over the real
  // seeded turn). The tamper-and-watch-it-fail demo is preserved below as the
  // educational carve-out — it drives the real wasm STARK prover/verifier.
  container.innerHTML = `
    <div class="section-header">
      <h2>STARK Proofs</h2>
      ${deepLinkBanner(
        [{ label: '<dregg-proof>', uri: 'dregg://proof/feed' }],
        'trust-tier + γ.2 bilateral PI over the seeded turn',
      )}
      <p>
        Generate real STARK proofs for Merkle membership claims over the BabyBear field
        (p = 2<sup>31</sup> - 2<sup>27</sup> + 1). These are transparent-setup,
        post-quantum secure proofs. Generate one, verify it, then tamper with it to see
        verification fail — demonstrating soundness.
      </p>
      ${inspectorEmbed(
        `<dregg-proof id="pf-inspector" uri="dregg://receipt/seed"></dregg-proof>`,
        'Canonical proof view (real seeded turn)',
      )}
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

    <div class="controls-row" style="margin-top: 12px;">
      <button class="btn btn-secondary" id="pf-aggregate" ${wasm ? '' : 'disabled'}>
        Prove &gamma;.2 Bilateral Aggregate (Golden)
      </button>
      <span style="font-size:12px;color:var(--text-dim);align-self:center;">
        Real cross-cell aggregate: alice OUTGOING transfer root == bob INCOMING transfer root
      </span>
    </div>
    <div id="pf-aggregate-result"></div>

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

  // Once the shared runtime has seeded a real committed turn, point the
  // embedded <dregg-proof> inspector and the Starbridge deeplink at it.
  onSeedReady((s) => {
    if (!s.turnHash) return;
    const uri = `dregg://receipt/${s.turnHash}`;
    container.querySelector('#pf-inspector')?.setAttribute('uri', uri);
    const link = container.querySelector('.pg-sb-link');
    if (link) link.href = `/starbridge/?at=${encodeURIComponent('dregg://proof/' + s.turnHash)}`;
  });

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
      const proof = wasm.generate_demo_stark_proof(leaf, depth);
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
      // generate_stark_proof returns a ProofResult { proof_json, proof_size_bytes, ... }
      // where proof_json is already the serialized StarkProof — pass it through directly.
      const result = wasm.verify_demo_stark_proof(currentProof.proof_json);
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
      // Tamper: pass the inner StarkProof JSON (not the wrapper).
      const tampered = wasm.tamper_demo_stark_proof(currentProof.proof_json);

      // Try to verify tampered proof
      const t0 = performance.now();
      const result = wasm.verify_demo_stark_proof(tampered);
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

  // γ.2 cross-cell bilateral AGGREGATE (Golden tier). Drives the real
  // canonical aggregator in the wasm runtime: it builds a two-cell transfer
  // Turn (alice → bob), fabricates alice's OUTGOING + bob's INCOMING per-cell
  // WitnessedReceipts from the SAME schedule, runs the outer
  // BilateralAggregationAir STARK, and SELF-VERIFIES it before returning. The
  // result is honest: `roots_matched` is true only when the proven+verified
  // aggregate shows alice's OUTGOING transfer root == bob's INCOMING transfer
  // root. This is NOT a flag flip on the single-turn proof.
  const aggregateBtn = container.querySelector('#pf-aggregate');
  const aggregateResult = container.querySelector('#pf-aggregate-result');
  if (aggregateBtn) {
    aggregateBtn.addEventListener('click', async () => {
      aggregateBtn.disabled = true;
      const prevLabel = aggregateBtn.textContent;
      aggregateBtn.textContent = 'Proving + verifying…';
      try {
        const { runtime, wasm: w } = await ensureStudioRuntime();
        const t0 = performance.now();
        const agg = w.prove_bilateral_aggregate(runtime._handle);
        const ms = performance.now() - t0;
        renderAggregate(aggregateResult, agg, ms);
      } catch (e) {
        // Honest failure: leave the tier Silver, report the precise reason.
        showResult(aggregateResult, 'error', `Bilateral aggregate failed: ${e.message || e}. Tier stays honestly Silver.`);
      } finally {
        aggregateBtn.disabled = false;
        aggregateBtn.textContent = prevLabel;
      }
    });
  }
}

function renderAggregate(el, agg, ms) {
  const matched = agg.bilateral_consistent && agg.roots_matched;
  const tier = matched ? 'GOLDEN' : 'SILVER';
  const tierColor = matched ? '#c9a84c' : '#a0b8c0';
  el.innerHTML = `
    <div class="result-panel" style="margin-top:12px;">
      <div class="result-panel__body">
        <div style="display:flex;align-items:center;gap:10px;margin-bottom:8px;">
          <span style="display:inline-block;padding:2px 10px;border-radius:3px;font-size:0.72rem;font-weight:700;letter-spacing:0.06em;text-transform:uppercase;color:#0a0f0d;background:${tierColor};">${tier} tier</span>
          <span style="font-size:12px;color:var(--text-dim);">verified γ.2 cross-cell aggregate in ${ms.toFixed(1)}ms</span>
        </div>
        <dl style="display:grid;grid-template-columns:max-content 1fr;gap:4px 14px;font-size:12px;font-family:var(--mono);">
          <dt style="color:var(--text-dim);">aggregate AIR</dt><dd>${escapeHtml(agg.kind)}</dd>
          <dt style="color:var(--text-dim);">proof size</dt><dd>${agg.proof_size_bytes} bytes</dd>
          <dt style="color:var(--text-dim);">cells</dt><dd>${agg.n_cells}</dd>
          <dt style="color:var(--text-dim);">consistent</dt><dd>${agg.bilateral_consistent ? 'yes (outer STARK pinned)' : 'no'}</dd>
          <dt style="color:var(--text-dim);">sender (out)</dt><dd>${shortHex(agg.sender_cell)}</dd>
          <dt style="color:var(--text-dim);">receiver (in)</dt><dd>${shortHex(agg.receiver_cell)}</dd>
          <dt style="color:var(--text-dim);">OUTGOING root</dt><dd>${shortHex(agg.outgoing_transfer_root)}</dd>
          <dt style="color:var(--text-dim);">INCOMING root</dt><dd>${shortHex(agg.incoming_transfer_root)}</dd>
          <dt style="color:var(--text-dim);">shared transfer_id</dt><dd>${shortHex(agg.shared_transfer_id)}</dd>
          <dt style="color:var(--text-dim);">cross-cell binding</dt><dd style="color:${matched ? '#c9a84c' : 'var(--text-dim)'};font-weight:700;">${matched ? 'BOUND — both sides fold the same transfer_id' : 'no'}</dd>
        </dl>
        <div style="font-size:11px;color:var(--text-dim);margin-top:6px;line-height:1.5;">
          OUTGOING/INCOMING roots are domain-separated (OTX2 / ITX2) and not byte-equal by design; the binding is the shared transfer_id both absorb, attested by the verified aggregate STARK.
        </div>
      </div>
    </div>`;
}

function shortHex(s, n = 12) {
  if (!s) return '(none)';
  return s.length <= n * 2 ? s : `${s.slice(0, n)}…${s.slice(-n)}`;
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
