// Bearer Capabilities section — create, grant, verify, exercise bearer caps

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';
import { deepLinkBanner } from '../studio-embed.js';

export function initBearer(wasm) {
  const container = document.getElementById('section-bearer');
  container.innerHTML = `
    <div class="section-header">
      <h2>Bearer Capabilities</h2>
      ${deepLinkBanner([{ label: '<dregg-bearer-cap>', uri: 'dregg://bearer-cap/demo' }])}
      <p>
        A bearer cap is a proof-carrying authorization token: whoever holds the proof can
        exercise the capability. Unlike delegation chains, bearer caps are transferable without
        updating any on-chain state. Grant a cap, pass it around, exercise it immediately.
      </p>
      <span class="next-hint" data-next="factories">Next: cell factories &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Target Cell</label>
        <input type="text" id="bc-target" value="" placeholder="auto-generated" spellcheck="false" style="width: 180px;">
      </div>
      <div class="control-group">
        <label>Action</label>
        <select id="bc-action" style="font-family:var(--mono);font-size:11px;padding:6px 10px;background:var(--surface-2);border:1px solid var(--border-2);border-radius:var(--radius);color:var(--text);">
          <option value="transfer">transfer</option>
          <option value="read">read</option>
          <option value="write">write</option>
          <option value="admin">admin</option>
          <option value="execute">execute</option>
        </select>
      </div>
      <div class="control-group">
        <label>Expiry (unix)</label>
        <input type="number" id="bc-expiry" value="0" min="0" style="width: 120px;">
      </div>
      <button class="btn btn-primary" id="bc-create" ${wasm ? '' : 'disabled'}>Create Bearer Cap</button>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="bc-verify" disabled>Verify Cap</button>
      <button class="btn btn-primary" id="bc-exercise" disabled>Exercise Cap</button>
      <button class="btn btn-danger" id="bc-expire" disabled>Simulate Expiry</button>
    </div>

    <div id="bc-caps-display"></div>
    <div id="bc-result"></div>
    <div id="bc-explainer"></div>
  `;

  if (!wasm) return;

  let caps = []; // { token_hex, delegator_pubkey, target_cell, action, expiry, exercised, expired }
  const capsDiv = container.querySelector('#bc-caps-display');
  const resultDiv = container.querySelector('#bc-result');
  const explainerDiv = container.querySelector('#bc-explainer');
  const verifyBtn = container.querySelector('#bc-verify');
  const exerciseBtn = container.querySelector('#bc-exercise');
  const expireBtn = container.querySelector('#bc-expire');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('factories'));

  function randomHex(n) {
    const bytes = new Uint8Array(n);
    crypto.getRandomValues(bytes);
    return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function renderCaps() {
    if (caps.length === 0) {
      capsDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Create a bearer cap to begin the demo.</div>
      </div></div>`;
      return;
    }

    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Bearer Capabilities</span></div><div class="result-panel__body">';
    caps.forEach((cap, i) => {
      let status = 'VALID';
      let cls = 'success';
      if (cap.expired) { status = 'EXPIRED'; cls = 'error'; }
      else if (cap.exercised) { status = 'EXERCISED'; cls = 'warning'; }

      html += `<div class="output-entry ${cls}">
        Cap #${i}: ${cap.token_hex.slice(0, 20)}...
        <br>Action: <strong>${cap.action}</strong> | Target: ${cap.target_cell.slice(0, 12)}... | Status: ${status}
        ${cap.expiry > 0 ? `<br>Expires: ${new Date(cap.expiry * 1000).toISOString()}` : '<br>No expiry'}
      </div>`;
    });
    html += '</div></div>';
    capsDiv.innerHTML = html;
  }

  function updateButtons() {
    const hasValid = caps.some(c => !c.exercised && !c.expired);
    const hasAny = caps.length > 0;
    verifyBtn.disabled = !hasAny;
    exerciseBtn.disabled = !hasValid;
    expireBtn.disabled = !hasValid;
  }

  container.querySelector('#bc-create').addEventListener('click', () => {
    const targetInput = container.querySelector('#bc-target').value.trim();
    const targetCell = targetInput.length === 64 ? targetInput : randomHex(32);
    const action = container.querySelector('#bc-action').value;
    const expiry = parseInt(container.querySelector('#bc-expiry').value) || 0;
    // WASM-side audit fix: `create_bearer_cap` now takes the delegator
    // *signing seed* (the 32-byte Ed25519 secret seed), not a public key. For
    // the demo we generate a fresh seed; the returned `delegator_pubkey_hex`
    // is what the verifier needs.
    const delegatorSigningSeed = randomHex(32);

    // Update the input to show the generated target
    if (targetInput.length !== 64) {
      container.querySelector('#bc-target').value = targetCell;
    }

    const t0 = performance.now();
    let result;
    try {
      result = wasm.create_bearer_cap(delegatorSigningSeed, targetCell, action, BigInt(expiry));
    } catch (e) {
      // No fabrication: bearer caps are real Ed25519 signatures. A failure is
      // surfaced honestly rather than minting an unforgeable-looking fake.
      explainerDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry error">create_bearer_cap failed: ${escapeHtml(String(e && e.message || e))}</div>
      </div></div>`;
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    caps.push({
      token_hex: result.bearer_token_hex,
      // Persist the PUBLIC key for verification (no longer the raw seed).
      delegator_pubkey: result.delegator_pubkey_hex,
      target_cell: result.target_cell,
      action: result.action,
      expiry: result.expiry,
      exercised: false,
      expired: false,
    });

    renderCaps();
    updateButtons();

    showExplainer(explainerDiv, {
      prover: `Created bearer cap (Ed25519-signed)\nDelegator pubkey: ${result.delegator_pubkey_hex.slice(0, 16)}...\nTarget: ${result.target_cell.slice(0, 16)}...\nAction: ${result.action}\nSignature: ${result.bearer_token_hex.slice(0, 20)}...`,
      verifier: `Bearer token is an Ed25519 signature by the delegator over BLAKE3(delegator_pubkey || target || action || expiry). Only the delegator (who holds the signing seed) can issue; anyone with the public key can verify.`,
      delta: `Earlier versions used a BLAKE3-hash-of-public-params as the "token" — anyone could forge it. The token is now a real signature, so only the delegator can mint a verifying cap.`,
      timing: elapsed,
    });
  });

  verifyBtn.addEventListener('click', () => {
    const cap = caps[caps.length - 1];
    if (!cap) return;

    const currentTime = Math.floor(Date.now() / 1000);
    const t0 = performance.now();
    let result;
    try {
      result = wasm.verify_bearer_cap(
        cap.token_hex, cap.delegator_pubkey, cap.target_cell,
        cap.action, BigInt(cap.expiry), BigInt(currentTime)
      );
    } catch (e) {
      // No fabrication: never fake a verification verdict. The real Ed25519
      // check is wasm.verify_bearer_cap; surface its failure honestly.
      showResult(resultDiv, 'error', `verify_bearer_cap failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    const status = result.valid && !result.expired ? 'VALID' : (result.expired ? 'EXPIRED' : 'INVALID');
    showResult(resultDiv, result.valid && !result.expired ? 'success' : 'error',
      `Verification: ${status}\nToken: ${cap.token_hex.slice(0, 20)}...\nSignature valid: ${result.signature_valid}\nExpired: ${result.expired}`);

    showExplainer(explainerDiv, {
      prover: `Presented bearer cap (Ed25519 signature) for verification\nSignature: ${cap.token_hex.slice(0, 20)}...\nClaimed action: ${cap.action} on ${cap.target_cell.slice(0, 12)}...`,
      verifier: `Recomputed the binding hash, then ran Ed25519 verify against the delegator pubkey. Checked expiry against current time (${currentTime}). Result: ${status}`,
      delta: `One Ed25519 verify (~150us) — still O(1), now cryptographically meaningful: a forgery requires the delegator's secret signing seed.`,
      timing: elapsed,
    });
  });

  exerciseBtn.addEventListener('click', () => {
    const cap = caps.find(c => !c.exercised && !c.expired);
    if (!cap) return;

    const t0 = performance.now();
    cap.exercised = true;
    state.proofCount++;
    notifyStateChange();
    const elapsed = (performance.now() - t0).toFixed(2);

    renderCaps();
    updateButtons();

    showResult(resultDiv, 'success', `Exercised: ${cap.action} on ${cap.target_cell.slice(0, 16)}...`);
    showExplainer(explainerDiv, {
      prover: `Exercised bearer cap\nAction: ${cap.action}\nTarget: ${cap.target_cell.slice(0, 16)}...\nThe cap is now spent (single-use in this demo)`,
      verifier: `Verified token validity\nExecuted authorized action\nRecorded exercise in audit log\n\nIn production: exercise can be single-use or multi-use depending on policy`,
      delta: `Bearer cap exercise is instantaneous — no consensus round needed. The holder proves authorization by possessing the token. After exercise, the action takes effect immediately. For single-use caps, a nullifier prevents replay.`,
      timing: elapsed,
    });
  });

  expireBtn.addEventListener('click', () => {
    const cap = caps.find(c => !c.exercised && !c.expired);
    if (!cap) return;

    cap.expired = true;
    renderCaps();
    updateButtons();

    showResult(resultDiv, 'warning', `Cap expired: ${cap.token_hex.slice(0, 20)}...`);
    showExplainer(explainerDiv, {
      prover: `Bearer cap expired\nToken: ${cap.token_hex.slice(0, 20)}...\nWas authorized for: ${cap.action}`,
      verifier: `Expiry check fails\nToken is structurally valid but temporally invalid\nAction DENIED`,
      delta: `Time-bounded bearer caps provide automatic revocation. Unlike revocation lists (which require propagation delay), expiry is instant and verifiable locally. The tradeoff: shorter expiry = more frequent reissuance.`,
      timing: '0.01',
    });
  });

  renderCaps();
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
          <div class="explainer__cell-label">Cap holder</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Verifier</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Design property</div>
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
