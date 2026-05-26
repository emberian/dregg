// Tokens section — mint, attenuate, verify

import { state, notifyStateChange, navigateTo } from '../playground.js';

export function initTokens(wasm) {
  const container = document.getElementById('section-tokens');
  container.innerHTML = `
    <div class="section-header">
      <h2>Tokens</h2>
      <!-- Tier 1 playground migration (§4.9 COMPLETE FOLLOWUP-05): deep-link to Starbridge (coexist during transition) -->
      <a href="/starbridge.html?at=pyana://token/demo" target="_blank" style="font-size:0.8em;float:right;">Inspect tokens in Starbridge (pyana://token/... deep) →</a>
      <p>
        Pyana tokens are macaroon-style bearer credentials. A root token is minted from a secret key,
        then attenuated by appending caveats that cryptographically restrict scope. Attenuation is
        one-way — you can narrow permissions but never widen them.
      </p>
      <span class="next-hint" data-next="proofs">Next: generate a STARK proof &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Root Key (32 bytes hex)</label>
        <input type="text" id="tk-root-key" placeholder="Click Generate to create one" maxlength="64" spellcheck="false" style="width: 340px;">
      </div>
      <button class="btn btn-secondary" id="tk-gen-key">Generate</button>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Location</label>
        <input type="text" id="tk-location" value="pyana.dev" spellcheck="false" style="width: 160px;">
      </div>
      <button class="btn btn-primary" id="tk-mint" disabled>Mint Token</button>
    </div>

    <hr style="border: none; border-top: 1px solid var(--border); margin: 20px 0;">

    <h3 style="font-family: var(--display); font-size: 1.1rem; color: var(--text); margin-bottom: 12px;">Attenuate</h3>
    <div class="controls-row">
      <div class="control-group">
        <label>Token</label>
        <select id="tk-att-select" style="width: 240px;">
          <option value="">-- mint a token first --</option>
        </select>
      </div>
      <div class="control-group">
        <label>Service</label>
        <input type="text" id="tk-att-service" value="dns" spellcheck="false" style="width: 100px;">
      </div>
      <div class="control-group">
        <label>Actions</label>
        <input type="text" id="tk-att-actions" value="read,write" spellcheck="false" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Expires (sec)</label>
        <input type="number" id="tk-att-expires" value="3600" min="0" style="width: 80px;">
      </div>
      <button class="btn btn-primary" id="tk-attenuate" disabled>Attenuate</button>
    </div>

    <hr style="border: none; border-top: 1px solid var(--border); margin: 20px 0;">

    <h3 style="font-family: var(--display); font-size: 1.1rem; color: var(--text); margin-bottom: 12px;">Verify</h3>
    <div class="controls-row">
      <div class="control-group">
        <label>Token</label>
        <select id="tk-ver-select" style="width: 240px;">
          <option value="">-- mint a token first --</option>
        </select>
      </div>
      <div class="control-group">
        <label>App ID</label>
        <input type="text" id="tk-ver-app" value="my-app" spellcheck="false" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Action</label>
        <input type="text" id="tk-ver-action" value="read" spellcheck="false" style="width: 100px;">
      </div>
      <button class="btn btn-primary" id="tk-verify" disabled>Verify</button>
    </div>

    <div id="tk-result"></div>
    <div id="tk-explainer"></div>
  `;

  if (!wasm) return;

  const keyInput = container.querySelector('#tk-root-key');
  const mintBtn = container.querySelector('#tk-mint');
  const genBtn = container.querySelector('#tk-gen-key');
  const attBtn = container.querySelector('#tk-attenuate');
  const verBtn = container.querySelector('#tk-verify');
  const attSelect = container.querySelector('#tk-att-select');
  const verSelect = container.querySelector('#tk-ver-select');
  const resultDiv = container.querySelector('#tk-result');
  const explainerDiv = container.querySelector('#tk-explainer');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('proofs'));

  function hexToBytes(hex) {
    const bytes = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
      bytes[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
    }
    return bytes;
  }

  function updateSelects() {
    const opts = state.tokens.map((t, i) =>
      `<option value="${i}">#${i} ${t.attenuated ? '(att)' : '(root)'} ${t.encoded.slice(0, 24)}...</option>`
    );
    const defaultOpt = '<option value="">-- select token --</option>';
    attSelect.innerHTML = defaultOpt + opts.join('');
    verSelect.innerHTML = defaultOpt + opts.join('');
    attBtn.disabled = state.tokens.length === 0;
    verBtn.disabled = state.tokens.length === 0;
  }

  genBtn.addEventListener('click', () => {
    try {
      const result = wasm.generate_root_key();
      keyInput.value = result.key_hex;
      state.rootKey = result.key_bytes;
      state.rootKeyHex = result.key_hex;
      mintBtn.disabled = false;
    } catch (e) {
      showResult('error', `Key generation failed: ${e.message}`);
    }
  });

  mintBtn.addEventListener('click', () => {
    const keyHex = keyInput.value.trim();
    if (keyHex.length !== 64) {
      showResult('error', 'Key must be 64 hex characters (32 bytes)');
      return;
    }
    const keyBytes = hexToBytes(keyHex);
    const location = container.querySelector('#tk-location').value.trim() || 'pyana.dev';

    const t0 = performance.now();
    try {
      const result = wasm.mint_token(keyBytes, location);
      const elapsed = (performance.now() - t0).toFixed(2);

      state.rootKey = keyBytes;
      state.rootKeyHex = keyHex;
      state.tokens.push({
        encoded: result.token,
        location,
        attenuated: false,
        service: null,
        actions: null,
        format: 'em2',
      });
      notifyStateChange();
      updateSelects();

      showResult('success', `Token minted: ${result.token.slice(0, 40)}...`);
      showExplainer({
        prover: `Root key: ${keyHex.slice(0, 16)}...\nLocation: ${location}\nFull token (${result.token.length} chars)`,
        verifier: `Token format: em2\nLocation claim: ${location}\nHMAC signature (verifiable with key)`,
        delta: `The root key is never transmitted.\nThe token is a self-contained bearer credential.\nAnyone with the token can present it, but only the key holder can verify or attenuate.`,
        timing: elapsed,
      });
    } catch (e) {
      showResult('error', `Mint failed: ${e.message}`);
    }
  });

  attBtn.addEventListener('click', () => {
    const idx = parseInt(attSelect.value);
    if (isNaN(idx) || !state.tokens[idx]) return;
    if (!state.rootKey) {
      showResult('error', 'Generate a root key first');
      return;
    }

    const token = state.tokens[idx].encoded;
    const service = container.querySelector('#tk-att-service').value.trim();
    const actions = container.querySelector('#tk-att-actions').value.trim();
    const expires = BigInt(container.querySelector('#tk-att-expires').value || '0');

    const t0 = performance.now();
    try {
      const result = wasm.attenuate_token(token, state.rootKey, service, actions, expires);
      const elapsed = (performance.now() - t0).toFixed(2);

      state.tokens.push({
        encoded: result.token,
        location: state.tokens[idx].location,
        attenuated: true,
        service,
        actions,
        format: 'em2',
      });
      notifyStateChange();
      updateSelects();

      showResult('success', `Attenuated: ${result.token.slice(0, 40)}... (${result.caveats_added} caveats added)`);
      showExplainer({
        prover: `Parent token: #${idx}\nAdded caveats: service=${service}, actions=${actions}, expires=${expires}s\nNew token: ${result.token.slice(0, 24)}...`,
        verifier: `Sees: attenuated token with restricted scope\nCan verify: caveats are cryptographically chained\nCannot: recover parent token or widen permissions`,
        delta: `Attenuation is irreversible. The child token cryptographically commits to narrower permissions. Even the token holder cannot remove caveats — they can only add more.`,
        timing: elapsed,
      });
    } catch (e) {
      showResult('error', `Attenuate failed: ${e.message}`);
    }
  });

  verBtn.addEventListener('click', () => {
    const idx = parseInt(verSelect.value);
    if (isNaN(idx) || !state.tokens[idx]) return;
    if (!state.rootKey) {
      showResult('error', 'Generate a root key first');
      return;
    }

    const token = state.tokens[idx].encoded;
    const appId = container.querySelector('#tk-ver-app').value.trim();
    const action = container.querySelector('#tk-ver-action').value.trim();

    const t0 = performance.now();
    try {
      const result = wasm.verify_token(token, state.rootKey, appId, action);
      const elapsed = (performance.now() - t0).toFixed(2);

      const status = result.allowed ? 'success' : 'warning';
      showResult(status, `${result.allowed ? 'ALLOWED' : 'DENIED'} — ${result.policy || 'default policy'}`);
      showExplainer({
        prover: `Presented token #${idx}\nRequested: app=${appId}, action=${action}`,
        verifier: `Decision: ${result.allowed ? 'ALLOWED' : 'DENIED'}\nPolicy matched: ${result.policy || 'default deny'}\nVerified HMAC chain integrity`,
        delta: `The verifier learns only whether the request is authorized. It does not learn the root key, the full caveat chain, or what other permissions the token might have.`,
        timing: elapsed,
      });
    } catch (e) {
      showResult('error', `Verify failed: ${e.message}`);
    }
  });

  function showResult(type, message) {
    resultDiv.innerHTML = `<div class="result-panel">
      <div class="result-panel__body">
        <div class="output-entry ${type}">${escapeHtml(message)}</div>
      </div>
    </div>`;
  }

  function showExplainer({ prover, verifier, delta, timing }) {
    explainerDiv.innerHTML = `
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
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
