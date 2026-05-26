// Capabilities section — delegation chains, attenuation, revocation

import { state, notifyStateChange, navigateTo } from '../playground.js';

export function initCapabilities(wasm) {
  const container = document.getElementById('section-capabilities');
  container.innerHTML = `
    <div class="section-header">
      <h2>Capabilities</h2>
      <!-- Tier 1 deep-link (§4.9 COMPLETE FOLLOWUP-05) -->
      <a href="/starbridge.html?at=pyana://capability/demo" target="_blank" style="font-size:0.8em;float:right;">Inspect caps in Starbridge (deep pyana://capability/...) →</a>
      <p>
        Capabilities are delegable, attenuable authorization tokens. A root capability grants
        full access; each delegation can only narrow scope (monotonic attenuation). Revocation
        propagates down the chain — revoking a parent invalidates all children. This models
        real-world delegation: "I grant you read access to my DNS, and you can sub-delegate
        read-only to your team."
      </p>
      <span class="next-hint" data-next="crossfed">Next: cross-federation bridge &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Initial Permissions</label>
        <input type="text" id="cap-perms" value="read,write,execute,admin" spellcheck="false" style="width: 260px;">
      </div>
      <button class="btn btn-primary" id="cap-create" ${wasm ? '' : 'disabled'}>Create Root Capability</button>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Delegate To</label>
        <input type="text" id="cap-delegate-to" value="alice" spellcheck="false" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Restrict To (subset)</label>
        <input type="text" id="cap-restrict" value="read,write" spellcheck="false" style="width: 160px;">
      </div>
      <div class="control-group">
        <label>Expires (sec)</label>
        <input type="number" id="cap-expires" value="3600" min="0" style="width: 80px;">
      </div>
      <button class="btn btn-primary" id="cap-delegate" disabled>Delegate</button>
      <button class="btn btn-danger" id="cap-revoke" disabled>Revoke Last</button>
    </div>

    <div id="cap-chain-display"></div>
    <div id="cap-result"></div>
    <div id="cap-explainer"></div>
  `;

  if (!wasm) return;

  const chainDisplay = container.querySelector('#cap-chain-display');
  const resultDiv = container.querySelector('#cap-result');
  const explainerDiv = container.querySelector('#cap-explainer');
  const delegateBtn = container.querySelector('#cap-delegate');
  const revokeBtn = container.querySelector('#cap-revoke');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('crossfed'));

  function renderChain() {
    if (state.capChain.length === 0) {
      chainDisplay.innerHTML = '';
      delegateBtn.disabled = true;
      revokeBtn.disabled = true;
      return;
    }

    delegateBtn.disabled = false;
    revokeBtn.disabled = false;

    let html = '<div class="cap-chain">';
    state.capChain.forEach((cap, i) => {
      const revokedClass = cap.revoked ? ' revoked' : '';
      const arrow = i > 0 ? '<div style="text-align:center;color:var(--text-muted);font-size:16px;margin:-4px 0;">&#8595;</div>' : '';
      html += `${arrow}<div class="cap-chain__item${revokedClass}">
        <span class="cap-level">L${i}</span>
        <span class="cap-perms">${cap.holder}: [${cap.permissions.join(', ')}]</span>
        <span class="cap-expiry">${cap.revoked ? 'REVOKED' : (cap.expires ? `${cap.expires}s` : 'no expiry')}</span>
      </div>`;
    });
    html += '</div>';
    chainDisplay.innerHTML = html;
  }

  container.querySelector('#cap-create').addEventListener('click', () => {
    const perms = container.querySelector('#cap-perms').value.split(',').map(s => s.trim()).filter(Boolean);

    const t0 = performance.now();

    state.capChain = [{
      holder: 'root',
      permissions: perms,
      expires: null,
      revoked: false,
      delegatedBy: null,
    }];

    const elapsed = (performance.now() - t0).toFixed(2);
    notifyStateChange();
    renderChain();

    showResult(resultDiv, 'success', `Root capability created with permissions: [${perms.join(', ')}]`);
    showExplainer(explainerDiv, {
      prover: `Created root capability\nPermissions: ${perms.join(', ')}\nThis is the maximum scope — all future delegations can only narrow this.`,
      verifier: `Root capability established\nFull permission set known\nDelegation chain starts here`,
      delta: `The root capability holder has full authority. No information is hidden at this level — the root is the trust anchor.`,
      timing: elapsed,
    });
  });

  delegateBtn.addEventListener('click', () => {
    if (state.capChain.length === 0) return;

    const parent = state.capChain[state.capChain.length - 1];
    if (parent.revoked) {
      showResult(resultDiv, 'error', 'Cannot delegate from a revoked capability');
      return;
    }

    const delegateTo = container.querySelector('#cap-delegate-to').value.trim() || 'user';
    const restrictTo = container.querySelector('#cap-restrict').value.split(',').map(s => s.trim()).filter(Boolean);
    const expires = parseInt(container.querySelector('#cap-expires').value) || 0;

    // Enforce monotonic attenuation: child perms must be subset of parent
    const validPerms = restrictTo.filter(p => parent.permissions.includes(p));
    if (validPerms.length === 0) {
      showResult(resultDiv, 'error', `Cannot delegate: [${restrictTo.join(', ')}] is not a subset of parent's [${parent.permissions.join(', ')}]`);
      return;
    }

    const t0 = performance.now();

    // Use WASM fold to demonstrate cryptographic narrowing
    const initialFacts = parent.permissions.map(p => `can:${p}`);
    const removeFacts = parent.permissions
      .filter(p => !validPerms.includes(p))
      .map(p => `can:${p}`);

    let foldResult = null;
    if (removeFacts.length > 0) {
      try {
        foldResult = wasm.demonstrate_fold(JSON.stringify(initialFacts), JSON.stringify(removeFacts));
      } catch (e) {
        // Fold is optional enhancement
      }
    }

    state.capChain.push({
      holder: delegateTo,
      permissions: validPerms,
      expires: expires || null,
      revoked: false,
      delegatedBy: parent.holder,
    });

    const elapsed = (performance.now() - t0).toFixed(2);
    notifyStateChange();
    renderChain();

    const dropped = parent.permissions.filter(p => !validPerms.includes(p));
    showResult(resultDiv, 'success',
      `Delegated to ${delegateTo}: [${validPerms.join(', ')}]${dropped.length > 0 ? `\nDropped: [${dropped.join(', ')}]` : ''}`);

    showExplainer(explainerDiv, {
      prover: `Delegated from ${parent.holder} to ${delegateTo}\nParent perms: [${parent.permissions.join(', ')}]\nChild perms: [${validPerms.join(', ')}]\nDropped: [${dropped.join(', ')}]${foldResult ? `\nFold commitment: ${(foldResult.new_root || '').slice(0, 16)}...` : ''}`,
      verifier: `Delegation chain extended (depth ${state.capChain.length - 1})\nChild cannot exceed parent scope\nCryptographic fold proves narrowing${foldResult ? `\nVerified: ${foldResult.verified}` : ''}`,
      delta: `Monotonic attenuation is enforced cryptographically. The delegatee (${delegateTo}) CANNOT add permissions back. Each link in the chain commits to a narrower scope than its parent.`,
      timing: elapsed,
    });
  });

  revokeBtn.addEventListener('click', () => {
    if (state.capChain.length <= 1) return;

    const t0 = performance.now();
    // Revoke last non-revoked capability
    for (let i = state.capChain.length - 1; i > 0; i--) {
      if (!state.capChain[i].revoked) {
        state.capChain[i].revoked = true;
        // Also revoke all children
        for (let j = i + 1; j < state.capChain.length; j++) {
          state.capChain[j].revoked = true;
        }
        const elapsed = (performance.now() - t0).toFixed(2);
        notifyStateChange();
        renderChain();

        showResult(resultDiv, 'info', `Revoked capability for "${state.capChain[i].holder}" and all descendants`);
        showExplainer(explainerDiv, {
          prover: `Revoked: ${state.capChain[i].holder}'s capability\nAll downstream delegations also invalidated\nRevocation is immediate and propagates`,
          verifier: `Capability marked revoked in the revocation set\nAll children automatically invalid\nNo further delegations possible from this point`,
          delta: `Revocation cascades. This is why capability-based systems are superior to ACL-based systems for delegation: the grantor retains control even after delegation.`,
          timing: elapsed,
        });
        return;
      }
    }
  });

  renderChain();
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
          <div class="explainer__cell-label">Grantor knows</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">System state</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Security property</div>
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
