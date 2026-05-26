/**
 * <pyana-cipherclerk uri="pyana://cipherclerk/<agent_index>">
 *
 * Inspector for pyana_sdk::AgentCipherclerk — the canonical agent identity +
 * token holdings. Surfaces public-key material only; private keys and seed
 * material are never shown.
 *
 * URI form:
 *   pyana://cipherclerk/0       — agent at index 0
 *   pyana://cipherclerk/alice   — (future) by name; index-only today
 *
 * Data sources (all through runtime signals / escape hatch; no cargo changes):
 *   - agent name + public_key + cell_id  — from create_agent result (cached by
 *     the JS runtime as a computed over getCapabilityTree which surfaces these)
 *   - capability tree (held caps count)  — runtime.listCapabilities(agentIdx)
 *   - receipt chain                      — runtime.listReceipts(agentIdx)
 *   - held tokens (HeldCapability list)  — runtime._wasm.get_capability_tree
 *     re-exposes held_tokens indirectly; direct token listing is NOT yet a
 *     first-class wasm export → now surfaced via <pyana-attenuated-token> + <pyana-bearer-cap>
 *     (Wave 3 inspectors; see their demo attenuate flows + cipherclerk Holdings tab)
 *   - sovereign cells                    — derived from listCells() filtered by
 *     matching public_key
 *
 * Modes:
 *   default  — four-tab inspector (Identity | Holdings | History | Stealth)
 *   compact  — single-line: "name · N tokens · M caps · K receipts"
 *
 * Platform-vocabulary directive (Houyhnhnm § 4.2 / STARBRIDGE-PLAN § 4.5):
 *   Embeds <pyana-cell uri="..."> for cell deeplinks.
 *   Embeds <pyana-capability uri="..."> for individual capability rows.
 *   Embeds <pyana-receipt uri="..."> for receipt chain head.
 *   Does NOT reimplement their logic here.
 *
 * CSS: injected once into document head under id="pyana-cipherclerk-styles".
 * Uses only site-palette tokens (--bg, --bg-raised, --fg, --fg-dim, --accent,
 * --accent-bright, --line, --sN). No fresh color literals.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Styles
// ---------------------------------------------------------------------------

(function injectStyles() {
  if (document.getElementById('pyana-cipherclerk-styles')) return;
  const s = document.createElement('style');
  s.id = 'pyana-cipherclerk-styles';
  s.textContent = `
/* ---- <pyana-cipherclerk> ---- */
.pcc {
  font-family: var(--font-mono, ui-monospace, monospace);
  font-size: 0.85rem;
  color: var(--fg);
}
.pcc--compact {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding: 2px 10px;
  background: var(--bg-raised);
  border: 1px solid var(--line);
  border-radius: 4px;
  font-size: 0.82rem;
}
.pcc__header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: var(--s2, 6px) var(--s3, 10px);
  border-bottom: 1px solid var(--line);
  background: var(--bg-raised);
}
.pcc__name {
  font-size: 0.9rem;
  font-weight: 600;
  color: var(--fg);
}
.pcc__badge {
  padding: 1px 7px;
  background: color-mix(in srgb, var(--accent, #5b8a5a) 28%, var(--bg-raised));
  color: var(--accent-bright, #7db87b);
  border: 1px solid color-mix(in srgb, var(--accent, #5b8a5a) 50%, transparent);
  border-radius: 3px;
  font-size: 0.68rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.06em;
}
.pcc__idx {
  color: var(--fg-dim);
  font-size: 0.75rem;
}
.pcc__kv {
  display: grid;
  grid-template-columns: max-content 1fr;
  column-gap: var(--s4, 16px);
  row-gap: 4px;
  padding: var(--s3, 10px);
  margin: 0;
  font-size: 0.82rem;
  border-bottom: 1px solid var(--line);
}
.pcc__kv dt {
  color: var(--fg-dim);
  font-weight: normal;
  text-transform: uppercase;
  font-size: 0.72rem;
  letter-spacing: 0.05em;
  padding-top: 2px;
}
.pcc__kv dd {
  margin: 0;
  color: var(--fg);
  word-break: break-all;
  display: flex;
  align-items: center;
  gap: 6px;
  flex-wrap: wrap;
}
.pcc__kv dd code {
  font: inherit;
  color: var(--fg);
  cursor: default;
}
.pcc__deeplink {
  display: inline-flex;
  align-items: center;
  gap: 3px;
  padding: 1px 6px;
  background: color-mix(in srgb, var(--accent, #5b8a5a) 15%, var(--bg-raised));
  border: 1px solid color-mix(in srgb, var(--accent, #5b8a5a) 40%, transparent);
  border-radius: 3px;
  font-size: 0.72rem;
  color: var(--accent-bright, #7db87b);
  cursor: pointer;
  text-decoration: none;
  font-family: inherit;
}
.pcc__deeplink:hover {
  background: color-mix(in srgb, var(--accent, #5b8a5a) 28%, var(--bg-raised));
}
/* tab bar */
.pcc__tabs {
  display: flex;
  gap: 0;
  border-bottom: 1px solid var(--line);
  background: var(--bg-raised);
  padding: 0 var(--s3, 10px);
  overflow-x: auto;
}
.pcc__tab {
  padding: 6px 14px;
  font: inherit;
  font-size: 0.78rem;
  font-family: var(--font-mono, ui-monospace, monospace);
  background: none;
  border: none;
  border-bottom: 2px solid transparent;
  color: var(--fg-dim);
  cursor: pointer;
  white-space: nowrap;
  margin-bottom: -1px;
}
.pcc__tab:hover { color: var(--fg); }
.pcc__tab--active {
  color: var(--fg);
  border-bottom-color: var(--accent, #5b8a5a);
}
.pcc__tab-panel {
  padding: var(--s3, 10px);
  display: flex;
  flex-direction: column;
  gap: var(--s3, 10px);
}
/* section headings inside tab panels */
.pcc__section-label {
  font-size: 0.7rem;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  color: var(--fg-dim);
  margin-bottom: 4px;
}
/* key row in Identity tab */
.pcc__key-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 0;
  border-bottom: 1px solid var(--line);
}
.pcc__key-label {
  min-width: 110px;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  color: var(--fg-dim);
}
.pcc__key-value {
  flex: 1;
  word-break: break-all;
  font-size: 0.80rem;
  color: var(--fg);
  cursor: default;
}
.pcc__key-value--expandable {
  cursor: pointer;
}
.pcc__key-value--expandable:hover { color: var(--accent-bright, #7db87b); }
/* token rows in Holdings tab */
.pcc__token-list {
  list-style: none;
  padding: 0;
  margin: 0;
  display: flex;
  flex-direction: column;
  gap: 3px;
}
.pcc__token-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 6px;
  background: var(--bg-raised);
  border: 1px solid var(--line);
  border-radius: 3px;
  font-size: 0.80rem;
}
.pcc__token-id {
  flex: 1;
  font-size: 0.78rem;
  color: var(--fg-dim);
  word-break: break-all;
}
.pcc__token-label {
  font-weight: 600;
  color: var(--fg);
  min-width: 60px;
  font-size: 0.78rem;
}
.pcc__token-resource {
  font-size: 0.75rem;
  color: var(--fg-dim);
  padding: 1px 5px;
  background: color-mix(in srgb, var(--fg-dim) 12%, var(--bg-raised));
  border: 1px solid var(--line);
  border-radius: 2px;
}
.pcc__token-expiry {
  font-size: 0.72rem;
  color: var(--fg-dim);
}
.pcc__todo {
  font-size: 0.78rem;
  color: var(--fg-dim);
  font-style: italic;
  padding: 4px 0;
  border-left: 2px solid var(--line);
  padding-left: 8px;
}
/* receipt chain item in History tab */
.pcc__chain-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 0;
}
.pcc__chain-idx {
  font-size: 0.72rem;
  color: var(--fg-dim);
  min-width: 2em;
  text-align: right;
}
/* empty / error states */
.pcc__empty {
  font-size: 0.80rem;
  color: var(--fg-dim);
  font-style: italic;
  padding: var(--s3, 10px) 0;
}
`;
  document.head.appendChild(s);
})();

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function _esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * Read agent identity from the capability tree (name, cell_id, public_key).
 * Returns null if agent_index is out of range.
 */
function _agentIdentityFromTree(capTree, agentIdx) {
  if (!capTree) return null;
  return {
    agent_name: capTree.agent_name || `agent #${agentIdx}`,
    cell_id: capTree.cell_id || null,
  };
}

// ---------------------------------------------------------------------------
// <pyana-cipherclerk>
// ---------------------------------------------------------------------------

class PyanaCipherclerk extends InspectorBase {
  // Track which tab is active; not a signal — component re-renders on click.
  _activeTab = 'identity';

  static get observedAttributes() { return ['uri', 'mode']; }

  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'cipherclerk')) return;

    const agentIdx = Number(parsed.id);
    if (!Number.isFinite(agentIdx) || agentIdx < 0) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">cipherclerk URI: agent_index must be a non-negative integer, got: ${_esc(parsed.id)}</div>`;
      return;
    }

    // --- Signals ---
    // We derive three separate signals rather than one composite so that
    // different tabs can read independently (avoids one large computed doing
    // everything).
    const capTreeSig = this._runtime.listCapabilities(agentIdx);
    const receiptsSig = this._runtime.listReceipts(agentIdx);
    // The runtime has no first-class getAgentTokens(); we surface what we can
    // via the capability tree. Macaroon-backed HeldToken from cclerk.tokens()
    // is not yet a wasm export — noted as TODO below.

    // Active tab stored as a Preact signal so tab clicks trigger re-render.
    const activeTab = signal(this._activeTab);

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const capTree = capTreeSig.value;
      const receipts = receiptsSig.value || [];

      // Derive counts.
      const caps = capTree ? (capTree.capabilities || []) : null;
      const capsCount = caps ? caps.length : null;
      const receiptCount = receipts.length;

      // --- compact mode --------------------------------------------------
      if (mode === 'compact') {
        const name = capTree ? (capTree.agent_name || `#${agentIdx}`) : `#${agentIdx}`;
        const tokPart = '? tokens'; // TODO: token count not yet exported
        const capPart = capsCount != null ? `${capsCount} cap${capsCount === 1 ? '' : 's'}` : '? caps';
        const rcptPart = `${receiptCount} receipt${receiptCount === 1 ? '' : 's'}`;
        return html`
          <span class="pcc pcc--compact" data-testid="pcc-compact">
            <span class="pcc__name">${_esc(name)}</span>
            ·
            <span class="pcc__idx">#${agentIdx}</span>
            ·
            <span>${_esc(tokPart)}</span>
            ·
            <span>${_esc(capPart)}</span>
            ·
            <span>${_esc(rcptPart)}</span>
          </span>`;
      }

      // --- default mode --------------------------------------------------
      const agentName = capTree ? (capTree.agent_name || `agent #${agentIdx}`) : `agent #${agentIdx}`;
      const cellId = capTree ? capTree.cell_id : null;

      // Public key: the wasm `get_capability_tree` doesn't directly surface
      // the agent's Ed25519 public key; however `get_peer_pubkey` does (it's
      // the PeerExchange key which derives from the cclerk's signing key).
      // We use the _wasm escape hatch exactly as turn-debugger.js does.
      let publicKey = null;
      try {
        const wasm = this._runtime._wasm;
        const handle = this._runtime._handle;
        if (wasm && handle != null) {
          const pkView = wasm.get_peer_pubkey(handle, agentIdx);
          if (pkView && pkView.public_key) publicKey = pkView.public_key;
        }
      } catch { /* not fatal — display as unavailable */ }

      // Stealth meta-address: not yet a wasm export from cclerk.
      // Display a placeholder per the Substrate rule.
      const stealthMetaAddress = null; // TODO: expose via wasm binding

      // KV grid summary row —————————————————————————————————————————————————
      const kvGrid = html`
        <dl class="pcc__kv" data-testid="pcc-kv">
          <dt>public key</dt>
          <dd>
            ${publicKey
              ? html`<code title=${publicKey} class="pcc__key-value pcc__key-value--expandable"
                  onClick=${(e) => { e.target.textContent = e.target.getAttribute('title'); e.target.classList.remove('pcc__key-value--expandable'); }}
                >${_esc(shortHex(publicKey, 24))}</code>`
              : html`<span style="color:var(--fg-dim);font-style:italic;font-size:0.78rem;">unavailable</span>`}
          </dd>
          <dt>cell id</dt>
          <dd>
            ${cellId
              ? html`
                  <code title=${cellId}>${_esc(shortHex(cellId, 24))}</code>
                  <pyana-cell uri=${`pyana://cell/${cellId}`} mode="compact" data-testid="pcc-cell-deeplink"></pyana-cell>`
              : html`<span style="color:var(--fg-dim);">—</span>`}
          </dd>
          <dt>token count</dt>
          <dd>
            <span style="color:var(--fg-dim);font-style:italic;font-size:0.78rem;">TODO: tokens listing not yet exposed via wasm</span>
          </dd>
          <dt>capabilities</dt>
          <dd>${capsCount != null ? String(capsCount) : '—'}</dd>
          <dt>receipt chain</dt>
          <dd>${String(receiptCount)}</dd>
          ${stealthMetaAddress
            ? html`<dt>stealth meta</dt><dd><code title=${stealthMetaAddress}>${_esc(shortHex(stealthMetaAddress, 24))}</code></dd>`
            : null}
        </dl>`;

      // ── Tab bar ──────────────────────────────────────────────────────────
      const TABS = [
        { id: 'identity', label: 'Identity' },
        { id: 'holdings', label: 'Holdings' },
        { id: 'history',  label: 'History' },
        { id: 'stealth',  label: 'Stealth' },
      ];
      const tab = activeTab.value;
      const tabBar = html`
        <div class="pcc__tabs" role="tablist" data-testid="pcc-tabs">
          ${TABS.map(t => html`
            <button
              role="tab"
              class=${`pcc__tab${tab === t.id ? ' pcc__tab--active' : ''}`}
              aria-selected=${tab === t.id}
              data-testid=${`pcc-tab-${t.id}`}
              onClick=${() => { activeTab.value = t.id; }}
            >${t.label}</button>
          `)}
        </div>`;

      // ── Tab: Identity ────────────────────────────────────────────────────
      const tabIdentity = html`
        <div class="pcc__tab-panel" role="tabpanel" data-testid="pcc-panel-identity">
          <div class="pcc__section-label">Signing Keys</div>
          <div class="pcc__key-row">
            <span class="pcc__key-label">Ed25519 pubkey</span>
            ${publicKey
              ? html`<code
                  class="pcc__key-value pcc__key-value--expandable"
                  title=${publicKey}
                  onClick=${(e) => {
                    e.target.textContent = e.target.getAttribute('title');
                    e.target.classList.remove('pcc__key-value--expandable');
                  }}
                >${_esc(shortHex(publicKey, 32))}</code>`
              : html`<span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">unavailable (get_peer_pubkey not reachable)</span>`}
          </div>
          <div class="pcc__key-row">
            <span class="pcc__key-label">Private key</span>
            <span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">never surfaced</span>
          </div>
          <div style="margin-top:var(--s3,10px);">
            <div class="pcc__section-label">HD Derivation</div>
            <div class="pcc__key-row">
              <span class="pcc__key-label">Derivation path</span>
              <span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">
                awaiting wasm32 support for HD path export
              </span>
            </div>
            <div class="pcc__key-row">
              <span class="pcc__key-label">HD seed</span>
              <span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">never surfaced</span>
            </div>
          </div>
          ${cellId ? html`
            <div style="margin-top:var(--s3,10px);">
              <div class="pcc__section-label">Sovereign Cell</div>
              <pyana-cell uri=${`pyana://cell/${cellId}`} mode="default"></pyana-cell>
            </div>` : null}
        </div>`;

      // ── Tab: Holdings ────────────────────────────────────────────────────
      // The wasm capability tree exposes HeldCapability (the intent-matcher
      // shape), not the macaroon-backed HeldToken from cclerk.tokens().
      // Both legitimately coexist (see wasm/src/runtime.rs SimAgent comment).
      // We surface what the tree gives us; a TODO note marks the gap.
      let holdingsContent;
      if (!capTree) {
        holdingsContent = html`<div class="pcc__empty">no capability tree available for agent #${agentIdx}</div>`;
      } else if (!caps || caps.length === 0) {
        holdingsContent = html`<div class="pcc__empty">no capabilities held</div>`;
      } else {
        holdingsContent = html`
          <ul class="pcc__token-list" data-testid="pcc-holdings-list">
            ${caps.map((c, i) => html`
              <li class="pcc__token-row" data-testid=${`pcc-cap-row-${i}`}>
                <span class="pcc__token-label">slot ${String(c.slot)}</span>
                <span class="pcc__token-resource">${_esc(c.permissions || '?')}</span>
                <span class="pcc__token-id" title=${c.target}>→ <code>${_esc(shortHex(c.target, 20))}</code></span>
                <pyana-capability uri=${`pyana://capability/${agentIdx}/${c.slot}`} mode="compact"></pyana-capability>
              </li>`
            )}
          </ul>`;
      }
      const tabHoldings = html`
        <div class="pcc__tab-panel" role="tabpanel" data-testid="pcc-panel-holdings">
          <div class="pcc__section-label">Capabilities (CDT)</div>
          ${holdingsContent}
          <div class="pcc__todo" data-testid="pcc-tokens-todo">
            TODO: macaroon-backed HeldToken list (cclerk.tokens()) is not yet exposed via a
            wasm binding. Once <code>get_agent_tokens(handle, agent_index)</code> lands in
            wasm/src/bindings.rs, this panel will show the full token chain per
            STARBRIDGE-PLAN § 4.5 (&lt;pyana-attenuated-token&gt;).
          </div>
        </div>`;

      // ── Tab: History ─────────────────────────────────────────────────────
      // The wasm runtime exposes one global receipt chain; per-agent filtering
      // is reserved for when get_receipts_for_agent() lands. We show the chain
      // head here as a deeplink and a receipt-list summary.
      let historyContent;
      if (receiptCount === 0) {
        historyContent = html`<div class="pcc__empty">no receipts yet (turn the agent to generate history)</div>`;
      } else {
        const head = receipts[receipts.length - 1];
        historyContent = html`
          <div>
            <div class="pcc__section-label">Chain head (most recent)</div>
            <pyana-receipt uri=${`pyana://receipt/${head.turn_hash}`} mode="default"></pyana-receipt>
          </div>
          <div>
            <div class="pcc__section-label">Full chain (${receiptCount} receipt${receiptCount === 1 ? '' : 's'}) — note: chain is currently global (per-agent filter awaiting wasm support)</div>
            <ul class="pcc__token-list" data-testid="pcc-history-list">
              ${receipts.slice().reverse().map((r, i) => html`
                <li class="pcc__chain-row" data-testid=${`pcc-receipt-row-${i}`}>
                  <span class="pcc__chain-idx">${String(receipts.length - i)}.</span>
                  <pyana-receipt uri=${`pyana://receipt/${r.turn_hash}`} mode="compact"></pyana-receipt>
                </li>`
              )}
            </ul>
          </div>`;
      }
      const tabHistory = html`
        <div class="pcc__tab-panel" role="tabpanel" data-testid="pcc-panel-history">
          ${historyContent}
        </div>`;

      // ── Tab: Stealth ─────────────────────────────────────────────────────
      // Stealth keypair (view + spend) and stealth notes are not yet exposed
      // by the wasm runtime. Placeholder per the Substrate rule.
      const tabStealth = html`
        <div class="pcc__tab-panel" role="tabpanel" data-testid="pcc-panel-stealth">
          <div class="pcc__section-label">Stealth Keys</div>
          <div class="pcc__key-row">
            <span class="pcc__key-label">View pubkey</span>
            <span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">awaiting wasm32 support for stealth key export</span>
          </div>
          <div class="pcc__key-row">
            <span class="pcc__key-label">Spend pubkey</span>
            <span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">awaiting wasm32 support for stealth key export</span>
          </div>
          <div class="pcc__key-row">
            <span class="pcc__key-label">Meta-address</span>
            ${stealthMetaAddress
              ? html`<code class="pcc__key-value" title=${stealthMetaAddress}>${_esc(shortHex(stealthMetaAddress, 32))}</code>`
              : html`<span class="pcc__key-value" style="color:var(--fg-dim);font-style:italic;">awaiting wasm32 support</span>`}
          </div>
          <div style="margin-top:var(--s3,10px);">
            <div class="pcc__section-label">Recent Stealth Notes Received</div>
            <div class="pcc__todo" data-testid="pcc-stealth-notes-todo">
              TODO: stealth notes require <code>get_stealth_notes(handle, agent_index)</code>
              wasm binding. See STARBRIDGE-PLAN § 4.3 (extension bugfix #1: wire
              note_announcement WS handler to call check_stealth_ownership).
            </div>
          </div>
        </div>`;

      // ── Active panel dispatch ─────────────────────────────────────────────
      const panels = {
        identity: tabIdentity,
        holdings: tabHoldings,
        history:  tabHistory,
        stealth:  tabStealth,
      };

      return html`
        <div class="pcc pyana-inspector pyana-inspector--cell" data-testid="pcc-root">
          <div class="pcc__header">
            <span class="pcc__name" data-testid="pcc-agent-name">${_esc(agentName)}</span>
            <span class="pcc__badge">cipherclerk</span>
            <span class="pcc__idx">#${agentIdx}</span>
          </div>
          ${kvGrid}
          ${tabBar}
          ${panels[tab]}
        </div>`;
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('pyana-cipherclerk')) {
  customElements.define('pyana-cipherclerk', PyanaCipherclerk);
}
