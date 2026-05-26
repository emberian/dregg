/**
 * <dregg-predicate> — Studio inspector for dregg-dsl / Datalog policy evaluation.
 *
 * Two modes:
 *   Read mode  — attribute uri="dregg://predicate/<hash>" or data-predicate='{"facts":[],"rules":[]}'
 *                Renders stored predicate (facts + built-in rules) view-only.
 *   Editor mode — attribute mode="editor"
 *                 Two textareas (facts JSON, request JSON), evaluate button,
 *                 live derivation trace pane.
 *
 * Compact mode: shows "N facts · M rules · ALLOW/DENY" summary inline.
 *
 * wasm binding: evaluate_datalog(facts_json, request_json) returns
 *   { conclusion: "allow"|"deny", policy_rule_id: number|null,
 *     num_derivation_steps: number, steps: StepInfo[] }
 * where StepInfo = { rule_id, derived_predicate_hex, num_bindings }
 *
 * The evaluate call is on the wasm module directly (not via runtime signal)
 * because policy evaluation is stateless — no cell handle needed.
 * Access via runtime._wasm (the documented escape hatch in runtime-in-memory.js).
 *
 * Integration points for other inspectors:
 *   - <dregg-capability> caveat display: embed in editor mode with data-predicate
 *     containing the token's restriction facts + a read-only request field for
 *     the target invocation.
 *   - <dregg-cell-program> Witnessed constraint display: a StateConstraintView with
 *     kind="Witnessed" and predicate_kind="Custom"|"Dfa" can inline a
 *     <dregg-predicate> in read mode to show the embedded policy.
 */

import { InspectorBase, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Default facts / request used in editor mode.
// The standard_policy() in the wasm crate uses the "secure" per-action fact
// format: action_allowed(app_id, action) — one fact per allowed action per app.
// (The legacy comma-separated format used in playground/sections/datalog.js is
// deprecated; standard_policy() uses MemberOf instead of Contains.)
// ---------------------------------------------------------------------------

const DEFAULT_FACTS = [
  { predicate: 'action_allowed', terms: ['my-app', 'read'] },
  { predicate: 'action_allowed', terms: ['my-app', 'write'] },
  { predicate: 'svc_action_allowed', terms: ['dns', 'read'] },
];

const DEFAULT_REQUEST = {
  app_id: 'my-app',
  action: 'read',
  now: 0,
};

// ---------------------------------------------------------------------------
// STANDARD_RULES: human-readable descriptions of dregg's built-in Datalog rules.
// These mirror the rule_ids in dregg-trace/src/policy.rs standard_policy().
// Shown read-only; the actual rules are compiled into the wasm crate.
// ---------------------------------------------------------------------------

const STANDARD_RULES = [
  { id: 40,   label: 'app_action_secure',     body: 'action_allowed(?app, ?act), request_app(?app), request_action(?act) ⇒ ALLOW' },
  { id: 41,   label: 'svc_action_secure',     body: 'svc_action_allowed(?svc, ?act), request_service(?svc), request_action(?act) ⇒ ALLOW' },
  { id: 3,    label: 'unrestricted',          body: 'unrestricted(1), request_action(?act) ⇒ ALLOW' },
  { id: 10,   label: 'app_action_time_bounded', body: 'action_allowed(?app,?act), request_app(?app), request_action(?act), valid_until(?exp), request_time(?t), ?t<?exp ⇒ ALLOW' },
  { id: 20,   label: 'budget_ok',             body: 'budget_remaining(?b, ?r), request_cost(?c), ?r≥?c ⇒ budget_ok(?b)' },
  { id: 21,   label: 'budget_deny',           body: 'budget_remaining(?b, ?r), request_cost(?c), ?c>?r ⇒ DENY' },
  { id: 30,   label: 'revocation_ok',         body: 'not_revoked(?t) ⇒ not_revoked_ok(?t)' },
  { id: 31,   label: 'revocation_deny',       body: 'revocable(?t), revoked(?t) ⇒ DENY' },
  { id: 50,   label: 'not_before_deny',       body: 'valid_after(?start), request_time(?t), ?t<?start ⇒ DENY' },
  { id: null, label: 'default',               body: 'DENY' },
];

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

/** Find the rule label for a given rule_id (or null for default deny). */
function _ruleLabel(id) {
  if (id == null) return 'default deny';
  const r = STANDARD_RULES.find(r => r.id === Number(id));
  return r ? r.label : `rule #${id}`;
}

// ---------------------------------------------------------------------------
// <dregg-predicate>
// ---------------------------------------------------------------------------

class DreggPredicate extends InspectorBase {
  static get observedAttributes() { return ['uri', 'mode', 'data-predicate']; }

  connectedCallback() {
    // Override: we need the runtime for wasm access, but also work standalone
    // (editor mode with no runtime — just a wasm global).
    super.connectedCallback().catch(() => {
      // No <dregg-app> ancestor in standalone use; render anyway with
      // direct wasm access from the Studio runtime API if available.
      this._runtime = null;
      this._api = window.dreggUi || null;
      this._render();
    });
  }

  _render() {
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    if (mode === 'editor') {
      this._renderEditor();
      return;
    }

    // Read / compact mode: resolve predicate data
    let predData = null;
    const dataAttr = this.getAttribute('data-predicate');
    if (dataAttr) {
      try { predData = JSON.parse(dataAttr); } catch { /* ignore */ }
    }

    const facts = predData?.facts || [];
    const lastResult = predData?.last_result || null;

    if (mode === 'compact') {
      this._renderCompact(facts, lastResult);
      return;
    }

    // Default read mode
    this._renderReadMode(facts, lastResult);
  }

  // ── Compact ─────────────────────────────────────────────────────────────

  _renderCompact(facts, lastResult) {
    const decisionHtml = lastResult
      ? `<span class="dregg-pred__decision dregg-pred__decision--${lastResult.conclusion}">${lastResult.conclusion.toUpperCase()}</span>`
      : '';
    // Count only named rules (exclude the null-id default-deny sentinel)
    const rulesCount = STANDARD_RULES.filter(r => r.id != null).length;
    this.innerHTML =
      `<span class="dregg-pred dregg-pred--compact">` +
        `<span class="dregg-pred__badge">Predicate</span>` +
        ` <span class="dregg-pred__summary">${facts.length} fact${facts.length === 1 ? '' : 's'} · ${rulesCount} rules` +
        (decisionHtml ? ` · ${decisionHtml}` : '') +
        `</span>` +
      `</span>`;
  }

  // ── Read mode ────────────────────────────────────────────────────────────

  _renderReadMode(facts, lastResult) {
    const root = document.createElement('div');
    root.className = 'dregg-pred dregg-pred--read';

    // Header
    const headerEl = document.createElement('div');
    headerEl.className = 'dregg-pred__header';
    headerEl.innerHTML =
      `<span class="dregg-pred__badge">Predicate (Datalog)</span>` +
      (lastResult
        ? ` <span class="dregg-pred__decision dregg-pred__decision--${_esc(lastResult.conclusion)}">${_esc(lastResult.conclusion.toUpperCase())}</span>`
        : '');
    root.appendChild(headerEl);

    // Facts section
    root.appendChild(this._buildFactsList(facts, false));

    // Rules section (read-only)
    root.appendChild(this._buildRulesPane(false));

    this.appendChild(root);
  }

  // ── Editor mode ──────────────────────────────────────────────────────────

  _renderEditor() {
    const root = document.createElement('div');
    root.className = 'dregg-pred dregg-pred--editor';

    // Header row with badge + decision badge (populated after evaluation)
    const headerEl = document.createElement('div');
    headerEl.className = 'dregg-pred__header';
    headerEl.innerHTML = `<span class="dregg-pred__badge">Predicate (Datalog)</span>`;
    root.appendChild(headerEl);

    // Two-column layout: left = facts + request + evaluate button; right = rules
    const cols = document.createElement('div');
    cols.className = 'dregg-pred__cols';
    root.appendChild(cols);

    // ── Left column ────────────────────────────────────────────────────────
    const left = document.createElement('div');
    left.className = 'dregg-pred__col dregg-pred__col--left';
    cols.appendChild(left);

    // Facts pane (structured list with add row + delete per row)
    const factsSection = document.createElement('div');
    factsSection.className = 'dregg-pred__section';
    factsSection.innerHTML =
      `<div class="dregg-pred__section-label">Facts` +
        `<button class="dregg-pred__add-btn" title="Add fact">+ Add</button>` +
      `</div>`;
    const factsList = document.createElement('ul');
    factsList.className = 'dregg-pred__facts-list';
    factsSection.appendChild(factsList);
    left.appendChild(factsSection);

    // Keep a JS array of {predicate, terms[]} to manage state
    let factsData = DEFAULT_FACTS.map(f => ({ ...f, terms: [...f.terms] }));

    const renderFactsList = () => {
      factsList.innerHTML = '';
      factsData.forEach((fact, idx) => {
        const li = document.createElement('li');
        li.className = 'dregg-pred__fact-row';
        li.innerHTML =
          `<code class="dregg-pred__fact-pred">${_esc(fact.predicate)}</code>` +
          `<span class="dregg-pred__fact-terms">(${fact.terms.map(t => _esc(String(t))).join(', ')})</span>` +
          `<button class="dregg-pred__remove-btn" data-idx="${idx}" title="Remove fact">×</button>`;
        factsList.appendChild(li);
      });
    };
    renderFactsList();

    factsSection.querySelector('.dregg-pred__add-btn').addEventListener('click', () => {
      const pred = window.prompt('Predicate name:', 'my-fact');
      if (!pred) return;
      const termsStr = window.prompt('Terms (comma-separated):', 'value1, value2') || '';
      const terms = termsStr.split(',').map(t => t.trim()).filter(Boolean);
      factsData.push({ predicate: pred, terms });
      renderFactsList();
    });

    factsList.addEventListener('click', e => {
      const btn = e.target.closest('.dregg-pred__remove-btn');
      if (!btn) return;
      const idx = Number(btn.dataset.idx);
      factsData.splice(idx, 1);
      renderFactsList();
    });

    // Request pane
    const reqSection = document.createElement('div');
    reqSection.className = 'dregg-pred__section dregg-pred__section--request';
    reqSection.innerHTML = `<div class="dregg-pred__section-label">Request</div>`;

    const reqGrid = document.createElement('div');
    reqGrid.className = 'dregg-pred__req-grid';

    const appIdInput = _makeInput('app_id', DEFAULT_REQUEST.app_id, 'App ID');
    const actionInput = _makeInput('action', DEFAULT_REQUEST.action, 'Action');
    const serviceInput = _makeInput('service', '', 'Service (optional)');

    reqGrid.appendChild(appIdInput.container);
    reqGrid.appendChild(actionInput.container);
    reqGrid.appendChild(serviceInput.container);
    reqSection.appendChild(reqGrid);
    left.appendChild(reqSection);

    // Evaluate button + error display
    const evalRow = document.createElement('div');
    evalRow.className = 'dregg-pred__eval-row';
    const evalBtn = document.createElement('button');
    evalBtn.className = 'dregg-pred__eval-btn';
    evalBtn.textContent = 'Evaluate';
    const denyExampleBtn = document.createElement('button');
    denyExampleBtn.className = 'dregg-pred__deny-btn';
    denyExampleBtn.textContent = 'Try denied request';
    const errEl = document.createElement('div');
    errEl.className = 'dregg-pred__err';
    errEl.style.display = 'none';
    evalRow.appendChild(evalBtn);
    evalRow.appendChild(denyExampleBtn);
    evalRow.appendChild(errEl);
    left.appendChild(evalRow);

    // Trace pane (appears after evaluation)
    const traceSection = document.createElement('div');
    traceSection.className = 'dregg-pred__section dregg-pred__section--trace';
    traceSection.style.display = 'none';
    traceSection.innerHTML = `<div class="dregg-pred__section-label">Derivation Trace</div>`;
    const traceBody = document.createElement('div');
    traceBody.className = 'dregg-pred__trace-body';
    traceSection.appendChild(traceBody);
    left.appendChild(traceSection);

    // ── Right column ───────────────────────────────────────────────────────
    const right = document.createElement('div');
    right.className = 'dregg-pred__col dregg-pred__col--right';
    right.appendChild(this._buildRulesPane(false));
    cols.appendChild(right);

    // ── Evaluate logic ─────────────────────────────────────────────────────
    const getWasm = () => {
      if (this._runtime && this._runtime._wasm) return this._runtime._wasm;
      return null;
    };

    const showErr = (msg) => {
      errEl.textContent = msg;
      errEl.style.display = '';
    };
    const clearErr = () => { errEl.style.display = 'none'; };

    const doEvaluate = () => {
      clearErr();
      const wasm = getWasm();
      if (!wasm || typeof wasm.evaluate_datalog !== 'function') {
        showErr('wasm not available — load the Studio page with wasm enabled');
        return;
      }

      const request = {};
      const appIdVal = appIdInput.input.value.trim();
      const actionVal = actionInput.input.value.trim();
      const serviceVal = serviceInput.input.value.trim();
      if (appIdVal)   request.app_id  = appIdVal;
      if (actionVal)  request.action  = actionVal;
      if (serviceVal) request.service = serviceVal;
      request.now = Math.floor(Date.now() / 1000);

      const t0 = performance.now();
      let result;
      try {
        result = wasm.evaluate_datalog(
          JSON.stringify(factsData),
          JSON.stringify(request),
        );
      } catch (e) {
        showErr(`Evaluation error: ${e.message || String(e)}`);
        return;
      }
      const elapsedMs = (performance.now() - t0).toFixed(2);

      // Update decision badge in header
      const existing = headerEl.querySelector('.dregg-pred__decision');
      if (existing) existing.remove();
      const decBadge = document.createElement('span');
      const allow = result.conclusion === 'allow';
      decBadge.className = `dregg-pred__decision dregg-pred__decision--${result.conclusion}`;
      decBadge.textContent = result.conclusion.toUpperCase();
      headerEl.appendChild(decBadge);

      // Render trace
      traceSection.style.display = '';
      traceBody.innerHTML = '';

      // Summary row
      const summary = document.createElement('div');
      summary.className = 'dregg-pred__trace-summary';
      summary.innerHTML =
        `<span class="dregg-pred__trace-rule">${_esc(_ruleLabel(result.policy_rule_id))}</span>` +
        ` · ${result.num_derivation_steps} step${result.num_derivation_steps === 1 ? '' : 's'}` +
        ` · <span class="dregg-pred__trace-timing">${elapsedMs}ms</span>`;
      traceBody.appendChild(summary);

      if (result.steps && result.steps.length > 0) {
        result.steps.forEach((step, i) => {
          const stepEl = document.createElement('div');
          stepEl.className = 'dregg-pred__trace-step';
          // Indentation represents inference depth (using rule_id as a rough proxy;
          // deeper rules fire first in the bottom-up Datalog evaluation)
          const indent = Math.min(step.rule_id, 3);
          stepEl.style.paddingLeft = `${indent * 16}px`;
          stepEl.innerHTML =
            `<span class="dregg-pred__trace-step-num">${i + 1}</span>` +
            `<span class="dregg-pred__trace-step-rule">rule #${step.rule_id} · ${_esc(_ruleLabel(step.rule_id))}</span>` +
            `<code class="dregg-pred__trace-step-pred" title="${_esc(step.derived_predicate_hex)}">${_esc(shortHex(step.derived_predicate_hex, 16))}</code>` +
            `<span class="dregg-pred__trace-step-bindings">${step.num_bindings} binding${step.num_bindings === 1 ? '' : 's'}</span>`;
          traceBody.appendChild(stepEl);
        });
      } else {
        const empty = document.createElement('div');
        empty.className = 'dregg-pred__trace-empty';
        empty.textContent = allow
          ? 'Matched by unrestricted/default rule — no derivation steps.'
          : 'No rules fired — default DENY applied.';
        traceBody.appendChild(empty);
      }
    };

    evalBtn.addEventListener('click', doEvaluate);
    denyExampleBtn.addEventListener('click', () => {
      appIdInput.input.value = 'unknown-app';
      actionInput.input.value = 'delete';
      serviceInput.input.value = '';
    });

    this.appendChild(root);
  }

  // ── Shared: rules pane (read-only in all modes) ───────────────────────────

  _buildRulesPane(editable) {
    const section = document.createElement('div');
    section.className = 'dregg-pred__section dregg-pred__section--rules';
    section.innerHTML = `<div class="dregg-pred__section-label">Policy Rules <span class="dregg-pred__rules-note">(built-in, read-only)</span></div>`;
    const list = document.createElement('ul');
    list.className = 'dregg-pred__rules-list';
    for (const rule of STANDARD_RULES) {
      const li = document.createElement('li');
      li.className = 'dregg-pred__rule-row';
      li.innerHTML =
        `<span class="dregg-pred__rule-label${rule.id == null ? ' dregg-pred__rule-label--default' : ''}">${_esc(rule.label)}</span>` +
        `<code class="dregg-pred__rule-body">${_esc(rule.body)}</code>`;
      list.appendChild(li);
    }
    section.appendChild(list);
    return section;
  }

  // ── Shared: facts list (view-only in read mode) ───────────────────────────

  _buildFactsList(facts, editable) {
    const section = document.createElement('div');
    section.className = 'dregg-pred__section';
    section.innerHTML = `<div class="dregg-pred__section-label">Facts (${facts.length})</div>`;
    if (!facts.length) {
      const empty = document.createElement('div');
      empty.className = 'dregg-pred__facts-empty';
      empty.textContent = 'No facts defined.';
      section.appendChild(empty);
      return section;
    }
    const list = document.createElement('ul');
    list.className = 'dregg-pred__facts-list';
    facts.forEach(f => {
      const li = document.createElement('li');
      li.className = 'dregg-pred__fact-row';
      li.innerHTML =
        `<code class="dregg-pred__fact-pred">${_esc(f.predicate)}</code>` +
        `<span class="dregg-pred__fact-terms">(${(f.terms || []).map(t => _esc(String(t))).join(', ')})</span>`;
      list.appendChild(li);
    });
    section.appendChild(list);
    return section;
  }
}

if (!customElements.get('dregg-predicate')) {
  customElements.define('dregg-predicate', DreggPredicate);
}

// ---------------------------------------------------------------------------
// Utility: create a labeled input field
// ---------------------------------------------------------------------------

function _makeInput(name, defaultValue, label) {
  const container = document.createElement('div');
  container.className = 'dregg-pred__req-field';
  const lbl = document.createElement('label');
  lbl.textContent = label;
  const input = document.createElement('input');
  input.type = 'text';
  input.name = name;
  input.value = defaultValue;
  input.className = 'dregg-pred__req-input';
  container.appendChild(lbl);
  container.appendChild(input);
  return { container, input };
}

// ---------------------------------------------------------------------------
// Styles — injected once into document head.
// Uses only site-palette tokens. No Shadow DOM.
// ---------------------------------------------------------------------------

(function injectStyles() {
  if (document.getElementById('dregg-predicate-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-predicate-styles';
  s.textContent = `
/* ── <dregg-predicate> ─────────────────────────────────────────────────── */
.dregg-pred {
  font-family: var(--font-mono, ui-monospace, monospace);
  font-size: 0.85rem;
}

/* Compact */
.dregg-pred--compact {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding: 2px 10px;
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 4px;
  font-size: 0.82rem;
}
.dregg-pred__summary {
  color: var(--fg-dim, #8a948f);
}

/* Header */
.dregg-pred__header {
  display: flex;
  align-items: center;
  gap: 10px;
  margin-bottom: var(--s3, 10px);
  padding-bottom: var(--s2, 6px);
  border-bottom: 1px solid var(--line, #2a302d);
}
.dregg-pred__badge {
  padding: 2px 10px;
  background: color-mix(in srgb, #7090c0 70%, var(--bg, #0a0f0d));
  color: #fff;
  border-radius: 3px;
  font-size: 0.72rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.05em;
}

/* Decision badge */
.dregg-pred__decision {
  padding: 3px 14px;
  border-radius: 3px;
  font-size: 0.82rem;
  font-weight: 700;
  letter-spacing: 0.08em;
}
.dregg-pred__decision--allow {
  background: color-mix(in srgb, var(--accent, #5b8a5a) 70%, var(--bg, #0a0f0d));
  color: #0a0f0d;
}
.dregg-pred__decision--deny {
  background: color-mix(in srgb, #d4685c 70%, var(--bg, #0a0f0d));
  color: #fff;
}

/* Section headers */
.dregg-pred__section {
  margin-bottom: var(--s3, 10px);
}
.dregg-pred__section-label {
  font-size: 0.72rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  color: var(--fg-dim, #8a948f);
  margin-bottom: var(--s2, 6px);
  display: flex;
  align-items: center;
  gap: 8px;
}
.dregg-pred__rules-note {
  font-weight: 400;
  text-transform: none;
  font-size: 0.72rem;
  opacity: 0.7;
}

/* Facts list */
.dregg-pred__facts-list {
  list-style: none;
  padding: 0;
  margin: 0;
  display: flex;
  flex-direction: column;
  gap: 3px;
}
.dregg-pred__fact-row {
  display: flex;
  align-items: baseline;
  gap: 6px;
  padding: 3px 6px;
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 3px;
}
.dregg-pred__fact-pred {
  color: var(--accent-bright, #7db87b);
  font-size: 0.80rem;
  white-space: nowrap;
}
.dregg-pred__fact-terms {
  color: var(--fg-dim, #8a948f);
  font-size: 0.78rem;
  flex: 1;
  word-break: break-all;
}
.dregg-pred__remove-btn {
  background: none;
  border: none;
  color: var(--fg-dim, #8a948f);
  cursor: pointer;
  font-size: 1rem;
  line-height: 1;
  padding: 0 2px;
  opacity: 0.6;
}
.dregg-pred__remove-btn:hover { opacity: 1; color: #d4685c; }
.dregg-pred__add-btn {
  background: none;
  border: 1px solid var(--line, #2a302d);
  border-radius: 3px;
  color: var(--fg-dim, #8a948f);
  cursor: pointer;
  font-size: 0.72rem;
  padding: 1px 7px;
  font-family: inherit;
}
.dregg-pred__add-btn:hover { border-color: var(--accent, #5b8a5a); color: var(--accent-bright, #7db87b); }
.dregg-pred__facts-empty {
  color: var(--fg-dim, #8a948f);
  font-size: 0.82rem;
  font-style: italic;
}

/* Rules list */
.dregg-pred__rules-list {
  list-style: none;
  padding: 0;
  margin: 0;
  display: flex;
  flex-direction: column;
  gap: 4px;
}
.dregg-pred__rule-row {
  padding: 4px 8px;
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 3px;
  display: flex;
  flex-direction: column;
  gap: 2px;
}
.dregg-pred__rule-label {
  font-size: 0.75rem;
  font-weight: 600;
  color: color-mix(in srgb, #7090c0 80%, var(--fg, #e4ddd0));
}
.dregg-pred__rule-label--default {
  color: var(--fg-dim, #8a948f);
  font-weight: 400;
  font-style: italic;
}
.dregg-pred__rule-body {
  font-size: 0.72rem;
  color: var(--fg-dim, #8a948f);
  white-space: pre-wrap;
  word-break: break-all;
}

/* Request fields */
.dregg-pred__req-grid {
  display: flex;
  flex-direction: column;
  gap: var(--s2, 6px);
}
.dregg-pred__req-field {
  display: flex;
  flex-direction: column;
  gap: 2px;
}
.dregg-pred__req-field label {
  font-size: 0.72rem;
  color: var(--fg-dim, #8a948f);
  text-transform: uppercase;
  letter-spacing: 0.04em;
}
.dregg-pred__req-input {
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 4px;
  color: var(--fg, #e4ddd0);
  font-family: var(--font-mono, ui-monospace, monospace);
  font-size: 0.82rem;
  padding: 4px 8px;
  width: 100%;
  box-sizing: border-box;
}
.dregg-pred__req-input:focus {
  outline: none;
  border-color: var(--accent, #5b8a5a);
}

/* Evaluate row */
.dregg-pred__eval-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-top: var(--s3, 10px);
  flex-wrap: wrap;
}
.dregg-pred__eval-btn {
  background: var(--accent, #5b8a5a);
  border: none;
  border-radius: 4px;
  color: #0a0f0d;
  cursor: pointer;
  font-family: inherit;
  font-size: 0.85rem;
  font-weight: 600;
  padding: 6px 16px;
}
.dregg-pred__eval-btn:hover { filter: brightness(1.15); }
.dregg-pred__deny-btn {
  background: none;
  border: 1px solid var(--line, #2a302d);
  border-radius: 4px;
  color: var(--fg-dim, #8a948f);
  cursor: pointer;
  font-family: inherit;
  font-size: 0.82rem;
  padding: 5px 12px;
}
.dregg-pred__deny-btn:hover { border-color: #d4685c; color: #e08878; }
.dregg-pred__err {
  color: #d4685c;
  font-size: 0.82rem;
  border: 1px solid color-mix(in srgb, #d4685c 40%, var(--line));
  border-radius: 4px;
  padding: 4px 10px;
  flex: 1;
}

/* Trace pane */
.dregg-pred__section--trace {
  margin-top: var(--s3, 10px);
  padding: var(--s2, 6px) var(--s3, 10px);
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 4px;
}
.dregg-pred__trace-summary {
  font-size: 0.82rem;
  color: var(--fg-dim, #8a948f);
  margin-bottom: var(--s2, 6px);
  padding-bottom: var(--s2, 6px);
  border-bottom: 1px solid var(--line, #2a302d);
}
.dregg-pred__trace-rule {
  font-weight: 600;
  color: var(--fg, #e4ddd0);
}
.dregg-pred__trace-timing {
  font-size: 0.75rem;
  opacity: 0.7;
}
.dregg-pred__trace-step {
  display: flex;
  align-items: baseline;
  gap: 8px;
  padding: 2px 0;
  font-size: 0.78rem;
  border-bottom: 1px dotted color-mix(in srgb, var(--line, #2a302d) 50%, transparent);
}
.dregg-pred__trace-step:last-child { border-bottom: none; }
.dregg-pred__trace-step-num {
  color: var(--fg-dim, #8a948f);
  min-width: 1.4em;
  text-align: right;
  font-size: 0.72rem;
}
.dregg-pred__trace-step-rule {
  color: color-mix(in srgb, #7090c0 80%, var(--fg, #e4ddd0));
  flex: 1;
  white-space: nowrap;
}
.dregg-pred__trace-step-pred {
  color: var(--fg-dim, #8a948f);
  font-size: 0.72rem;
  white-space: nowrap;
}
.dregg-pred__trace-step-bindings {
  color: var(--fg-dim, #8a948f);
  font-size: 0.72rem;
  white-space: nowrap;
}
.dregg-pred__trace-empty {
  color: var(--fg-dim, #8a948f);
  font-size: 0.82rem;
  font-style: italic;
}

/* Editor two-column layout */
.dregg-pred--editor {
  padding: var(--s3, 10px);
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 6px;
}
.dregg-pred__cols {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: var(--s4, 16px);
}
@media (max-width: 640px) {
  .dregg-pred__cols { grid-template-columns: 1fr; }
}
.dregg-pred__col--left,
.dregg-pred__col--right {
  display: flex;
  flex-direction: column;
  gap: var(--s2, 6px);
}

/* Read mode */
.dregg-pred--read {
  padding: var(--s3, 10px);
  background: var(--bg-raised, #121b16);
  border: 1px solid var(--line, #2a302d);
  border-radius: 6px;
}
`;
  document.head.appendChild(s);
})();
