// Datalog section — write policies, evaluate, derivation trace

import { state, notifyStateChange, navigateTo } from '../playground.js';
import { deepLinkBanner, inspectorEmbed } from '../studio-embed.js';

export function initDatalog(wasm) {
  const container = document.getElementById('section-datalog');
  // Tier 2 (STARBRIDGE-PLAN §4.9): the canonical policy surface is the platform
  // <dregg-predicate mode="editor"> inspector — it calls the real wasm
  // evaluate_datalog(facts, request) and renders the derivation trace. The
  // legacy split-pane below is preserved as the educational walkthrough.
  container.innerHTML = `
    <div class="section-header">
      <h2>Datalog Policy Engine</h2>
      ${deepLinkBanner(
        [{ label: '<dregg-predicate>', uri: 'dregg://predicate/demo' }],
        'real evaluate_datalog + derivation trace',
      )}
      <p>
        Authorization decisions are made by a Datalog evaluator. Facts describe the token's
        permissions, rules define the policy, and the evaluator produces a step-by-step derivation
        trace showing exactly why a request was allowed or denied. Deterministic, auditable, composable.
      </p>
      ${inspectorEmbed(
        `<dregg-predicate mode="editor"></dregg-predicate>`,
        'Canonical predicate evaluator (real wasm Datalog)',
      )}
      <span class="next-hint" data-next="notes">Next: private value transfer &#8594;</span>
    </div>

    <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 20px;">
      <div>
        <div class="control-group">
          <label>Policy Rules (read-only — these are dregg's standard rules)</label>
          <div style="background: var(--surface-2); border: 1px solid var(--border); border-radius: var(--radius); padding: 12px; font-family: var(--mono); font-size: 11px; color: var(--text-dim); line-height: 1.7; margin-top: 4px;">
<pre style="margin:0; font-size:inherit; background:none; border:none; padding:0; color:inherit;">rule allow_unrestricted:
  fact(unrestricted, "true") =>
    ALLOW

rule allow_app_action:
  fact(app, ?app_id, ?actions),
  request.app_id = ?app_id,
  request.action IN ?actions =>
    ALLOW

rule allow_service:
  fact(service, ?svc, ?actions),
  request.action IN ?actions =>
    ALLOW

default: DENY</pre>
          </div>
        </div>
      </div>
      <div>
        <div class="control-group">
          <label>Facts (JSON array)</label>
          <textarea id="dl-facts" rows="6" style="width: 100%;" spellcheck="false">[
  {"predicate": "app", "terms": ["my-app", "read,write"]},
  {"predicate": "service", "terms": ["dns", "read"]},
  {"predicate": "unrestricted", "terms": ["true"]}
]</textarea>
        </div>
        <div class="control-group" style="margin-top: 12px;">
          <label>Request (JSON)</label>
          <textarea id="dl-request" rows="4" style="width: 100%;" spellcheck="false">{
  "app_id": "my-app",
  "action": "read",
  "now": ${Math.floor(Date.now() / 1000)}
}</textarea>
        </div>
        <div style="margin-top: 12px;">
          <button class="btn btn-primary" id="dl-evaluate" ${wasm ? '' : 'disabled'}>Evaluate</button>
          <button class="btn btn-secondary" id="dl-deny-example" style="margin-left: 8px;">Try Denied Request</button>
        </div>
      </div>
    </div>

    <div id="dl-result"></div>
    <div id="dl-trace"></div>
    <div id="dl-explainer"></div>
  `;

  if (!wasm) return;

  const factsArea = container.querySelector('#dl-facts');
  const requestArea = container.querySelector('#dl-request');
  const resultDiv = container.querySelector('#dl-result');
  const traceDiv = container.querySelector('#dl-trace');
  const explainerDiv = container.querySelector('#dl-explainer');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('notes'));

  container.querySelector('#dl-deny-example').addEventListener('click', () => {
    requestArea.value = JSON.stringify({
      app_id: "unknown-app",
      action: "delete",
      now: Math.floor(Date.now() / 1000),
    }, null, 2);
  });

  container.querySelector('#dl-evaluate').addEventListener('click', () => {
    let facts, request;
    try {
      facts = JSON.parse(factsArea.value);
      request = JSON.parse(requestArea.value);
    } catch (e) {
      showResult(resultDiv, 'error', `JSON parse error: ${e.message}`);
      return;
    }

    const t0 = performance.now();
    try {
      const result = wasm.evaluate_datalog(JSON.stringify(facts), JSON.stringify(request));
      const elapsed = (performance.now() - t0).toFixed(2);

      // WASM returns: { conclusion: "allow"|"deny", policy_rule_id, num_derivation_steps, steps[] }
      const decision = result.conclusion;
      const ruleLabel = result.policy_rule_id != null
        ? `rule #${result.policy_rule_id}`
        : '(default deny)';
      const isAllowed = decision === 'allow';

      showResult(resultDiv, isAllowed ? 'success' : 'warning',
        `Decision: ${decision}\nMatched rule: ${ruleLabel}`);

      // Render derivation trace
      if (result.steps && result.steps.length > 0) {
        let traceHtml = `<div class="result-panel" style="margin-top: 12px;">
          <div class="result-panel__header">
            <span class="result-panel__title">Derivation Trace</span>
            <span class="result-panel__timing">${elapsed}ms</span>
          </div>
          <div class="result-panel__body">`;

        result.steps.forEach((step, i) => {
          traceHtml += `<div class="output-entry info" style="display:flex;gap:8px;">
            <span>&#10003;</span>
            <span>Step ${i + 1}: rule #${step.rule_id} derived ${step.num_bindings} binding(s) &rarr; <code>${escapeHtml(step.derived_predicate_hex.slice(0, 24))}...</code></span>
          </div>`;
        });

        traceHtml += '</div></div>';
        traceDiv.innerHTML = traceHtml;
      } else {
        traceDiv.innerHTML = '';
      }

      showExplainer(explainerDiv, {
        prover: `Token facts: ${facts.length} predicates\nRequest: app_id="${request.app_id}", action="${request.action}"\nFull fact set visible to evaluator`,
        verifier: `Decision: ${decision}\nMatched rule: ${ruleLabel}\nDerivation: ${result.num_derivation_steps} evaluation steps\nDeterministic: same facts + request always yields same decision`,
        delta: `The evaluator's trace is fully auditable. Unlike opaque access-control lists, Datalog shows exactly WHY a decision was made. This enables debugging, compliance, and formal verification of policies.`,
        timing: elapsed,
      });
    } catch (e) {
      showResult(resultDiv, 'error', `Evaluation failed: ${e.message}`);
      traceDiv.innerHTML = '';
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
          <div class="explainer__cell-label">Evaluator input</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Decision output</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Auditability</div>
          <div class="explainer__cell-content">${escapeHtml(delta)}</div>
        </div>
      </div>
      <div class="explainer__timing">Evaluated in <span>${timing}ms</span></div>
    </div>
  `;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
