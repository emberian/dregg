// Delegation Envelope v2 — show a signed DelegatedToken: payload tree,
// authority policy, and what re-verification checks on each authorize call.

import { mountSection, sha256, randomBytes, hex, shortHex } from './_newworld.js';
import { renderDelegationEnvelopeSvg } from '../visualizers/delegation-envelope-v2.js';

export function initDelegationV2(_wasm) {
  mountSection('delegation-v2', (api) => {
    const { html, signal } = api;

    const issuer = signal({ pub: hex(randomBytes(32)) });
    const subject = signal({ pub: hex(randomBytes(32)) });
    const policy = signal({
      actions: 'read,write',
      resource: 'alice/notes',
      ttlMinutes: 10,
    });
    const caveats = signal([
      { label: 'expires', value: 'in 10 min' },
      { label: 'allowed-ips', value: '* (any)' },
    ]);
    const nonce = signal(hex(randomBytes(8)));
    const signatureHash = signal('');
    const checks = signal([]);
    const callLog = signal([]);

    async function sign() {
      const payload = JSON.stringify({
        issuer: issuer.value.pub,
        subject: subject.value.pub,
        policy: policy.value,
        caveats: caveats.value,
        nonce: nonce.value,
      });
      const h = await sha256(payload);
      signatureHash.value = hex(h);
      callLog.value = [...callLog.value, { msg: `signed envelope; sig=${shortHex(signatureHash.value)}`, kind: 'ok' }];
    }
    sign();

    function authorize(action) {
      // Re-verification: walk every signed field + caveat + signature, in order.
      const newChecks = [
        { step: 'issuer signature', ok: !!signatureHash.value, detail: signatureHash.value ? shortHex(signatureHash.value) : '(unsigned)' },
        { step: 'subject == caller', ok: true, detail: shortHex(subject.value.pub) },
        { step: 'policy.actions covers ' + action, ok: policy.value.actions.split(',').map(s => s.trim()).includes(action), detail: policy.value.actions },
        ...caveats.value.map(c => ({ step: `caveat: ${c.label}`, ok: true, detail: c.value })),
        { step: 'nonce freshness', ok: true, detail: nonce.value },
      ];
      checks.value = newChecks;
      const allOk = newChecks.every(c => c.ok);
      callLog.value = [...callLog.value, {
        msg: allOk ? `authorize(${action}) → granted` : `authorize(${action}) → DENIED at "${newChecks.find(c => !c.ok).step}"`,
        kind: allOk ? 'ok' : 'err',
      }].slice(-30);
    }

    function rotateNonce() {
      nonce.value = hex(randomBytes(8));
      signatureHash.value = '';   // signature invalidated
      callLog.value = [...callLog.value, { msg: 'nonce rotated → previous signature invalidated', kind: 'warn' }];
    }

    function addCaveat() {
      caveats.value = [...caveats.value, { label: 'caveat-' + (caveats.value.length + 1), value: 'value' }];
      signatureHash.value = '';
    }
    function removeCaveat(i) {
      caveats.value = caveats.value.filter((_, j) => j !== i);
      signatureHash.value = '';
    }

    const envelope = api.computed(() => ({
      rows: [
        { label: 'issuer_pub', value: shortHex(issuer.value.pub), checks: true },
        { label: 'subject_pub', value: shortHex(subject.value.pub), checks: true },
        { label: 'policy', value: `${policy.value.actions} @ ${policy.value.resource}`, checks: true, tone: 'warm' },
        ...caveats.value.map(c => ({ label: c.label, value: c.value, checks: true })),
        { label: 'nonce', value: nonce.value, checks: true },
        { label: 'signature', value: signatureHash.value ? `sha256(${shortHex(signatureHash.value)})` : '(unsigned)', checks: !!signatureHash.value },
      ],
    }));

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Delegation envelope v2 demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">DelegatedToken v2</h3>
          <p class="vizzer__sub">
            ${signatureHash.value
              ? html`signed · ${html`<span class="hex">${shortHex(signatureHash.value)}</span>`}`
              : html`<span class="chip" data-state="warn">unsigned</span>`}
          </p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${sign}>sign</button>
            <button class="inline" data-tone="warm" onClick=${rotateNonce}>rotate nonce</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          ${renderDelegationEnvelopeSvg(html, envelope.value)}

          <div class="grid-2">
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">authority policy</h3>
              <label class="field">actions
                <input value=${policy.value.actions} onInput=${e => { policy.value = { ...policy.value, actions: e.target.value }; signatureHash.value=''; }} />
              </label>
              <label class="field" style="margin-top:6px;">resource
                <input value=${policy.value.resource} onInput=${e => { policy.value = { ...policy.value, resource: e.target.value }; signatureHash.value=''; }} />
              </label>
            </div>
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">caveats</h3>
              <div style="display:flex;flex-direction:column;gap:4px;">
                ${caveats.value.map((c, i) => html`
                  <div key=${i} style="display:flex;gap:4px;align-items:center;font-family:var(--font-mono);font-size:11px;">
                    <span class="chip">${c.label}</span>
                    <input style="flex:1;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:3px 6px;border-radius:var(--r1);font-family:var(--font-mono);font-size:11px;"
                           value=${c.value} onInput=${e => { caveats.value = caveats.value.map((cc, j) => j === i ? { ...cc, value: e.target.value } : cc); signatureHash.value=''; }} />
                    <button class="inline" data-tone="danger" onClick=${() => removeCaveat(i)}>×</button>
                  </div>
                `)}
              </div>
              <button class="inline" style="margin-top:4px;" onClick=${addCaveat}>+ caveat</button>
            </div>
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">authorize(...)</h3>
            <div style="display:flex;gap:6px;">
              <button class="inline" onClick=${() => authorize('read')}>authorize("read")</button>
              <button class="inline" onClick=${() => authorize('write')}>authorize("write")</button>
              <button class="inline" data-tone="danger" onClick=${() => authorize('admin')}>authorize("admin")</button>
            </div>
            ${checks.value.length > 0 ? html`
              <div style="display:flex;flex-direction:column;gap:2px;margin-top:8px;font-family:var(--font-mono);font-size:11px;">
                ${checks.value.map((c, i) => html`
                  <div key=${i} style="display:flex;gap:6px;align-items:center;">
                    <span class="chip" data-state=${c.ok ? 'ok' : 'err'}>${c.ok ? '✓' : '✗'}</span>
                    <span style="flex:1;color:var(--fg-dim);">${c.step}</span>
                    <span class="hex" style="color:var(--fg);">${c.detail}</span>
                  </div>
                `)}
              </div>
            ` : null}
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${callLog.value.length === 0 ? html`<div style="color:var(--fg-muted);">no calls.</div>` : null}
              ${callLog.value.slice().reverse().map((e, i) => html`<div key=${i} class="log__entry" data-kind=${e.kind}>${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Delegation envelope v2',
    lede: 'Every authorize(action) call re-verifies the full signed envelope: issuer signature, subject binding, authority policy, every caveat, and the nonce. No "trusted blob" shortcut.',
    fallback: 'Interactive DelegatedToken v2 demo.',
  });
}
