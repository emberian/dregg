// Blinded Queues — commit/reveal/consume with real BLAKE3 commitments via the
// pyana wasm pkg. Demonstrates nullifier-set semantics + double-consume reject.

import { mountSection, blake3CommitmentLike, randomBytes, hex, shortHex } from './_newworld.js';
import { renderBlindedQueueSvg } from '../visualizers/blinded-queue.js';

export function initBlindedQueues(wasm) {
  mountSection('blinded-queues', (api) => {
    const { html, signal, computed } = api;

    // Reactive state: commitments[], nullifiers Set, log[]
    const orderText = signal('order: BUY 100 ABC @ 0.5 XYZ');
    const commits = signal([]);          // { id, blob, secret, commitment, algo, consumed }
    const nullifiers = signal(new Set());
    const logEntries = signal([]);

    function pushLog(msg, kind = 'info') {
      logEntries.value = [...logEntries.value, { msg, kind, t: Date.now() }].slice(-30);
    }

    async function commit() {
      const blob = orderText.value;
      const secret = randomBytes(32);
      const c = await blake3CommitmentLike(wasm, blob, ':commit:', secret);
      const id = commits.value.length + 1;
      commits.value = [...commits.value, {
        id, blob, secret, commitment: c.hex, algo: c.algo, consumed: false,
      }];
      pushLog(`commit #${id} → ${shortHex(c.hex)} (${c.algo})`, 'ok');
    }

    async function consume(id) {
      const entry = commits.value.find(c => c.id === id);
      if (!entry) return;
      // Nullifier = BLAKE3(secret || "nullify"). Anyone with the secret can
      // compute it; once published it goes into the nullifier set.
      const n = await blake3CommitmentLike(wasm, entry.secret, ':nullify');
      if (nullifiers.value.has(n.hex)) {
        pushLog(`REJECTED consume #${id} — nullifier already seen (double-spend)`, 'err');
        return;
      }
      const next = new Set(nullifiers.value);
      next.add(n.hex);
      nullifiers.value = next;
      commits.value = commits.value.map(c => c.id === id ? { ...c, consumed: true, nullifier: n.hex } : c);
      pushLog(`consumed #${id} → nullifier ${shortHex(n.hex)}`, 'ok');
    }

    async function tryDoubleConsume(id) {
      // Manually replay the consume step to demonstrate rejection.
      const entry = commits.value.find(c => c.id === id);
      if (!entry || !entry.nullifier) return;
      if (nullifiers.value.has(entry.nullifier)) {
        pushLog(`REJECTED replay of #${id} — nullifier ${shortHex(entry.nullifier)} already published`, 'err');
      }
    }

    function reset() {
      commits.value = [];
      nullifiers.value = new Set();
      logEntries.value = [];
    }

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Blinded queue demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Blinded queue</h3>
          <p class="vizzer__sub">commit → consume → nullifier</p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${reset} aria-label="Reset queue state">reset</button>
          </div>
        </header>

        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">
          <label class="field">
            order payload
            <input value=${orderText.value} onInput=${e => orderText.value = e.target.value} />
          </label>
          <div style="display:flex;gap:8px;">
            <button class="inline" onClick=${commit}>commit</button>
            <span class="chip" data-state="ok">commits: ${commits.value.length}</span>
            <span class="chip" data-state="warn">nullifiers: ${nullifiers.value.size}</span>
          </div>

          ${renderBlindedQueueSvg(html, commits.value, nullifiers.value)}

          <table style="width:100%;font-family:var(--font-mono);font-size:11px;border-collapse:collapse;">
            <thead>
              <tr style="text-align:left;color:var(--fg-dim);border-bottom:1px solid var(--line);">
                <th style="padding:4px 8px;">#</th>
                <th style="padding:4px 8px;">commitment</th>
                <th style="padding:4px 8px;">algo</th>
                <th style="padding:4px 8px;">state</th>
                <th style="padding:4px 8px;">action</th>
              </tr>
            </thead>
            <tbody>
              ${commits.value.map(c => html`
                <tr key=${c.id} style="border-bottom:1px solid var(--line);">
                  <td style="padding:4px 8px;">${c.id}</td>
                  <td style="padding:4px 8px;"><span class="hex" title=${c.commitment}>${shortHex(c.commitment)}</span></td>
                  <td style="padding:4px 8px;">${c.algo}</td>
                  <td style="padding:4px 8px;">
                    <span class="chip" data-state=${c.consumed ? 'warn' : 'ok'}>${c.consumed ? 'consumed' : 'open'}</span>
                  </td>
                  <td style="padding:4px 8px;">
                    ${c.consumed
                      ? html`<button class="inline" data-tone="danger" onClick=${() => tryDoubleConsume(c.id)}>try double-consume</button>`
                      : html`<button class="inline" onClick=${() => consume(c.id)}>consume</button>`}
                  </td>
                </tr>
              `)}
              ${commits.value.length === 0 ? html`
                <tr><td colspan="5" class="pyana-empty" style="padding:16px;">no commits yet — make one above.</td></tr>
              ` : null}
            </tbody>
          </table>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;letter-spacing:0.04em;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${logEntries.value.length === 0
                ? html`<div style="color:var(--fg-muted);">no events yet.</div>`
                : logEntries.value.map(e => html`<div class="log__entry" data-kind=${e.kind}>${new Date(e.t).toLocaleTimeString()} — ${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Blinded queues',
    lede: 'Order commitments hide payload until the order-owner consumes them. Once a commitment is consumed, its nullifier is published — replays are rejected.',
    fallback: 'Interactive blinded-queue demo. Commit an order, consume it, and observe that re-consuming the same secret is rejected.',
  });
}
