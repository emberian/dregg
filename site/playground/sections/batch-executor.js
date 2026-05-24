// Batch Executor — collect → execute → proof, with per-client failure modes.

import { mountSection, randomBytes, hex, shortHex } from './_newworld.js';
import { renderBatchExecutorSvg } from '../visualizers/batch-executor.js';

const STAGES = ['idle', 'collect', 'execute', 'proof', 'done'];

export function initBatchExecutor(_wasm) {
  mountSection('batch-executor', (api) => {
    const { html, signal } = api;

    const clients = signal([
      { id: 1, failAt: null },
      { id: 2, failAt: null },
      { id: 3, failAt: 'execute' },
      { id: 4, failAt: null },
    ]);
    const stage = signal('idle');
    const proofHash = signal('');
    const log = signal([]);
    const running = signal(false);

    function pushLog(msg, kind = 'info') {
      log.value = [...log.value, { msg, kind }].slice(-40);
    }

    async function run() {
      if (running.value) return;
      running.value = true;
      proofHash.value = '';
      for (const s of ['collect', 'execute', 'proof', 'done']) {
        stage.value = s;
        pushLog(`stage: ${s}`, 'info');
        const failed = clients.value.filter(c => c.failAt === s);
        for (const f of failed) {
          pushLog(`client ${f.id} failed at ${s}`, 'err');
        }
        if (s === 'proof') {
          proofHash.value = hex(randomBytes(32));
          pushLog(`proof committed: ${shortHex(proofHash.value)}`, 'ok');
        }
        await new Promise(r => setTimeout(r, 250));
      }
      running.value = false;
      const ok = clients.value.filter(c => !c.failAt).length;
      pushLog(`batch finalized: ${ok}/${clients.value.length} client(s) included`, 'ok');
    }

    function reset() {
      stage.value = 'idle';
      proofHash.value = '';
      pushLog('reset', 'info');
    }

    function setFailure(id, at) {
      clients.value = clients.value.map(c => c.id === id ? { ...c, failAt: at } : c);
    }

    function addClient() {
      const id = (clients.value[clients.value.length - 1]?.id || 0) + 1;
      clients.value = [...clients.value, { id, failAt: null }];
    }
    function removeClient(id) {
      clients.value = clients.value.filter(c => c.id !== id);
    }

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Batch executor demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Batch executor</h3>
          <p class="vizzer__sub">stage: <span class="chip" data-state="ok">${stage.value}</span>${proofHash.value ? html` · proof ${html`<span class="hex">${shortHex(proofHash.value)}</span>`}` : ''}</p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${run} disabled=${running.value}>run batch</button>
            <button class="inline" onClick=${reset}>reset</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          ${renderBatchExecutorSvg(html, clients.value, stage.value === 'idle' ? 'collect' : stage.value)}

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">clients</h3>
            <div style="display:flex;flex-direction:column;gap:6px;">
              ${clients.value.map(c => html`
                <div key=${c.id} style="display:flex;gap:8px;align-items:center;font-family:var(--font-mono);font-size:11px;">
                  <span class="chip">${c.id}</span>
                  <label style="color:var(--fg-dim);">
                    fail at:
                    <select value=${c.failAt || ''} onChange=${e => setFailure(c.id, e.target.value || null)}
                            style="margin-left:4px;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:2px 6px;border-radius:var(--r1);font-family:var(--font-mono);font-size:11px;">
                      <option value="">(succeeds)</option>
                      <option value="collect">collect</option>
                      <option value="execute">execute</option>
                      <option value="proof">proof</option>
                    </select>
                  </label>
                  <button class="inline" data-tone="danger" onClick=${() => removeClient(c.id)}>×</button>
                </div>
              `)}
            </div>
            <button class="inline" style="margin-top:6px;" onClick=${addClient}>+ client</button>
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${log.value.length === 0 ? html`<div style="color:var(--fg-muted);">no runs yet.</div>` : null}
              ${log.value.slice().reverse().map((e, i) => html`<div key=${i} class="log__entry" data-kind=${e.kind}>${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Batch executor',
    lede: 'Clients submit intents that are collected, executed, and committed under a single batch proof. Per-client failures get isolated; the rest of the batch still finalizes.',
    fallback: 'Interactive batch-executor demo with controllable per-client failure stages.',
  });
}
