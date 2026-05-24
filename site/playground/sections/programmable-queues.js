// Programmable Queues — define constraints, then try-enqueue candidates and
// watch the policy accept or reject each one.

import { mountSection, sha256, hex, shortHex } from './_newworld.js';
import { renderProgrammableQueueSvg } from '../visualizers/programmable-queue.js';

// A constraint has a `kind` + `param`. We support a small DSL:
//   - max-payload-bytes (n)
//   - require-tag (string)
//   - reject-substring (string)
//   - min-fee (n)
function evalConstraint(c, item) {
  switch (c.kind) {
    case 'max-payload-bytes': {
      const n = item.payload.length;
      if (n > c.param) return { ok: false, reason: `payload ${n}B > ${c.param}B` };
      return { ok: true };
    }
    case 'require-tag': {
      if ((item.tag || '') !== c.param) return { ok: false, reason: `tag ≠ "${c.param}"` };
      return { ok: true };
    }
    case 'reject-substring': {
      if (item.payload.includes(c.param)) return { ok: false, reason: `payload contains "${c.param}"` };
      return { ok: true };
    }
    case 'min-fee': {
      if ((item.fee | 0) < c.param) return { ok: false, reason: `fee ${item.fee} < ${c.param}` };
      return { ok: true };
    }
    default: return { ok: true };
  }
}

function describe(c) {
  switch (c.kind) {
    case 'max-payload-bytes': return `max payload = ${c.param} bytes`;
    case 'require-tag':       return `require tag = "${c.param}"`;
    case 'reject-substring':  return `reject if payload contains "${c.param}"`;
    case 'min-fee':           return `minimum fee = ${c.param}`;
    default:                  return c.kind;
  }
}

export function initProgrammableQueues(_wasm) {
  mountSection('programmable-queues', (api) => {
    const { html, signal } = api;

    const constraints = signal([
      { kind: 'max-payload-bytes', param: 64 },
      { kind: 'min-fee',          param: 1 },
    ]);
    const candidatePayload = signal('hello');
    const candidateTag = signal('order');
    const candidateFee = signal(2);
    const decisions = signal([]);     // { accept, label, reason }
    const vkHash = signal('');

    async function recomputeVk() {
      const enc = JSON.stringify(constraints.value);
      const h = await sha256(enc);
      vkHash.value = hex(h);
    }
    recomputeVk();

    function addConstraint(kind) {
      const defaults = {
        'max-payload-bytes': 128,
        'require-tag': 'order',
        'reject-substring': 'forbidden',
        'min-fee': 1,
      };
      constraints.value = [...constraints.value, { kind, param: defaults[kind] }];
      recomputeVk();
    }
    function removeConstraint(i) {
      constraints.value = constraints.value.filter((_, j) => j !== i);
      recomputeVk();
    }
    function updateParam(i, value) {
      constraints.value = constraints.value.map((c, j) =>
        j === i ? { ...c, param: c.kind === 'require-tag' || c.kind === 'reject-substring' ? value : (+value || 0) } : c);
      recomputeVk();
    }

    function tryEnqueue() {
      const item = {
        payload: candidatePayload.value,
        tag: candidateTag.value,
        fee: +candidateFee.value || 0,
      };
      let firstFailure = null;
      for (const c of constraints.value) {
        const res = evalConstraint(c, item);
        if (!res.ok) { firstFailure = { c, reason: res.reason }; break; }
      }
      const label = `${item.tag}/${item.payload.slice(0, 12)}`;
      decisions.value = [...decisions.value, firstFailure
        ? { accept: false, label, reason: firstFailure.reason }
        : { accept: true, label }
      ].slice(-40);
    }

    function clearTimeline() { decisions.value = []; }

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Programmable queue demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Programmable queue</h3>
          <p class="vizzer__sub">
            vk_hash:
            <span class="hex" title=${vkHash.value}>${shortHex(vkHash.value)}</span>
          </p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${clearTimeline}>clear timeline</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">constraints</h3>
            <div style="display:flex;flex-direction:column;gap:6px;">
              ${constraints.value.map((c, i) => html`
                <div key=${i} style="display:flex;gap:8px;align-items:center;font-family:var(--font-mono);font-size:11px;">
                  <span class="chip" data-state="ok">${i + 1}</span>
                  <span style="color:var(--fg-dim);min-width:160px;">${c.kind}</span>
                  <input
                    style="flex:1;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:4px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;"
                    value=${c.param}
                    onInput=${e => updateParam(i, e.target.value)} />
                  <button class="inline" data-tone="danger" onClick=${() => removeConstraint(i)}>remove</button>
                </div>
              `)}
            </div>
            <div style="display:flex;gap:6px;flex-wrap:wrap;margin-top:8px;">
              <button class="inline" onClick=${() => addConstraint('max-payload-bytes')}>+ max-payload-bytes</button>
              <button class="inline" onClick=${() => addConstraint('require-tag')}>+ require-tag</button>
              <button class="inline" onClick=${() => addConstraint('reject-substring')}>+ reject-substring</button>
              <button class="inline" onClick=${() => addConstraint('min-fee')}>+ min-fee</button>
            </div>
          </div>

          <div class="grid-2">
            <label class="field">payload
              <input value=${candidatePayload.value} onInput=${e => candidatePayload.value = e.target.value} />
            </label>
            <label class="field">tag
              <input value=${candidateTag.value} onInput=${e => candidateTag.value = e.target.value} />
            </label>
            <label class="field">fee
              <input type="number" value=${candidateFee.value} onInput=${e => candidateFee.value = e.target.value} />
            </label>
            <div style="display:flex;align-items:flex-end;">
              <button class="inline" onClick=${tryEnqueue}>try_enqueue</button>
            </div>
          </div>

          ${renderProgrammableQueueSvg(html,
            constraints.value.map(c => ({ label: describe(c) })),
            decisions.value)}

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">recent decisions</h3>
            <div class="log" role="log" aria-live="polite">
              ${decisions.value.slice().reverse().map((d, i) => html`
                <div key=${i} class="log__entry" data-kind=${d.accept ? 'ok' : 'err'}>
                  ${d.accept ? `ACCEPT  ${d.label}` : `REJECT  ${d.label} — ${d.reason}`}
                </div>
              `)}
              ${decisions.value.length === 0 ? html`<div style="color:var(--fg-muted);">no candidates yet.</div>` : null}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Programmable queues',
    lede: 'A queue is a policy program. Define constraints, then try-enqueue candidates and watch the policy accept or reject each one.',
    fallback: 'Interactive constraint-builder + try-enqueue demo.',
  });
}
