// Nameservice — register/resolve/reverse with admin-auth prompt.

import { mountSection, randomBytes, hex, shortHex } from './_newworld.js';
import { renderNameserviceSvg } from '../visualizers/nameservice-registration.js';

const DEMO_ADMIN_TOKEN = 'em2_admin_demo_xyz';

export function initNameservice(_wasm) {
  mountSection('nameservice', (api) => {
    const { html, signal } = api;

    const names = signal([]);   // { name, serviceId, owner }
    const adminToken = signal('');
    const adminOk = signal(false);
    const newName = signal('alice.pyana');
    const resolveQuery = signal('alice.pyana');
    const reverseQuery = signal('');
    const log = signal([]);

    function pushLog(msg, kind = 'info') {
      log.value = [...log.value, { msg, kind }].slice(-30);
    }

    function unlockAdmin() {
      if (adminToken.value === DEMO_ADMIN_TOKEN) {
        adminOk.value = true;
        pushLog('admin token accepted; you can now register names.', 'ok');
      } else {
        adminOk.value = false;
        pushLog('admin token rejected.', 'err');
      }
    }

    function register() {
      if (!adminOk.value) { pushLog('register: admin auth required.', 'err'); return; }
      const exists = names.value.find(n => n.name === newName.value);
      if (exists) { pushLog(`register: "${newName.value}" already registered.`, 'err'); return; }
      const serviceId = hex(randomBytes(16));
      names.value = [...names.value, { name: newName.value, serviceId, owner: 'demo-user' }];
      pushLog(`registered ${newName.value} → ${shortHex(serviceId)}`, 'ok');
    }

    function resolve() {
      const hit = names.value.find(n => n.name === resolveQuery.value);
      if (hit) pushLog(`resolve: ${hit.name} → ${shortHex(hit.serviceId)}`, 'ok');
      else pushLog(`resolve: "${resolveQuery.value}" — not found.`, 'err');
    }

    function reverse() {
      const hit = names.value.find(n => n.serviceId.startsWith(reverseQuery.value));
      if (hit) pushLog(`reverse: ${shortHex(reverseQuery.value)} → ${hit.name}`, 'ok');
      else pushLog(`reverse: "${reverseQuery.value}" — not found.`, 'err');
    }

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Nameservice demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Nameservice</h3>
          <p class="vizzer__sub">${names.value.length} name(s) registered</p>
          <div class="vizzer__controls">
            ${adminOk.value
              ? html`<span class="chip" data-state="ok">admin: ok</span>`
              : html`<span class="chip" data-state="warn">admin: locked</span>`}
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          ${!adminOk.value ? html`
            <div class="pyana-card" data-tone="warm" style="padding:12px;">
              <p style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);">
                Registration is gated by an admin token. Demo token:
                <span class="hex">${DEMO_ADMIN_TOKEN}</span>
              </p>
              <div style="display:flex;gap:6px;margin-top:8px;">
                <input
                  style="flex:1;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:6px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;"
                  value=${adminToken.value}
                  onInput=${e => adminToken.value = e.target.value}
                  placeholder="paste admin token..." />
                <button class="inline" onClick=${unlockAdmin}>unlock</button>
              </div>
            </div>
          ` : null}

          <div class="grid-2">
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">register</h3>
              <div style="display:flex;gap:6px;">
                <input
                  style="flex:1;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:6px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;"
                  value=${newName.value}
                  onInput=${e => newName.value = e.target.value} />
                <button class="inline" onClick=${register} disabled=${!adminOk.value}>register</button>
              </div>
            </div>
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">resolve</h3>
              <div style="display:flex;gap:6px;">
                <input
                  style="flex:1;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:6px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;"
                  value=${resolveQuery.value}
                  onInput=${e => resolveQuery.value = e.target.value} />
                <button class="inline" onClick=${resolve}>resolve</button>
              </div>
            </div>
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">reverse (prefix lookup)</h3>
            <div style="display:flex;gap:6px;">
              <input
                style="flex:1;background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:6px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;"
                placeholder="service-id prefix..."
                value=${reverseQuery.value}
                onInput=${e => reverseQuery.value = e.target.value} />
              <button class="inline" onClick=${reverse}>reverse</button>
            </div>
          </div>

          ${renderNameserviceSvg(html, names.value)}

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${log.value.length === 0 ? html`<div style="color:var(--fg-muted);">no events.</div>` : null}
              ${log.value.slice().reverse().map((e, i) => html`<div key=${i} class="log__entry" data-kind=${e.kind}>${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Nameservice',
    lede: 'Map human-readable names to service ids; admin-gated registration prevents squatting. Resolve goes name → id; reverse goes id → name.',
    fallback: 'Interactive nameservice demo.',
  });
}
