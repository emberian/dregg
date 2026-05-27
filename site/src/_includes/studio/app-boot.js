/**
 * starbridge-app boot layer.
 *
 * End-user app pages mount ordinary <dregg-app> elements, then this module
 * attaches the same Studio runtime context Starbridge uses. It also exposes a
 * small local-preview bridge on window.dregg when the Cipherclerk extension is
 * absent, without replacing the extension-owned API when it is present.
 */

import '/_includes/runtime-bootstrap.js';
import './context.js';
import './inspectors.js';
import { createInMemoryRuntime } from './runtime-in-memory.js';

function whenDreggUi() {
  return new Promise(resolve => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', e => resolve(e.detail), { once: true });
  });
}

function hexFromBytes(bytes) {
  return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
}

function installPreviewBridge(runtime, wasm) {
  window.__starbridgeAppRuntime = runtime;
  if (window.dregg && Object.isFrozen(window.dregg)) {
    return window.dregg;
  }
  const api = window.dregg || {};
  if (!window.dregg) window.dregg = api;

  try { api.__starbridgeRuntime = runtime; } catch {}

  if (!api.blockHeight) {
    api.blockHeight = async () => Number(runtime.cursor?.value || 0);
  }
  if (!api.readCell) {
    api.readCell = async (uri) => {
      const id = String(uri || '').replace(/^dregg:\/\/cell\//, '');
      return runtime.getCell(id).value;
    };
  }
  api.cell ||= {};
  if (!api.cell.readField) {
    api.cell.readField = async (cellIdOrUri, slot) => {
      const id = String(cellIdOrUri || '').replace(/^dregg:\/\/cell\//, '');
      const cell = runtime.getCell(id).value;
      const fields = cell?.fields || cell?.state_fields || cell?.slots || [];
      return fields[Number(slot)] ?? null;
    };
  }
  if (!api.blake3 && wasm?.blake3_hash) {
    api.blake3 = async (input) => {
      const text = input instanceof Uint8Array
        ? new TextDecoder().decode(input)
        : String(input ?? '');
      const hex = wasm.blake3_hash(text);
      const out = new Uint8Array(hex.length / 2);
      for (let i = 0; i < out.length; i += 1) out[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
      return out;
    };
  }
  if (!api.signTurn) {
    api.signTurn = async () => ({
      submitted: false,
      error: 'Cipherclerk extension signTurn is not available; local preview is read-only.',
    });
  }
  api.nameservice ||= {};
  if (!api.nameservice.listEntries) {
    api.nameservice.listEntries = async () => [];
  }

  return api;
}

function appIdFromPath(pathname = window.location.pathname) {
  const match = pathname.match(/\/starbridge-apps\/([^/]+)/);
  return match ? decodeURIComponent(match[1]) : '';
}

async function loadAppManifest() {
  const appId = appIdFromPath();
  if (!appId) return null;
  try {
    const resp = await fetch(`/starbridge-apps/${encodeURIComponent(appId)}/manifest.json`, {
      headers: { Accept: 'application/json' },
    });
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    return await resp.json();
  } catch (e) {
    console.warn(`[starbridge-app] manifest unavailable for ${appId}:`, e);
    return { id: appId, manifest_health: { status: 'unavailable', detail: String(e?.message || e) } };
  }
}

function postHostMessage(type, detail) {
  const message = { type, detail };
  if (detail && typeof detail === 'object') Object.assign(message, detail);
  if (!window.parent || window.parent === window) return;
  try {
    window.parent.postMessage(message, window.location.origin);
  } catch {
    window.parent.postMessage(message, '*');
  }
}

function installHostBridge(manifest, appEl, runtime) {
  const api = {
    manifest,
    appId: manifest?.id || appIdFromPath(),
    actions: Array.isArray(manifest?.host_actions) ? manifest.host_actions : [],
    inspectors: Array.isArray(manifest?.host_inspectors)
      ? manifest.host_inspectors
      : (manifest?.inspectors || []).map((name) => ({ id: name, label: name, tag: name })),
    controls: Array.isArray(manifest?.host_controls) ? manifest.host_controls : [],
    inspect(uri) {
      const target = uri || appEl?.getAttribute('registry-uri') || appEl?.getAttribute('uri') || '';
      postHostMessage('starbridge:inspect', { appId: this.appId, uri: target });
    },
    navigate(uri) {
      const target = uri || appEl?.getAttribute('registry-uri') || appEl?.getAttribute('uri') || '';
      postHostMessage('starbridge:navigate', { uri: target });
    },
    requestAction(actionId, payload = {}) {
      postHostMessage('starbridge:action', { appId: this.appId, actionId, payload });
    },
  };
  window.__starbridgeAppHost = api;
  postHostMessage('starbridge:app-ready', {
    appId: api.appId,
    manifest,
    actions: api.actions,
    inspectors: api.inspectors,
    controls: api.controls,
    registryUri: appEl?.getAttribute('registry-uri') || appEl?.getAttribute('uri') || '',
    runtime: runtime ? 'host-attached' : 'local-preview',
  });
  return api;
}

function installDevtoolsLink(appEl) {
  const params = new URLSearchParams(window.location.search);
  if (params.get('embedded') === '1') return;
  const uri = appEl.getAttribute('registry-uri') || appEl.getAttribute('uri') || '';
  const href = uri ? `/starbridge/?at=${encodeURIComponent(uri)}` : '/starbridge/';
  const link = document.createElement('a');
  link.className = 'starbridge-devtools-link';
  link.href = href;
  link.textContent = 'Open in Starbridge';
  link.setAttribute('aria-label', 'Open this app runtime in Starbridge');
  link.style.cssText = [
    'position:fixed',
    'right:16px',
    'bottom:16px',
    'z-index:50',
    'padding:7px 10px',
    'border:1px solid #888',
    'border-radius:4px',
    'background:#111',
    'color:#fff',
    'font:12px ui-monospace,monospace',
    'text-decoration:none',
  ].join(';');
  document.body.appendChild(link);
}

function installEmbeddedChromeReset() {
  document.documentElement.dataset.embedded = 'starbridge';
  if (document.getElementById('starbridge-embedded-reset')) return;
  const style = document.createElement('style');
  style.id = 'starbridge-embedded-reset';
  style.textContent = `
    html[data-embedded="starbridge"],
    html[data-embedded="starbridge"] body {
      margin: 0;
      min-height: 100%;
      max-width: none;
      background: transparent;
      color-scheme: light;
      overflow-x: hidden;
    }
    html[data-embedded="starbridge"] .starbridge-devtools-link,
    html[data-embedded="starbridge"] .site-header,
    html[data-embedded="starbridge"] .app-header,
    html[data-embedded="starbridge"] footer {
      display: none !important;
    }
    html[data-embedded="starbridge"] header {
      margin: 0;
      padding: 0.75rem 0.875rem;
      border-bottom: 1px solid #ddd;
      background: rgba(255, 255, 255, 0.72);
      position: sticky;
      top: 0;
      z-index: 1;
      backdrop-filter: blur(10px);
    }
    html[data-embedded="starbridge"] header h1 {
      margin: 0;
      font-size: 1.05rem;
    }
    html[data-embedded="starbridge"] header p {
      margin: 0.35rem 0 0;
      font-size: 0.82rem;
      line-height: 1.35;
    }
    html[data-embedded="starbridge"] main,
    html[data-embedded="starbridge"] dregg-app {
      display: block;
      min-height: 100%;
    }
    html[data-embedded="starbridge"] main {
      padding: 0.875rem;
    }
    html[data-embedded="starbridge"] section,
    html[data-embedded="starbridge"] aside,
    html[data-embedded="starbridge"] dregg-app > * {
      max-width: 100%;
      box-sizing: border-box;
    }
    html[data-embedded="starbridge"] pre,
    html[data-embedded="starbridge"] code {
      white-space: pre-wrap;
      overflow-wrap: anywhere;
    }
  `;
  document.head.appendChild(style);
}

async function boot() {
  const api = await whenDreggUi();
  const wasm = await import('/pkg/dregg_wasm.js');
  await wasm.default();
  const params = new URLSearchParams(window.location.search);
  const embedded = params.get('embedded') === '1';
  const manifest = await loadAppManifest();
  if (embedded) installEmbeddedChromeReset();
  let hostRuntime = null;
  if (embedded && window.parent && window.parent !== window) {
    try {
      hostRuntime = window.parent.__starbridge?.runtime || null;
    } catch {
      hostRuntime = null;
    }
  }

  const runtimes = new Map();
  const apps = Array.from(document.querySelectorAll('dregg-app'));
  for (const appEl of apps) {
    const runtimeKind = appEl.getAttribute('runtime') || 'in-memory';
    if (hostRuntime) {
      appEl.runtime = hostRuntime;
      runtimes.set(appEl, hostRuntime);
      installPreviewBridge(hostRuntime, wasm);
      continue;
    }
    if (runtimeKind !== 'in-memory') {
      console.warn(`[starbridge-app] runtime "${runtimeKind}" awaits app-boot support; using in-memory`);
    }
    const runtime = await createInMemoryRuntime({ wasm, signals: api });
    appEl.runtime = runtime;
    runtimes.set(appEl, runtime);
    installPreviewBridge(runtime, wasm);
  }

  const first = apps[0];
  if (first) installDevtoolsLink(first);
  if (first) installHostBridge(manifest, first, runtimes.get(first));

  window.__starbridgeApp = {
    apps,
    runtimes,
    wasm,
    hexFromBytes,
    manifest,
  };
}

boot().catch((e) => {
  console.error('[starbridge-app] boot failed', e);
});
