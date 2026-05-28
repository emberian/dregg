// starbridge-apps/shared/app-runtime-ready.js
//
// Per-page boot helper that makes a starbridge-app's core flow REAL in the
// local in-browser preview. It is loaded by each app's pages/index.html
// AFTER app-boot.js (which attaches window.__starbridgeAppRuntime and the
// read-only signTurn stub).
//
// Responsibilities:
//   1. Wait for app-boot to attach the real in-memory runtime.
//   2. Create a real cell for the app's placeholder registry URI and rewrite
//      the placeholder URI on every inspector element to the real hex id, so
//      reads + writes + enumeration all key off the same real cell.
//   3. Install the real window.dregg.signTurn (routes turns through the
//      runtime's canonical TurnExecutor) — unless the extension cclerk owns a
//      frozen window.dregg, in which case the extension wins.
//
// Owned by the starbridge-apps lane (does not touch app-boot.js).

import { ensureAppCell, installRealSignTurn } from './runtime-submit.js';

function waitForRuntime(timeoutMs = 20000) {
  return new Promise((resolve, reject) => {
    const start = Date.now();
    (function poll() {
      if (window.__starbridgeAppRuntime) return resolve(window.__starbridgeAppRuntime);
      if (Date.now() - start > timeoutMs) return reject(new Error('runtime not attached'));
      setTimeout(poll, 50);
    })();
  });
}

// Attributes on inspector elements that carry a placeholder cell URI we must
// rewrite to the real created cell id.
const URI_ATTRS = ['uri', 'registry-uri', 'issuer-uri', 'verifier-uri', 'credential-uri'];

function rewriteUris(realCellUri, placeholder) {
  const sel = '[uri],[registry-uri],[issuer-uri],[verifier-uri],[credential-uri]';
  for (const el of document.querySelectorAll(sel)) {
    for (const attr of URI_ATTRS) {
      const v = el.getAttribute(attr);
      if (v && v === placeholder) el.setAttribute(attr, realCellUri);
    }
  }
}

/**
 * Boot the real preview runtime for an app.
 * @param {object} opts
 * @param {string} opts.placeholderUri - the placeholder cell URI in the page
 *   (e.g. 'dregg://cell/registry-default'). Defaults to the registry-uri of
 *   the first <dregg-app>.
 */
export async function bootAppRuntime(opts = {}) {
  let placeholder = opts.placeholderUri;
  const appEl = document.querySelector('dregg-app');
  if (!placeholder && appEl) {
    placeholder = appEl.getAttribute('registry-uri') || appEl.getAttribute('uri') || '';
  }
  try {
    await waitForRuntime();
  } catch (e) {
    console.warn('[app-runtime-ready] runtime never attached:', e?.message || e);
    return { ok: false, error: String(e?.message || e) };
  }

  // Install the real signing path first so any inspector action that fires
  // before cell creation still routes correctly (it will lazily create).
  installRealSignTurn();

  if (!placeholder) {
    return { ok: true, cellUri: null, note: 'no placeholder URI to bind' };
  }

  let realCellId;
  try {
    realCellId = await ensureAppCell(placeholder);
  } catch (e) {
    console.warn('[app-runtime-ready] cell creation failed:', e?.message || e);
    return { ok: false, error: String(e?.message || e) };
  }
  const realCellUri = `dregg://cell/${realCellId}`;
  rewriteUris(realCellUri, placeholder);

  // Re-rewrite on DOM mutations (some inspectors render children that carry
  // the placeholder URI, e.g. the detail <dregg-name>).
  const obs = new MutationObserver(() => rewriteUris(realCellUri, placeholder));
  obs.observe(document.body, { childList: true, subtree: true, attributes: true,
    attributeFilter: URI_ATTRS });

  window.__starbridgeAppCellUri = realCellUri;
  document.dispatchEvent(new CustomEvent('starbridge-app:runtime-ready', {
    detail: { cellUri: realCellUri, placeholder },
  }));
  return { ok: true, cellUri: realCellUri };
}

// Auto-boot unless a page opts out by setting window.__starbridgeNoAutoBoot.
if (typeof window !== 'undefined' && !window.__starbridgeNoAutoBoot) {
  bootAppRuntime().catch((e) => console.warn('[app-runtime-ready] boot failed', e));
}
