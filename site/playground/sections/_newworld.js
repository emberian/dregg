// Shared helpers for the "new world" sections. All seven new sections wait
// for the runtime (Preact + signals + htm) to be ready before mounting; if
// the runtime fails to load, we leave a graceful fallback in the section
// container.

let readyPromise = null;

export function whenRuntime() {
  if (readyPromise) return readyPromise;
  readyPromise = new Promise(resolve => {
    if (window.dregg) return resolve(window.dregg);
    window.addEventListener('dregg:ready', e => resolve(e.detail), { once: true });
    // If after 4 seconds the runtime never fires, surface a noop so sections
    // at least render their fallback content.
    setTimeout(() => {
      if (!window.dregg) {
        console.warn('[dregg] runtime not ready after 4s — sections will use fallback content.');
        resolve(null);
      }
    }, 4000);
  });
  return readyPromise;
}

/**
 * Mount a Preact application into a section container.
 * @param {string} sectionId  The `#section-<id>` element id (without prefix).
 * @param {(api, container) => any} factory  Builds the root VNode.
 * @param {{title: string, lede: string, fallback?: string}} meta
 */
export async function mountSection(sectionId, factory, meta) {
  const root = document.getElementById(`section-${sectionId}`);
  if (!root) return;

  // Static (no-JS) fallback content goes in immediately so the section is
  // never blank.
  root.innerHTML = `
    <div class="pg-newworld">
      <div class="section-header">
        <h2>${meta.title}</h2>
        <p>${meta.lede}</p>
      </div>
      <div data-mount class="dregg-card" role="region" aria-label="${meta.title}">
        <p style="color: var(--fg-muted); font-size: var(--text-sm);">
          ${meta.fallback || 'Loading interactive demo…'}
        </p>
      </div>
    </div>
  `;

  const api = await whenRuntime();
  if (!api) {
    // Runtime failed; the fallback message stays in place.
    return;
  }

  const mountPoint = root.querySelector('[data-mount]');
  if (!mountPoint) return;

  try {
    const tree = factory(api, mountPoint);
    if (tree && typeof tree === 'object') {
      mountPoint.innerHTML = '';
      api.render(tree, mountPoint);
    }
  } catch (e) {
    console.error(`[dregg] section ${sectionId} mount failed`, e);
    mountPoint.innerHTML = `<p style="color: var(--danger); font-size: var(--text-sm);">
      Interactive demo failed to load: ${String(e.message || e)}
    </p>`;
  }
}

// ---- Crypto helpers shared across sections ----
//
// We prefer SubtleCrypto where available (built-in, no third-party JS) and
// fall back to a small JS implementation only for BLAKE3 commitments derived
// from the existing dregg wasm pkg.
const enc = new TextEncoder();
const dec = new TextDecoder();

export async function sha256(...parts) {
  const buf = concatBytes(parts.map(toBytes));
  const hashBuf = await crypto.subtle.digest('SHA-256', buf);
  return new Uint8Array(hashBuf);
}

export function toBytes(x) {
  if (x instanceof Uint8Array) return x;
  if (x instanceof ArrayBuffer) return new Uint8Array(x);
  if (typeof x === 'string') return enc.encode(x);
  if (Array.isArray(x)) return new Uint8Array(x);
  throw new Error('unsupported byte input');
}

export function concatBytes(arrays) {
  const total = arrays.reduce((n, a) => n + a.length, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const a of arrays) { out.set(a, off); off += a.length; }
  return out;
}

export function hex(bytes) {
  return Array.from(bytes, b => b.toString(16).padStart(2, '0')).join('');
}

export function shortHex(s, n = 7) {
  if (!s) return '--';
  return s.length <= n * 2 + 3 ? s : `${s.slice(0, n)}…${s.slice(-n)}`;
}

export function randomBytes(n) {
  const out = new Uint8Array(n);
  crypto.getRandomValues(out);
  return out;
}

/** BLAKE3-compatible commitment via the dregg wasm pkg `compute_merkle_root`.
 *  Dragon's Egg's storage layer uses 4-ary BLAKE3 merkle commitments; a single-leaf
 *  root is exactly `BLAKE3(leaf || ":0")`. We don't need to round-trip the
 *  exact internal serialization to get a deterministic, BLAKE3-derived
 *  32-byte commitment for visualization purposes.
 *
 *  Falls back to SHA-256 if the wasm pkg isn't available (e.g. WASM load
 *  failed on the page); we tag the result so the UI can show which it used.
 */
export async function blake3CommitmentLike(wasmExports, ...parts) {
  const buf = concatBytes(parts.map(toBytes));
  if (wasmExports && wasmExports.compute_merkle_root) {
    try {
      const leaf = hex(buf);
      const res = wasmExports.compute_merkle_root(JSON.stringify([leaf]));
      if (res && res.root_hex) {
        return { hex: res.root_hex, algo: 'blake3' };
      }
    } catch (e) {
      // fall through to sha256
    }
  }
  const h = await sha256(buf);
  return { hex: hex(h), algo: 'sha256-fallback' };
}
