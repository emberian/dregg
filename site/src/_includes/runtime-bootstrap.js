/**
 * Pyana runtime bootstrap.
 *
 * Loads Preact + signals + htm from CDN, exposes `window.pyanaUi` for Studio
 * use, and mounts every `<[data-vizzer]>` element on the page once
 * its visualizer module has registered.
 *
 * Usage in any HTML page:
 *   <script type="module" src="/_includes/runtime-bootstrap.js"></script>
 *
 * The bootstrap is fail-soft: if the CDN is unreachable, a small banner
 * appears at the bottom of the page and `<[data-vizzer]>` elements display
 * their static fallback content.
 *
 * Pinned versions (bump deliberately, never float):
 *   preact 10.22.0, @preact/signals-core 1.7.0, htm 3.1.1
 */

const CDN = 'https://esm.sh';
const PREACT = `${CDN}/preact@10.22.0`;
const SIGNALS = `${CDN}/@preact/signals-core@1.7.0`;
const HTM = `${CDN}/htm@3.1.1`;

const registry = new Map();      // vizzer name → factory(host, dataset, api)
const pending = new Map();       // vizzer name → [hosts waiting to mount]

function failSoft(err) {
  console.warn('[pyana] runtime unavailable:', err);
  const banner = document.createElement('div');
  banner.setAttribute('role', 'status');
  banner.style.cssText = [
    'position:fixed', 'left:50%', 'bottom:16px', 'transform:translateX(-50%)',
    'background:#182420', 'color:#e4ddd0', 'border:1px solid rgba(228,221,208,0.16)',
    'border-radius:6px', 'padding:8px 14px', 'font:14px system-ui, sans-serif',
    'z-index:80', 'box-shadow:0 4px 12px rgba(0,0,0,0.5)',
  ].join(';');
  banner.textContent = 'Interactive features unavailable — refresh, or check network';
  document.body && document.body.appendChild(banner);
}

async function loadModules() {
  const [preact, signals, htmMod] = await Promise.all([
    import(PREACT),
    import(SIGNALS),
    import(HTM),
  ]);
  const html = htmMod.default.bind(preact.h);
  return { preact, signals, html };
}

function makeApi({ preact, signals, html }) {
  const reducedMotion = () =>
    window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  const hex = {
    to(bytes) {
      const arr = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
      return Array.from(arr, b => b.toString(16).padStart(2, '0')).join('');
    },
    from(s) {
      const clean = s.replace(/^0x/, '');
      const out = new Uint8Array(clean.length >> 1);
      for (let i = 0; i < out.length; i++) out[i] = parseInt(clean.substr(i * 2, 2), 16);
      return out;
    },
    short(s, n = 7) {
      if (!s) return '--';
      return s.length <= n * 2 + 3 ? s : `${s.slice(0, n)}…${s.slice(-n)}`;
    },
    color(s) {
      // Deterministic palette swatch from first 6 hex chars. Stays inside
      // the design palette by mixing into a moss / lantern / tide / ember base.
      if (!s) return 'var(--fg-muted)';
      const n = parseInt(s.slice(0, 6), 16);
      const base = ['#5b8a5a', '#c49245', '#6ba3c7', '#d4685c', '#9cc08a'][n % 5];
      return base;
    },
  };

  function toast(message, kind = 'info', ttl = 3200) {
    let host = document.querySelector('.pyana-toast-host');
    if (!host) {
      host = document.createElement('div');
      host.className = 'pyana-toast-host';
      document.body.appendChild(host);
    }
    const t = document.createElement('div');
    t.className = 'pyana-toast';
    t.dataset.kind = kind;
    t.textContent = message;
    host.appendChild(t);
    setTimeout(() => { t.style.opacity = '0'; t.style.transform = 'translateY(8px)'; }, ttl - 240);
    setTimeout(() => t.remove(), ttl);
  }

  async function copy(text) {
    try {
      await navigator.clipboard.writeText(text);
      toast('Copied', 'info', 1400);
      return true;
    } catch (e) {
      toast('Copy failed', 'err');
      return false;
    }
  }

  // Lightweight client-side highlight — defers to Shiki at build time for
  // server-rendered code. This is a runtime fallback only for code the user
  // types into the playground sandbox. For now: identity passthrough wrapped
  // in <pre><code>.
  function highlight(code, lang) {
    const el = document.createElement('pre');
    el.className = 'code-block code-block--runtime';
    const c = document.createElement('code');
    c.className = `language-${lang || 'plaintext'}`;
    c.textContent = code;
    el.appendChild(c);
    return el;
  }

  function register(name, factory) {
    registry.set(name, factory);
    const waiting = pending.get(name) || [];
    for (const host of waiting) mountOne(host);
    pending.delete(name);
  }

  function mountOne(host) {
    const name = host.dataset.vizzer;
    const factory = registry.get(name);
    if (!factory) {
      const list = pending.get(name) || [];
      list.push(host);
      pending.set(name, list);
      host.dataset.loading = 'true';
      return;
    }
    host.dataset.loading = 'false';
    // Fallback content stays in the DOM if mounting throws.
    try {
      const tree = factory(host, { ...host.dataset }, api);
      if (tree && typeof tree === 'object' && 'type' in tree) {
        // factory returned a Preact VNode — render it
        host.innerHTML = '';
        preact.render(tree, host);
      }
      // else: factory took over rendering itself
    } catch (e) {
      console.warn(`[pyana] vizzer ${name} failed`, e);
    }
  }

  function mount(root = document) {
    root.querySelectorAll('[data-vizzer]').forEach(host => {
      if (host.dataset.mounted === 'true') return;
      host.dataset.mounted = 'true';
      mountOne(host);
    });
  }

  const api = {
    // Preact + htm
    h: preact.h,
    render: preact.render,
    Fragment: preact.Fragment,
    html,
    // signals
    signal: signals.signal,
    computed: signals.computed,
    effect: signals.effect,
    batch: signals.batch,
    // helpers
    register,
    mount,
    highlight,
    copy,
    toast,
    reducedMotion,
    hex,
  };

  return api;
}

(async function boot() {
  try {
    const mods = await loadModules();
    const api = makeApi(mods);
    window.pyanaUi = api;

    // Dispatch an event so Studio modules can wait for readiness.
    // NOTE: window.pyana is the canonical user-facing dapp API owned by the
    // Cipherclerk browser extension. This bootstrap uses window.pyanaUi
    // to avoid the silent-failure collision (the extension claims window.pyana
    // via Object.defineProperty writable:false).
    window.dispatchEvent(new CustomEvent('pyanaUi:ready', { detail: api }));

    // Auto-mount any visualizers already in the document.
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', () => api.mount());
    } else {
      api.mount();
    }
  } catch (e) {
    failSoft(e);
  }
})();
