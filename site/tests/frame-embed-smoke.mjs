/**
 * Frame-embedding (site side) smoke test.
 *
 * Starbridge is the IDE host. Opening an app from the Apps surface renders an
 * <iframe class="sb__app-frame"> whose src is the app page with ?embedded=1.
 * The SITE-side contract this test pins:
 *
 *   1. The embedded app frame loads runtime-bootstrap.js itself, so
 *      `window.dreggUi` is DEFINED inside the frame.
 *   2. The frame attaches a real runtime to its <dregg-app> (host-attached if
 *      the parent exposed one, else its own in-frame in-memory runtime).
 *   3. A <dregg-*> inspector inside the frame UPGRADES (custom element defined)
 *      and renders REAL content — not a spinner, not a blank frame.
 *   4. Zero console/page errors in BOTH the parent and the frame.
 *
 * Note: locally `serve` sends no X-Frame-Options, so framing works. The
 * deployed Caddy header fix is owned by the devnet lane; here we verify the
 * in-frame runtime wiring only.
 *
 * Prereqs:  dist served on :8080  →  npx serve dist -l 8080
 * Run:      node tests/frame-embed-smoke.mjs
 * Env:      STARBRIDGE_BASE (default http://localhost:8080)
 *           APP_ID          (default nameservice)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';
const APP_ID = process.env.APP_ID || 'nameservice';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const parentErrors = [];
  const frameErrors = [];
  // Tag console/page errors by frame so we can attribute them.
  page.on('pageerror', (e) => parentErrors.push(e.message));
  page.on('console', (msg) => {
    if (msg.type() !== 'error') return;
    const url = msg.location()?.url || '';
    const text = msg.text();
    if (url.includes('/starbridge-apps/')) frameErrors.push(text);
    else parentErrors.push(text);
  });

  // ─── Boot the host ─────────────────────────────────────────────────────────
  await page.goto(`${BASE}/starbridge/`, { waitUntil: 'domcontentloaded' });
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  // Parent must expose the runtime handle apps reach for.
  await page.waitForFunction(() => !!window.__starbridge?.runtime, { timeout: 20000 });
  check('parent exposes window.__starbridge.runtime', true);

  // ─── Trigger the app embed ────────────────────────────────────────────────
  // Open the app workspace the same way the UI does (Apps surface / palette).
  await page.evaluate((id) => {
    window.__starbridge.setCurrentUri(`dregg://app/${id}`);
  }, APP_ID);

  // The app workspace mounts the iframe.
  await page.waitForSelector('iframe.sb__app-frame', { timeout: 15000 });
  const frameSrc = await page.getAttribute('iframe.sb__app-frame', 'src');
  check('app frame mounted with embedded src', /embedded=1/.test(frameSrc || ''), frameSrc || '');

  // ─── Reach into the frame ─────────────────────────────────────────────────
  const elHandle = await page.$('iframe.sb__app-frame');
  const frame = await elHandle.contentFrame();
  check('iframe has a content frame', !!frame);

  // (1) window.dreggUi defined INSIDE the frame.
  await frame.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  check('window.dreggUi defined inside frame', true);

  // (2) The frame attaches a real runtime to its <dregg-app>.
  await frame.waitForFunction(() => {
    const app = document.querySelector('dregg-app');
    return app && app.runtime && app.runtime.caps;
  }, { timeout: 20000 });
  const runtimeInfo = await frame.evaluate(() => {
    const app = document.querySelector('dregg-app');
    let parentRuntime = null;
    try { parentRuntime = window.parent?.__starbridge?.runtime ?? null; } catch {}
    return {
      hasRuntime: !!app?.runtime,
      caps: app?.runtime?.caps || null,
      source: app?.runtime?.source?.kind || null,
      // Must be the frame's OWN runtime, NOT the parent realm's object — a
      // borrowed cross-realm runtime would make in-frame signal effects dead.
      borrowedFromParent: !!parentRuntime && app?.runtime === parentRuntime,
    };
  });
  check('frame <dregg-app> has a runtime', runtimeInfo.hasRuntime,
    `source=${runtimeInfo.source} caps=${JSON.stringify(runtimeInfo.caps)}`);
  check('frame runtime is in-frame (not a borrowed cross-realm object)',
    runtimeInfo.borrowedFromParent === false);

  // (3) A <dregg-*> inspector inside the frame upgrades + renders real content.
  //     dregg-name-registry renders into a shadow root, so read shadowRoot text.
  await frame.waitForSelector('dregg-name-registry', { timeout: 15000 });
  // Wait for the element to actually paint its chrome (not just be defined).
  await frame.waitForFunction(() => {
    const el = document.querySelector('dregg-name-registry');
    const txt = (el?.shadowRoot?.textContent || el?.textContent || '').trim();
    return txt.length > 0;
  }, { timeout: 15000 }).catch(() => {});
  const upgraded = await frame.evaluate(() => {
    const el = document.querySelector('dregg-name-registry');
    if (!el) return { defined: false };
    const tag = el.tagName.toLowerCase();
    const root = el.shadowRoot || el;
    return {
      defined: !!customElements.get(tag),
      // Real content = the inspector painted its own chrome (toolbar/table/empty
      // state), and is NOT stuck on the transient "loading registry…" spinner.
      text: (root.textContent || '').replace(/\s+/g, ' ').trim(),
      // Concrete structural proof the inspector painted its OWN chrome
      // (toolbar / search input / table / empty-state), not just whitespace.
      hasChrome: !!root.querySelector?.(
        'input[type=search], table, [class*="toolbar"], [class*="empty"], dregg-status-bar',
      ),
      stuckLoading: /^(loading registry…|loading…)$/i.test((root.textContent || '').trim()),
    };
  });
  check('inspector custom element is defined inside frame', upgraded.defined === true);
  const looksReal = upgraded.hasChrome && !upgraded.stuckLoading
    && upgraded.text && upgraded.text.length > 0;
  check('inspector rendered real content (not blank / not bare spinner)', looksReal,
    upgraded.text ? upgraded.text.slice(0, 120) : '(empty)');

  // Give the runtime a beat to settle, then re-confirm no errors crept in.
  await page.waitForTimeout(800);

  // (4) Zero errors in both frames.
  check('no parent-frame errors', parentErrors.length === 0, parentErrors.join(' | '));
  check('no embedded-frame errors', frameErrors.length === 0, frameErrors.join(' | '));

  await browser.close();
  console.log(`\n[frame-embed] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[frame-embed] crashed:', e); process.exit(2); });
