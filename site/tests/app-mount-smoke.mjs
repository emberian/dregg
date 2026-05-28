/**
 * Generic mount smoke for the remaining starbridge-app pages
 * (subscription, governed-namespace).
 *
 * These apps are honestly MOUNTED (not fully end-to-end this pass): the page
 * loads, the in-memory runtime attaches, a real cell is bound + a real
 * window.dregg.signTurn is installed, and their custom elements UPGRADE and
 * render real chrome — no undefined-element / blank-panel errors. Their core
 * multi-party flows (publisher/consumer grants; propose/vote/commit with
 * threshold-sig auth) need richer multi-agent + Authorization::Custom wiring
 * than the single-agent preview provides; the Rust integration tests prove
 * those flows at the executor level.
 *
 * Prereqs:  dist served on :8080.
 * Run:      node tests/app-mount-smoke.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';

const APPS = [
  {
    id: 'subscription',
    tags: ['dregg-subscription', 'dregg-subscription-publish-form', 'dregg-subscription-feed'],
  },
  {
    id: 'governed-namespace',
    tags: ['dregg-namespace', 'dregg-namespace-route-table', 'dregg-namespace-proposal',
      'dregg-namespace-dispatch'],
  },
];

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function smokeApp(browser, app) {
  const page = await browser.newPage();
  const errors = [];
  page.on('pageerror', (e) => errors.push(e.message));
  page.on('console', (m) => { if (m.type() === 'error') errors.push(m.text()); });

  await page.goto(`${BASE}/starbridge-apps/${app.id}/pages/`, { waitUntil: 'domcontentloaded' });

  await page.waitForFunction(() => {
    const a = document.querySelector('dregg-app');
    return a && a.runtime && a.runtime.caps;
  }, { timeout: 25000 }).catch(() => {});
  const hasRuntime = await page.evaluate(() => {
    const a = document.querySelector('dregg-app');
    return !!(a && a.runtime && a.runtime.caps);
  });
  check(`[${app.id}] runtime attached`, hasRuntime);

  await page.waitForFunction(() => !!window.__starbridgeAppCellUri, { timeout: 25000 }).catch(() => {});
  const cellUri = await page.evaluate(() => window.__starbridgeAppCellUri);
  check(`[${app.id}] real cell created + bound`,
    /^dregg:\/\/cell\/[0-9a-f]{64}$/.test(cellUri || ''), cellUri || '(none)');

  for (const tag of app.tags) {
    const info = await page.evaluate((t) => {
      const defined = !!customElements.get(t);
      const el = document.querySelector(t);
      const root = el?.shadowRoot || el;
      const text = (root?.textContent || '').replace(/\s+/g, ' ').trim();
      return { defined, painted: text.length > 0 };
    }, tag);
    check(`[${app.id}] <${tag}> defined`, info.defined);
    check(`[${app.id}] <${tag}> rendered content`, info.painted);
  }

  await page.waitForTimeout(300);
  const realErrors = errors.filter((e) => !/read-only|credentials|listEntries/.test(e));
  check(`[${app.id}] no console/page errors`, realErrors.length === 0, realErrors.join(' | '));

  await page.close();
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  for (const app of APPS) await smokeApp(browser, app);
  await browser.close();
  console.log(`\n[app-mount] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[app-mount] crashed:', e); process.exit(2); });
