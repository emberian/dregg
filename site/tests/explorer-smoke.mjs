/**
 * Explorer ⇄ inspector parity smoke test.
 *
 * The explorer is the SAME platform inspectors as the Studio, over a live
 * dregg-node via RemoteRuntime (read-only). This test verifies:
 *
 *   1. The page boots, mounts a single <dregg-app id="explorer-app">, and
 *      attaches a RemoteRuntime (caps.read=true, caps.mutate=false).
 *   2. When connected, real node data renders THROUGH real inspectors:
 *      - Cells page mounts <dregg-cell-list> with the node's actual cells.
 *      - Federation page mounts <dregg-federation-list> with a real federation.
 *      - Deep-linking ?at=dregg://cell/<id> mounts <dregg-cell> with live data.
 *   3. When offline (no reachable node), the connection chrome says "offline"
 *      and inspectors show honest empty states — never fabricated data.
 *
 * Prereqs:
 *   - dist served on :8080  →  npx serve dist -l 8080
 *   - a dregg-node on :8420 with at least one cell (faucet-seeded):
 *       dregg-node init --data-dir /tmp/dregg-explorer-data
 *       dregg-node run --port 8420 --federation-size 1 --enable-faucet \
 *         --data-dir /tmp/dregg-explorer-data
 *       curl -XPOST localhost:8420/api/faucet -d '{"recipient":"<64hex>","amount":1000}'
 *
 * Run:  node tests/explorer-smoke.mjs
 * Env:  EXPLORER_BASE (default http://localhost:8080)
 *       NODE_URL      (default http://localhost:8420)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.EXPLORER_BASE || 'http://localhost:8080';
const NODE_URL = process.env.NODE_URL || 'http://localhost:8420';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function bootExplorer(page, { nodeUrl }) {
  // Seed node URL + disable auto-refresh churn before the module boots.
  await page.addInitScript((url) => {
    localStorage.setItem('dregg_node_url', url);
    localStorage.setItem('dregg_auto_refresh', 'false');
  }, nodeUrl);
  await page.goto(`${BASE}/explorer/`, { waitUntil: 'domcontentloaded' });
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  await page.waitForFunction(() => {
    const app = document.getElementById('explorer-app');
    return app && app.runtime && app.runtime.caps;
  }, { timeout: 20000 });
}

async function run() {
  // Is a node actually reachable? Decides whether we run the live assertions.
  let nodeCells = [];
  let nodeLive = false;
  try {
    const res = await fetch(`${NODE_URL}/api/cells`);
    if (res.ok) { nodeCells = await res.json(); nodeLive = true; }
  } catch {}
  console.log(`[smoke] node ${NODE_URL} live=${nodeLive} cells=${nodeCells.length}`);

  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();
  const pageErrors = [];
  page.on('pageerror', e => pageErrors.push(e.message));

  // ─── Connected path ──────────────────────────────────────────────────────
  await bootExplorer(page, { nodeUrl: NODE_URL });

  const caps = await page.evaluate(() => document.getElementById('explorer-app').runtime.caps);
  check('runtime is read-only', caps.read === true && caps.mutate === false, JSON.stringify(caps));

  const source = await page.evaluate(() => document.getElementById('explorer-app').runtime.source);
  check('runtime source is remote', source.kind === 'remote', source.label);

  if (nodeLive) {
    // Connection indicator goes to "connected".
    await page.waitForFunction(
      () => document.getElementById('connection-status')?.classList.contains('connected'),
      { timeout: 15000 },
    ).catch(() => {});
    const connected = await page.evaluate(() =>
      document.getElementById('connection-status')?.classList.contains('connected'));
    check('connection indicator shows connected', connected === true);

    // Cells page → <dregg-cell-list> with real cells.
    await page.click('[data-page="cells"]');
    await page.waitForSelector('#mount-cells dregg-cell-list', { timeout: 10000 });
    // Wait for the runtime poll to populate the list.
    await page.waitForFunction(() => {
      const list = document.querySelector('#mount-cells dregg-cell-list');
      return list && list.querySelectorAll('dregg-cell').length > 0;
    }, { timeout: 15000 }).catch(() => {});
    const renderedCells = await page.evaluate(() =>
      document.querySelectorAll('#mount-cells dregg-cell-list dregg-cell').length);
    check('cells render through <dregg-cell-list>', renderedCells > 0,
      `${renderedCells} <dregg-cell> mounted (node has ${nodeCells.length})`);

    // Federation page → <dregg-federation-list> with a real federation row.
    await page.click('[data-page="federation"]');
    await page.waitForSelector('#mount-federation dregg-federation-list', { timeout: 10000 });
    await page.waitForFunction(() => {
      const t = document.querySelector('#mount-federation dregg-federation-list')?.textContent || '';
      return /federation/i.test(t);
    }, { timeout: 15000 }).catch(() => {});
    const fedText = await page.evaluate(() =>
      document.querySelector('#mount-federation dregg-federation-list')?.textContent || '');
    check('federation renders through <dregg-federation-list>', /federation/i.test(fedText));

    // Deep-link a real cell → <dregg-cell> renders its live balance.
    if (nodeCells.length) {
      const cellId = nodeCells[0].id;
      await page.goto(`${BASE}/explorer/?at=${encodeURIComponent(`dregg://cell/${cellId}`)}`,
        { waitUntil: 'domcontentloaded' });
      await page.addInitScript(() => {}); // noop, init script already applied via context
      await page.waitForFunction(() => {
        const app = document.getElementById('explorer-app');
        return app && app.runtime && app.runtime.caps;
      }, { timeout: 20000 });
      await page.waitForSelector('#detail-cells dregg-cell, #mount-cells dregg-cell', { timeout: 10000 });
      await page.waitForFunction((id) => {
        const els = document.querySelectorAll('dregg-cell');
        for (const el of els) {
          if ((el.getAttribute('uri') || '').includes(id) && /balance/i.test(el.textContent)) return true;
        }
        return false;
      }, cellId, { timeout: 15000 }).catch(() => {});
      const cellRendered = await page.evaluate((id) => {
        const els = document.querySelectorAll('dregg-cell');
        for (const el of els) {
          if ((el.getAttribute('uri') || '').includes(id) && /balance/i.test(el.textContent)) {
            return el.textContent.replace(/\s+/g, ' ').trim().slice(0, 80);
          }
        }
        return null;
      }, cellId);
      check('deep-linked cell renders live data through <dregg-cell>', !!cellRendered, cellRendered || 'not found');
    }
  } else {
    console.log('[smoke] node not live — skipping connected assertions, running offline path only');
  }

  // ─── Offline path ────────────────────────────────────────────────────────
  // Point at a dead port; nothing must be fabricated.
  await bootExplorer(page, { nodeUrl: 'http://127.0.0.1:9' });
  await page.waitForFunction(
    () => document.getElementById('connection-status')?.classList.contains('error'),
    { timeout: 15000 },
  ).catch(() => {});
  const offline = await page.evaluate(() => {
    const el = document.getElementById('connection-status');
    return { error: el?.classList.contains('error'), label: el?.querySelector('.ex-connection__label')?.textContent };
  });
  check('offline → connection shows error/offline', offline.error === true, offline.label);

  await page.click('[data-page="cells"]');
  await page.waitForSelector('#mount-cells dregg-cell-list', { timeout: 10000 });
  // Give the dead-port runtime a moment; it must NOT invent cells.
  await page.waitForTimeout(1500);
  const offlineCells = await page.evaluate(() =>
    document.querySelectorAll('#mount-cells dregg-cell-list dregg-cell').length);
  check('offline → no fabricated cells', offlineCells === 0, `${offlineCells} cells`);
  const offlineEmpty = await page.evaluate(() =>
    (document.querySelector('#mount-cells dregg-cell-list')?.textContent || '').toLowerCase());
  check('offline → cell-list shows honest empty state',
    offlineEmpty.includes('no cells'), offlineEmpty.slice(0, 60));

  check('no uncaught page errors', pageErrors.length === 0, pageErrors.join(' | '));

  await browser.close();
  console.log(`\n[smoke] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[smoke] crashed:', e); process.exit(2); });
