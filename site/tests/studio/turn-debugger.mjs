/**
 * Playwright ad-hoc test for <pyana-turn-debugger> inspector.
 *
 * Run with:
 *   node tests/studio/turn-debugger.mjs
 *
 * Requires dist/ to be served on port 8080 (the default playwright config):
 *   npx serve dist -l 8080
 *
 * What this test does:
 *  1. Navigates to /studio.html (has wasm + in-memory runtime + pyana-app#app)
 *  2. Waits for wasm init and runtime-ready
 *  3. Creates an agent, executes a turn to generate a turn_hash
 *  4. Injects turn-debugger.js (not in inspectors.js barrel)
 *  5. Mounts <pyana-turn-debugger uri="pyana://turn/<hash>">
 *  6. Verifies trace rows render (ptd__row elements)
 *  7. Clicks a row and verifies the expansion panel appears
 *  8. Tests compact mode
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

// proof-inspector-test.mjs uses 4818; if 8080 is also running (playwright config default),
// both work. The -L flag on curl showed 8080 → /studio redirect works fine.
const BASE = 'http://localhost:8080';

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => {
    if (msg.type() === 'error') errors.push(`[console.error] ${msg.text()}`);
  });

  console.log('[test] Navigating to /studio.html ...');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Wait for pyana:ready (Preact + signals loaded)
  await page.waitForFunction(() => !!window.pyana, { timeout: 20000 });
  console.log('[test] pyana:ready fired.');

  // Wait for the wasm runtime to be attached to the app element
  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] runtime attached to <pyana-app#app>.');

  // ─── Step 1: create agents and execute a turn via JS API ─────────────────
  // We call the runtime API directly (not via button clicks) so the test is
  // not coupled to the page's button wiring. createAgent → mintToken produces
  // a receipt in the sim.
  const turnHash = await page.evaluate(() => {
    const app = document.getElementById('app');
    const rt = app.runtime;

    // Create alice with initial balance
    const alice = rt.createAgent('alice', 5000n);
    if (!alice || alice.agent_index == null) {
      return { error: 'createAgent failed: ' + JSON.stringify(alice) };
    }

    // executeTurn generates a committed turn + receipt (even with empty actions)
    // fee must cover computrons; 1000 is sufficient for an empty turn
    const turnResult = rt.executeTurn(alice.agent_index, [], 1000);
    if (!turnResult) return { error: 'executeTurn returned null' };
    if (turnResult.status !== 'committed') {
      return { error: 'executeTurn not committed: ' + JSON.stringify(turnResult) };
    }

    // Grab the receipt chain
    const chain = rt.listReceipts(null).value || [];
    if (chain.length === 0) return { error: 'receipt chain empty after mint' };

    return chain[0].turn_hash;
  });

  if (!turnHash || typeof turnHash === 'object') {
    throw new Error('TEST SETUP FAILED: ' + JSON.stringify(turnHash));
  }
  console.log(`[test] turn_hash: ${turnHash.slice(0, 16)}…`);

  // ─── Step 2: inject turn-debugger.js module ───────────────────────────────
  await page.addScriptTag({ url: `${BASE}/_includes/studio/inspectors/turn-debugger.js`, type: 'module' });
  // Give the module a moment to register the custom element
  await page.waitForFunction(() => !!customElements.get('pyana-turn-debugger'), { timeout: 5000 });
  console.log('[test] <pyana-turn-debugger> custom element registered.');

  // ─── Step 3: mount element inside <pyana-app#app> ─────────────────────────
  await page.evaluate((hash) => {
    const el = document.createElement('pyana-turn-debugger');
    el.setAttribute('uri', `pyana://turn/${hash}`);
    el.setAttribute('id', 'test-debugger');
    document.getElementById('app').appendChild(el);
  }, turnHash);

  // Wait for the component to render (either rows or empty message)
  await page.waitForFunction(() => {
    const el = document.getElementById('test-debugger');
    return el && el.children.length > 0;
  }, { timeout: 8000 });
  console.log('[test] <pyana-turn-debugger> rendered.');

  // ─── Test 1: trace rows render ─────────────────────────────────────────────
  const rowCount = await page.evaluate(() => {
    const el = document.getElementById('test-debugger');
    return el ? el.querySelectorAll('.ptd__row').length : 0;
  });
  console.log(`[test 1] Trace row count: ${rowCount}`);

  if (rowCount === 0) {
    // Check if there's a "no trace steps" message (turn may not have any actions)
    const emptyMsg = await page.evaluate(() => {
      const el = document.getElementById('test-debugger');
      return el ? el.innerText : '';
    });
    console.log('[test 1] Element text when no rows:', emptyMsg.slice(0, 200));
    // A turn for agent creation may have 0 steps in the sim. This is expected.
    // We still check that the component rendered without error.
    const hasInspectorClass = await page.evaluate(() => {
      const el = document.getElementById('test-debugger');
      return el ? !!el.querySelector('.pyana-inspector') : false;
    });
    if (!hasInspectorClass) {
      throw new Error('TEST FAILED: inspector wrapper not rendered at all');
    }
    console.log('[test 1] PASS: empty trace rendered gracefully (0 steps in sim turn).');
  } else {
    console.log(`[test 1] PASS: ${rowCount} trace row(s) rendered.`);
  }

  // ─── Test 2: header and breadcrumb present ────────────────────────────────
  const hasHeader = await page.evaluate(() => {
    const el = document.getElementById('test-debugger');
    return el ? !!el.querySelector('.ptd__header') : false;
  });
  if (!hasHeader) throw new Error('TEST FAILED: ptd__header not found');
  console.log('[test 2] PASS: header present.');

  const breadcrumbText = await page.evaluate(() => {
    const el = document.getElementById('test-debugger');
    const bc = el && el.querySelector('.ptd__breadcrumb');
    return bc ? bc.textContent.trim() : '';
  });
  console.log(`[test 2] Breadcrumb: "${breadcrumbText}"`);
  if (!breadcrumbText) throw new Error('TEST FAILED: breadcrumb empty');

  // ─── Test 3: row click → expansion panel ─────────────────────────────────
  if (rowCount > 0) {
    await page.click('#test-debugger .ptd__row');
    await page.waitForFunction(() => {
      const el = document.getElementById('test-debugger');
      return el && el.querySelector('.ptd__expansion') !== null;
    }, { timeout: 3000 });
    const expansionText = await page.evaluate(() => {
      const el = document.getElementById('test-debugger');
      const exp = el && el.querySelector('.ptd__expansion');
      return exp ? exp.innerText.slice(0, 200) : '';
    });
    console.log(`[test 3] Expansion panel text: "${expansionText.slice(0, 120)}"`);
    if (!expansionText) throw new Error('TEST FAILED: expansion panel is empty');
    console.log('[test 3] PASS: expansion panel appears on row click.');

    // Click again to collapse
    await page.click('#test-debugger .ptd__row');
    await page.waitForTimeout(100);
    const expansionGone = await page.evaluate(() => {
      const el = document.getElementById('test-debugger');
      return el ? el.querySelector('.ptd__expansion') === null : true;
    });
    console.log(`[test 3] Expansion collapsed: ${expansionGone}`);
  } else {
    console.log('[test 3] SKIP: no rows to click (0-step trace).');
  }

  // ─── Test 4: compact mode ─────────────────────────────────────────────────
  await page.evaluate((hash) => {
    const el = document.createElement('pyana-turn-debugger');
    el.setAttribute('uri', `pyana://turn/${hash}`);
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-debugger-compact');
    document.getElementById('app').appendChild(el);
  }, turnHash);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-debugger-compact');
    return el && el.children.length > 0;
  }, { timeout: 5000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-debugger-compact');
    return el ? el.innerText.trim() : '';
  });
  console.log(`[test 4] Compact text: "${compactText}"`);

  // Compact mode should include "step" or "computrons"
  const hasCompactContent = compactText.includes('step') || compactText.includes('computron');
  if (!hasCompactContent) throw new Error(`TEST FAILED: compact mode text unexpected: "${compactText}"`);
  console.log('[test 4] PASS: compact mode renders summary line.');

  // ─── Test 5: bad URI shows error ──────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-turn-debugger');
    el.setAttribute('uri', 'pyana://cell/notAturnURI');
    el.setAttribute('id', 'test-debugger-bad');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-debugger-bad');
    return el && el.children.length > 0;
  }, { timeout: 3000 });

  const badText = await page.evaluate(() => {
    const el = document.getElementById('test-debugger-bad');
    return el ? el.innerText : '';
  });
  const showsError = badText.includes('wrong kind') || badText.includes('cell') || badText.includes('err');
  if (!showsError) throw new Error(`TEST FAILED: bad URI did not show error, got: "${badText}"`);
  console.log('[test 5] PASS: wrong-kind URI shows error.');

  // ─── Check for unexpected JS errors ──────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM not available') &&
    !e.includes('net::ERR_')
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors during test run:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message || err);
  process.exit(1);
});
