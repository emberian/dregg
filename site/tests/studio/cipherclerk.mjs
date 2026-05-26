/**
 * Playwright test for <pyana-cipherclerk> inspector.
 *
 * Run with:
 *   node tests/studio/cipherclerk.mjs
 *
 * Requires the site served on port 8080:
 *   npx serve . -l 8080   (from /Users/ember/dev/breadstuffs/site)
 *
 * Tests:
 *  1. Component mounts and renders all four tabs (Identity, Holdings, History, Stealth)
 *  2. KV grid is present with cell-deeplink embedding <pyana-cell>
 *  3. Clicking Holdings tab renders the tab panel
 *  4. Clicking History tab renders the History panel (shows chain or empty note)
 *  5. Clicking Stealth tab renders the Stealth panel
 *  6. cell deeplink (<pyana-cell>) is present in KV grid after agent creation
 *  7. Compact mode renders name + counts line
 *  8. Bad URI shows error
 *  9. No unexpected JS errors
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

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

  console.log('[test] Navigating to /studio …');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Wait for pyanaUi (the rename from window.pyana per STARBRIDGE-PLAN §4.2).
  // Fall back to window.pyana for compatibility with runtimes that haven't
  // completed the rename yet.
  await page.waitForFunction(() => !!(window.pyanaUi || window.pyana), { timeout: 20000 });
  console.log('[test] pyanaUi/pyana ready.');

  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] runtime attached.');

  // ── Step 1: Create Alice agent ────────────────────────────────────────────
  const aliceInfo = await page.evaluate(() => {
    const rt = document.getElementById('app').runtime;
    const alice = rt.createAgent('alice', 5000n);
    if (!alice || alice.agent_index == null) {
      return { error: 'createAgent failed: ' + JSON.stringify(alice) };
    }
    // Execute a turn so the receipt chain is non-empty
    const turn = rt.executeTurn(alice.agent_index, [], 1000);
    if (!turn || turn.status !== 'committed') {
      return { error: 'executeTurn failed: ' + JSON.stringify(turn) };
    }
    return {
      agent_index: alice.agent_index,
      cell_id: alice.cell_id,
      public_key: alice.public_key,
    };
  });

  if (aliceInfo.error) throw new Error('TEST SETUP FAILED: ' + aliceInfo.error);
  console.log(`[test] Alice created: agent_index=${aliceInfo.agent_index}, cell_id=${aliceInfo.cell_id?.slice(0, 16)}…`);

  // ── Step 2: Inject cipherclerk.js module ─────────────────────────────────
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/cipherclerk.js`,
    type: 'module',
  });
  await page.waitForFunction(() => !!customElements.get('pyana-cipherclerk'), { timeout: 5000 });
  console.log('[test] <pyana-cipherclerk> registered.');

  // ── Step 3: Mount element ─────────────────────────────────────────────────
  await page.evaluate((agentIdx) => {
    const el = document.createElement('pyana-cipherclerk');
    el.setAttribute('uri', `pyana://cipherclerk/${agentIdx}`);
    el.setAttribute('id', 'test-cc');
    document.getElementById('app').appendChild(el);
  }, aliceInfo.agent_index);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc');
    return el && el.querySelector('[data-testid="pcc-root"]') !== null;
  }, { timeout: 8000 });
  console.log('[test] <pyana-cipherclerk> rendered.');

  // ── Test 1: header is present with agent name + badge ────────────────────
  const headerText = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    const name = el && el.querySelector('[data-testid="pcc-agent-name"]');
    return name ? name.textContent.trim() : '';
  });
  if (!headerText.toLowerCase().includes('alice')) {
    throw new Error(`TEST 1 FAILED: header doesn't include "alice", got: "${headerText}"`);
  }
  console.log(`[test 1] PASS: header text "${headerText}".`);

  // ── Test 2: KV grid is present ────────────────────────────────────────────
  const kvPresent = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-kv"]') : false;
  });
  if (!kvPresent) throw new Error('TEST 2 FAILED: KV grid not found');
  console.log('[test 2] PASS: KV grid present.');

  // ── Test 3: All four tab buttons render ───────────────────────────────────
  const tabIds = ['identity', 'holdings', 'history', 'stealth'];
  for (const tabId of tabIds) {
    const found = await page.evaluate((tid) => {
      const el = document.getElementById('test-cc');
      return el ? !!el.querySelector(`[data-testid="pcc-tab-${tid}"]`) : false;
    }, tabId);
    if (!found) throw new Error(`TEST 3 FAILED: tab "${tabId}" not found`);
    console.log(`[test 3] PASS: tab "${tabId}" present.`);
  }

  // ── Test 4: Identity tab panel is visible by default ─────────────────────
  const identityPanelVisible = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-panel-identity"]') : false;
  });
  if (!identityPanelVisible) throw new Error('TEST 4 FAILED: Identity panel not visible by default');
  console.log('[test 4] PASS: Identity tab panel visible on load.');

  // ── Test 5: Click Holdings tab → Holdings panel renders ──────────────────
  await page.click('#test-cc [data-testid="pcc-tab-holdings"]');
  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-panel-holdings"]') : false;
  }, { timeout: 3000 });
  const holdingsTodo = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-tokens-todo"]') : false;
  });
  if (!holdingsTodo) throw new Error('TEST 5 FAILED: Holdings panel or token-TODO not found');
  console.log('[test 5] PASS: Holdings tab panel renders with TODO note.');

  // ── Test 6: Click History tab → History panel renders ────────────────────
  await page.click('#test-cc [data-testid="pcc-tab-history"]');
  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-panel-history"]') : false;
  }, { timeout: 3000 });
  // We executed a turn, so receipt chain should have content or at least render
  const historyPanel = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    const panel = el && el.querySelector('[data-testid="pcc-panel-history"]');
    return panel ? panel.textContent.trim().slice(0, 200) : '';
  });
  if (!historyPanel) throw new Error('TEST 6 FAILED: History panel is empty');
  console.log(`[test 6] PASS: History panel rendered: "${historyPanel.slice(0, 80)}…"`);

  // ── Test 7: Click Stealth tab → Stealth panel renders ────────────────────
  await page.click('#test-cc [data-testid="pcc-tab-stealth"]');
  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-panel-stealth"]') : false;
  }, { timeout: 3000 });
  const stealthNote = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-stealth-notes-todo"]') : false;
  });
  if (!stealthNote) throw new Error('TEST 7 FAILED: Stealth panel or stealth-TODO not found');
  console.log('[test 7] PASS: Stealth tab panel renders with TODO note.');

  // ── Test 8: Cell deeplink — navigate back to Identity to check ─────────────
  await page.click('#test-cc [data-testid="pcc-tab-identity"]');
  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc');
    return el ? !!el.querySelector('[data-testid="pcc-panel-identity"]') : false;
  }, { timeout: 3000 });

  // The KV grid should contain a <pyana-cell> deeplink for the agent's cell_id.
  // pyana-cell is registered in inspectors.js (loaded by studio page).
  const cellDeeplinkPresent = await page.evaluate(() => {
    const el = document.getElementById('test-cc');
    // Look for pyana-cell anywhere inside the component
    return el ? el.querySelector('pyana-cell') !== null : false;
  });
  if (!cellDeeplinkPresent) {
    throw new Error('TEST 8 FAILED: no <pyana-cell> deeplink found inside <pyana-cipherclerk>');
  }
  console.log('[test 8] PASS: <pyana-cell> deeplink present in Identity/KV grid.');

  // ── Test 9: Compact mode renders summary ────────────────────────────────
  await page.evaluate((agentIdx) => {
    const el = document.createElement('pyana-cipherclerk');
    el.setAttribute('uri', `pyana://cipherclerk/${agentIdx}`);
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-cc-compact');
    document.getElementById('app').appendChild(el);
  }, aliceInfo.agent_index);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc-compact');
    return el && el.querySelector('[data-testid="pcc-compact"]') !== null;
  }, { timeout: 5000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-cc-compact');
    return el ? el.textContent.trim() : '';
  });
  const hasAlice = compactText.toLowerCase().includes('alice');
  const hasCaps = compactText.includes('cap') || compactText.includes('token') || compactText.includes('receipt');
  if (!hasAlice || !hasCaps) {
    throw new Error(`TEST 9 FAILED: compact text unexpected: "${compactText}"`);
  }
  console.log(`[test 9] PASS: compact mode: "${compactText.slice(0, 80)}"`);

  // ── Test 10: Bad URI shows error ─────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-cipherclerk');
    el.setAttribute('uri', 'pyana://cell/notacipherclerk');
    el.setAttribute('id', 'test-cc-bad');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cc-bad');
    return el && el.children.length > 0;
  }, { timeout: 3000 });

  const badText = await page.evaluate(() => {
    const el = document.getElementById('test-cc-bad');
    return el ? el.innerText : '';
  });
  const showsError = badText.includes('wrong kind') || badText.includes('err') || badText.includes('cell');
  if (!showsError) throw new Error(`TEST 10 FAILED: bad URI didn't show error, got: "${badText}"`);
  console.log('[test 10] PASS: wrong-kind URI shows error.');

  // ── JS error check ────────────────────────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM not available') &&
    !e.includes('net::ERR_') &&
    !e.includes('favicon')
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors during run:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message || err);
  process.exit(1);
});
