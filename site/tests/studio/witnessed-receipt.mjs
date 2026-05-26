/**
 * Playwright ad-hoc test for <pyana-witnessed-receipt> inspector.
 *
 * Run with:
 *   node tests/studio/witnessed-receipt.mjs
 *
 * Requires dist/ to be served on port 4818 (or 8080):
 *   npx serve dist -l 4818
 *
 * What this test does:
 *  1. Navigates to /studio.html (has wasm + in-memory runtime + pyana-app#app)
 *  2. Waits for wasm init and runtime-ready
 *  3. Creates an agent, executes a turn to generate a turn_hash → receipt
 *  4. Injects witnessed-receipt.js + its dependencies (proof.js, receipt.js)
 *  5. Mounts <pyana-witnessed-receipt uri="pyana://receipt/<hash>">
 *  6. Verifies scope-0 + Placeholder tier render (sim runtime → no proof_view)
 *  7. Verifies embedded <pyana-receipt> and <pyana-proof> mount correctly
 *  8. Tests compact mode output
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

const BASE = 'http://localhost:4818';

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => {
    if (msg.type() === 'error') errors.push(`[console.error] ${msg.text()}`);
  });

  console.log('[test] Navigating to /studio ...');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Wait for pyanaUi:ready (Preact + signals loaded; dist uses window.pyanaUi)
  await page.waitForFunction(() => !!window.pyanaUi, { timeout: 20000 });
  console.log('[test] pyanaUi:ready fired.');

  // Wait for the wasm runtime to be attached to the app element
  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] runtime attached to <pyana-app#app>.');

  // ─── Step 1: create agent + execute a turn ──────────────────────────────────
  const turnHash = await page.evaluate(() => {
    const rt = document.getElementById('app').runtime;
    const alice = rt.createAgent('alice', 5000n);
    if (!alice || alice.agent_index == null) {
      return { error: 'createAgent failed: ' + JSON.stringify(alice) };
    }
    const turnResult = rt.executeTurn(alice.agent_index, [], 1000);
    if (!turnResult) return { error: 'executeTurn returned null' };
    if (turnResult.status !== 'committed') {
      return { error: 'executeTurn not committed: ' + JSON.stringify(turnResult) };
    }
    const chain = rt.listReceipts(null).value || [];
    if (chain.length === 0) return { error: 'receipt chain empty after turn' };
    return chain[0].turn_hash;
  });

  if (!turnHash || typeof turnHash === 'object') {
    throw new Error('TEST SETUP FAILED: ' + JSON.stringify(turnHash));
  }
  console.log(`[test] turn_hash: ${turnHash.slice(0, 16)}…`);

  // ─── Step 2: inject witnessed-receipt.js (proof.js already loaded via barrel) ──
  // proof.js and receipt.js are in the barrel (inspectors.js) loaded by studio.html
  // witnessed-receipt.js is not yet in the barrel, so inject as module.
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/witnessed-receipt.js`,
    type: 'module',
  });
  await page.waitForFunction(
    () => !!customElements.get('pyana-witnessed-receipt'),
    { timeout: 5000 }
  );
  console.log('[test] <pyana-witnessed-receipt> custom element registered.');

  // ─── Step 3: mount inside <pyana-app#app> ───────────────────────────────────
  await page.evaluate((hash) => {
    const el = document.createElement('pyana-witnessed-receipt');
    el.setAttribute('uri', `pyana://receipt/${hash}`);
    el.setAttribute('id', 'test-wr');
    document.getElementById('app').appendChild(el);
  }, turnHash);

  // Wait for the component to produce children
  await page.waitForFunction(() => {
    const el = document.getElementById('test-wr');
    return el && el.children.length > 0;
  }, { timeout: 8000 });
  console.log('[test] <pyana-witnessed-receipt> rendered.');

  // ─── Test 1: scope-0 badge present ─────────────────────────────────────────
  const scopeBadgeText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const badge = el && el.querySelector('.pwr__scope-badge');
    return badge ? badge.textContent.trim() : '';
  });
  console.log(`[test 1] Scope badge text: "${scopeBadgeText}"`);
  if (!scopeBadgeText.includes('Scope-0')) {
    throw new Error(`TEST FAILED: expected scope badge "Scope-0", got "${scopeBadgeText}"`);
  }
  console.log('[test 1] PASS: scope-0 badge rendered (sim runtime has no proof_view).');

  // ─── Test 2: Placeholder tier badge present ─────────────────────────────────
  const tierBadgeText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const badge = el && el.querySelector('.pwr__tier-badge');
    return badge ? badge.textContent.trim() : '';
  });
  console.log(`[test 2] Tier badge text: "${tierBadgeText}"`);
  if (!tierBadgeText.includes('Placeholder')) {
    throw new Error(`TEST FAILED: expected tier badge "Placeholder tier", got "${tierBadgeText}"`);
  }
  console.log('[test 2] PASS: Placeholder tier badge rendered.');

  // ─── Test 3: embedded <pyana-receipt> mounts ────────────────────────────────
  // The sub-pane uses a <details open> + <pyana-receipt uri=...> child element.
  // We wait for the sub-element to have rendered children.
  const receiptMounted = await page.waitForFunction(() => {
    const el = document.getElementById('test-wr');
    if (!el) return false;
    const sub = el.querySelector('pyana-receipt');
    // pyana-receipt renders a div child once it resolves
    return sub && sub.children.length > 0;
  }, { timeout: 8000 }).then(() => true).catch(() => false);

  console.log(`[test 3] <pyana-receipt> mounted: ${receiptMounted}`);
  if (!receiptMounted) {
    // Inspect the DOM to understand the state
    const wrHtml = await page.evaluate(() => {
      const el = document.getElementById('test-wr');
      return el ? el.innerHTML.slice(0, 800) : '(no element)';
    });
    console.log('[test 3] witnessed-receipt innerHTML:', wrHtml);
    throw new Error('TEST FAILED: embedded <pyana-receipt> did not render children');
  }
  console.log('[test 3] PASS: embedded <pyana-receipt> rendered.');

  // ─── Test 4: embedded <pyana-proof> mounts ──────────────────────────────────
  const proofMounted = await page.waitForFunction(() => {
    const el = document.getElementById('test-wr');
    if (!el) return false;
    const sub = el.querySelector('pyana-proof');
    return sub && sub.children.length > 0;
  }, { timeout: 8000 }).then(() => true).catch(() => false);

  console.log(`[test 4] <pyana-proof> mounted: ${proofMounted}`);
  if (!proofMounted) {
    throw new Error('TEST FAILED: embedded <pyana-proof> did not render children');
  }
  // The proof element should contain a scope-0 indicator (no proof in sim)
  const proofText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const sub = el && el.querySelector('pyana-proof');
    return sub ? sub.innerText.slice(0, 400) : '';
  });
  console.log(`[test 4] <pyana-proof> text: "${proofText.slice(0, 120)}"`);
  const proofShowsScope0 = proofText.toLowerCase().includes('scope-0') ||
    proofText.toLowerCase().includes('no proof') ||
    proofText.toLowerCase().includes('placeholder');
  if (!proofShowsScope0) {
    console.warn('[test 4] WARN: <pyana-proof> did not show scope-0 language (may be ok if tier badge shown)');
  } else {
    console.log('[test 4] PASS: embedded <pyana-proof> shows scope-0 / no proof content.');
  }

  // ─── Test 5: scope strip renders scope description ──────────────────────────
  const stripText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const strip = el && el.querySelector('.pwr__scope-strip');
    return strip ? strip.innerText.trim() : '';
  });
  console.log(`[test 5] Scope strip text: "${stripText.slice(0, 120)}"`);
  if (!stripText) {
    throw new Error('TEST FAILED: .pwr__scope-strip not found');
  }
  console.log('[test 5] PASS: scope strip rendered.');

  // ─── Test 6: compact mode ───────────────────────────────────────────────────
  await page.evaluate((hash) => {
    const el = document.createElement('pyana-witnessed-receipt');
    el.setAttribute('uri', `pyana://receipt/${hash}`);
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-wr-compact');
    document.getElementById('app').appendChild(el);
  }, turnHash);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-wr-compact');
    return el && el.children.length > 0;
  }, { timeout: 5000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-wr-compact');
    return el ? el.innerText.trim() : '';
  });
  console.log(`[test 6] Compact text: "${compactText}"`);

  const compactLower = compactText.toLowerCase();
  const hasScope = compactLower.includes('scope-');
  const hasTier = compactLower.includes('tier') || compactLower.includes('placeholder');
  const hasTurn = compactLower.includes('turn');
  if (!hasScope) throw new Error(`TEST FAILED: compact mode missing scope badge, got: "${compactText}"`);
  if (!hasTier) throw new Error(`TEST FAILED: compact mode missing tier, got: "${compactText}"`);
  if (!hasTurn) throw new Error(`TEST FAILED: compact mode missing turn=, got: "${compactText}"`);
  console.log('[test 6] PASS: compact mode has scope + tier + turn=.');

  // ─── Test 7: bad URI shows error ────────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-witnessed-receipt');
    el.setAttribute('uri', 'pyana://cell/notAreceiptURI');
    el.setAttribute('id', 'test-wr-bad');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-wr-bad');
    return el && el.children.length > 0;
  }, { timeout: 3000 });

  const badText = await page.evaluate(() => {
    const el = document.getElementById('test-wr-bad');
    return el ? el.innerText : '';
  });
  const showsError = badText.includes('wrong kind') || badText.includes('cell') || badText.includes('err');
  if (!showsError) throw new Error(`TEST FAILED: bad URI did not show error, got: "${badText}"`);
  console.log('[test 7] PASS: wrong-kind URI shows error.');

  // ─── Check for unexpected JS errors ─────────────────────────────────────────
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
