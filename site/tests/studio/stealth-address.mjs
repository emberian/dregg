/**
 * Playwright ad-hoc test for <dregg-stealth-address> inspector.
 *
 * Run with:
 *   node tests/studio/stealth-address.mjs
 *
 * Requires dist/ to be served on port 8080:
 *   npx serve . -l 8080
 *
 * What this test does:
 *  1. Navigates to /studio (has wasm + in-memory runtime + dregg-app#app)
 *  2. Waits for dregg:ready and runtime attachment
 *  3. Injects stealth-address.js module
 *  4. Verifies custom element registration
 *
 *  Test A — default (read) mode:
 *    Mount with a plausible dregg://stealth/<hex> URI.
 *    Verify: header "stealth address" kind badge, KV rows for spend/view/meta keys.
 *    Verify: received panel renders (empty is fine).
 *
 *  Test B — demo mode:
 *    Mount with mode="demo".
 *    Verify: all 5 step panels present.
 *    Click "Derive Keys" → step 1 result rows appear.
 *    Fill amount=123, click "Send Private Transfer" → step 2 result rows appear.
 *    Click "Generate Range Proof" → step 3 result rows appear.
 *    Click "Scan Announcements" → step 4 result rows appear.
 *    Click "Verify Conservation" → step 5 result + conservation badge appear.
 *    Verify: privacy badge present (Fully Private, Selective, or Trusted).
 *    Verify: timeline <details> expands.
 *
 *  Test C — compact mode:
 *    Mount with mode="compact".
 *    Verify: renders inline with "stealth" kind text.
 *
 *  Test D — no critical JS errors throughout.
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

  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  console.log('[test] dreggUi:ready fired.');

  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] runtime attached to <dregg-app#app>.');

  // Inject the stealth-address inspector module
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/stealth-address.js`,
    type: 'module',
  });
  await page.waitForFunction(() => !!customElements.get('dregg-stealth-address'), { timeout: 8000 });
  console.log('[test] <dregg-stealth-address> custom element registered.');

  // ─── Test A: default (read) mode ─────────────────────────────────────────

  // A plausible 128-hex meta address (spend_pub || view_pub each 32 bytes)
  const META_HEX = 'a'.repeat(64) + 'b'.repeat(64);
  await page.evaluate((metaHex) => {
    const el = document.createElement('dregg-stealth-address');
    el.setAttribute('uri', `dregg://stealth/${metaHex}`);
    el.setAttribute('id', 'test-stealth-default');
    document.getElementById('app').appendChild(el);
  }, META_HEX);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-default');
    return el && el.querySelector('.dregg-stealth');
  }, { timeout: 8000 });
  console.log('[test A] Element rendered.');

  // Kind badge
  const kindText = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-default');
    const badge = el && el.querySelector('.dregg-stealth__kind');
    return badge ? badge.textContent.trim() : '';
  });
  if (!kindText.includes('stealth')) {
    throw new Error(`[test A] FAIL: kind badge missing, got "${kindText}"`);
  }
  console.log(`[test A] PASS: kind badge = "${kindText}"`);

  // Privacy badge
  const privacyBadge = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-default');
    const b = el && el.querySelector('.dregg-stealth__badge');
    return b ? b.textContent.trim() : '';
  });
  const validLevels = ['Fully Private', 'Selective', 'Trusted'];
  if (!validLevels.includes(privacyBadge)) {
    throw new Error(`[test A] FAIL: privacy badge unexpected: "${privacyBadge}"`);
  }
  console.log(`[test A] PASS: privacy badge = "${privacyBadge}"`);

  // KV grid should have spend pubkey and view pubkey rows
  const kvDts = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-default');
    return Array.from(el.querySelectorAll('.dregg-stealth__kv dt')).map(dt => dt.textContent.trim());
  });
  if (!kvDts.includes('spend pubkey')) {
    throw new Error(`[test A] FAIL: 'spend pubkey' dt not found. Got: ${JSON.stringify(kvDts)}`);
  }
  if (!kvDts.includes('view pubkey')) {
    throw new Error(`[test A] FAIL: 'view pubkey' dt not found. Got: ${JSON.stringify(kvDts)}`);
  }
  console.log(`[test A] PASS: KV grid has spend pubkey + view pubkey. dts=${JSON.stringify(kvDts)}`);

  // Received panel
  const hasReceivedPanel = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-default');
    return !!el.querySelector('.dregg-stealth__received');
  });
  if (!hasReceivedPanel) {
    throw new Error('[test A] FAIL: received panel missing');
  }
  console.log('[test A] PASS: received panel present.');

  // ─── Test B: demo mode ────────────────────────────────────────────────────

  await page.evaluate(() => {
    const el = document.createElement('dregg-stealth-address');
    el.setAttribute('mode', 'demo');
    el.setAttribute('id', 'test-stealth-demo');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-demo');
    return el && el.querySelector('.dregg-stealth-demo__step');
  }, { timeout: 8000 });
  console.log('[test B] Demo element rendered.');

  // All 5 step panels should be present
  const stepCount = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    return el.querySelectorAll('.dregg-stealth-demo__step').length;
  });
  if (stepCount !== 5) {
    throw new Error(`[test B] FAIL: expected 5 step panels, got ${stepCount}`);
  }
  console.log(`[test B] PASS: ${stepCount} step panels present.`);

  // Step 1: Click "Derive Keys"
  await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    // Click the first primary button (Derive Keys)
    const btns = el.querySelectorAll('.dregg-stealth-demo__btn--primary');
    if (btns[0]) btns[0].click();
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-demo');
    const kv = el && el.querySelectorAll('.dregg-stealth-demo__kv');
    return kv && kv.length > 0;
  }, { timeout: 5000 });
  console.log('[test B] Step 1 result KV rendered.');

  const step1KvDts = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    return Array.from(el.querySelectorAll('.dregg-stealth-demo__kv dt')).map(dt => dt.textContent.trim());
  });
  if (!step1KvDts.includes('view pubkey') && !step1KvDts.includes('spend pubkey')) {
    throw new Error(`[test B] FAIL: step 1 KV rows missing. Got: ${JSON.stringify(step1KvDts)}`);
  }
  console.log(`[test B] PASS: step 1 key rows present: ${JSON.stringify(step1KvDts.slice(0, 4))}`);

  // Step 2: Set amount=123, click "Send Private Transfer"
  await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const amountInput = el.querySelector('input[type="number"]');
    if (amountInput) {
      const nativeInputValueSetter = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, 'value').set;
      nativeInputValueSetter.call(amountInput, '123');
      amountInput.dispatchEvent(new Event('input', { bubbles: true }));
    }
    // Click second primary button (Send Private Transfer)
    const btns = el.querySelectorAll('.dregg-stealth-demo__btn--primary');
    if (btns[1]) btns[1].click();
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-demo');
    const dts = Array.from(el.querySelectorAll('.dregg-stealth-demo__kv dt')).map(d => d.textContent.trim());
    return dts.includes('one-time pubkey') || dts.includes('commitment');
  }, { timeout: 5000 });
  console.log('[test B] Step 2 result rendered (one-time pubkey / commitment).');

  // Step 3: Click "Generate Range Proof"
  await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const btns = el.querySelectorAll('.dregg-stealth-demo__btn--primary');
    if (btns[2]) btns[2].click();
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-demo');
    const dts = Array.from(el.querySelectorAll('.dregg-stealth-demo__kv dt')).map(d => d.textContent.trim());
    return dts.includes('proof size') || dts.includes('range');
  }, { timeout: 5000 });
  console.log('[test B] Step 3 result rendered (proof size).');

  // Step 4: Click "Scan Announcements"
  await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const btns = el.querySelectorAll('.dregg-stealth-demo__btn--primary');
    if (btns[3]) btns[3].click();
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-demo');
    const dts = Array.from(el.querySelectorAll('.dregg-stealth-demo__kv dt')).map(d => d.textContent.trim());
    return dts.includes('scanned') || dts.includes('owned');
  }, { timeout: 5000 });
  console.log('[test B] Step 4 result rendered (scan results).');

  const scanDts = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    return Array.from(el.querySelectorAll('.dregg-stealth-demo__kv dt')).map(d => d.textContent.trim());
  });
  if (!scanDts.includes('scanned')) {
    throw new Error(`[test B] FAIL: scan result KV missing 'scanned'. Got: ${JSON.stringify(scanDts)}`);
  }
  console.log('[test B] PASS: step 4 scan results present.');

  // Step 5: Click "Verify Conservation"
  await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const btns = el.querySelectorAll('.dregg-stealth-demo__btn--primary');
    if (btns[4]) btns[4].click();
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-demo');
    return !!el.querySelector('.dregg-stealth-demo__conservation');
  }, { timeout: 5000 });
  console.log('[test B] Step 5 conservation panel rendered.');

  const conservText = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const div = el.querySelector('.dregg-stealth-demo__conservation');
    return div ? div.textContent.trim() : '';
  });
  if (!conservText) {
    throw new Error('[test B] FAIL: conservation text empty');
  }
  // verify_conservation_proof is now REAL: a balanced set proves the Schnorr
  // excess (value balance). The old "STUB — verify_conservation_proof not yet
  // implemented" expectation is stale; assert the real VALID verdict instead.
  if (!conservText.includes('VALID') || conservText.includes('STUB')) {
    throw new Error(`[test B] FAIL: expected real VALID conservation verdict, got: "${conservText.slice(0, 120)}"`);
  }
  console.log(`[test B] PASS: real conservation verdict = "${conservText.slice(0, 80)}"`);

  // The range-proof row must now show REAL Bulletproofs were verified
  // (range_proofs_checked=true), not a placeholder.
  const conservKv = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const rows = Array.from(el.querySelectorAll('.dregg-stealth-demo__step'))
      .find(s => s.textContent.includes('Verify Conservation'));
    return rows ? rows.textContent : '';
  });
  if (!/Bulletproof/i.test(conservKv) || /placeholder/i.test(conservKv)) {
    throw new Error(`[test B] FAIL: conservation panel must show real Bulletproof range proofs, not a placeholder. Got: "${conservKv.slice(0, 200)}"`);
  }
  if (!/range proofs[\s\S]*true/i.test(conservKv)) {
    throw new Error(`[test B] FAIL: range_proofs_checked must be true. Got: "${conservKv.slice(0, 200)}"`);
  }
  console.log('[test B] PASS: real Bulletproof range proofs verified (range_proofs_checked=true).');

  // Privacy badge in demo mode
  const demoPrivacyBadge = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    const b = el && el.querySelector('.dregg-stealth__badge');
    return b ? b.textContent.trim() : '';
  });
  if (!validLevels.includes(demoPrivacyBadge)) {
    throw new Error(`[test B] FAIL: demo privacy badge unexpected: "${demoPrivacyBadge}"`);
  }
  console.log(`[test B] PASS: demo privacy badge = "${demoPrivacyBadge}"`);

  // Timeline details present
  const hasTimeline = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    return !!el.querySelector('.dregg-stealth-demo__timeline');
  });
  if (!hasTimeline) {
    throw new Error('[test B] FAIL: timeline not rendered after completing steps');
  }
  console.log('[test B] PASS: timeline present after full flow.');

  const timelineEntries = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-demo');
    return el.querySelectorAll('.dregg-stealth-demo__timeline-entry').length;
  });
  if (timelineEntries === 0) {
    throw new Error('[test B] FAIL: timeline has no entries');
  }
  console.log(`[test B] PASS: ${timelineEntries} timeline entries.`);

  // ─── Test C: compact mode ─────────────────────────────────────────────────

  await page.evaluate(() => {
    const el = document.createElement('dregg-stealth-address');
    el.setAttribute('uri', 'dregg://stealth/ccccdddd1234abcd');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-stealth-compact');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-stealth-compact');
    return el && el.children.length > 0;
  }, { timeout: 5000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-stealth-compact');
    return el ? el.textContent.trim() : '';
  });
  if (!compactText.toLowerCase().includes('stealth')) {
    throw new Error(`[test C] FAIL: compact mode text missing "stealth". Got: "${compactText}"`);
  }
  console.log(`[test C] PASS: compact mode = "${compactText.slice(0, 80)}"`);

  // ─── Test D: no critical JS errors ───────────────────────────────────────

  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM not available') &&
    !e.includes('net::ERR_') &&
    !e.includes('Failed to fetch')
  );
  if (realErrors.length > 0) {
    console.error('[test D] JS errors during run:', realErrors);
    throw new Error(`[test D] FAIL: JS errors: ${realErrors.join('; ')}`);
  }
  console.log('[test D] PASS: no critical JS errors.');

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message || err);
  process.exit(1);
});
