/**
 * Playwright ad-hoc test for <pyana-predicate> inspector.
 *
 * Run from site/ root:
 *   node tests/studio/predicate-inspector.mjs
 *
 * Requires the dist/ site to be served on port 8080:
 *   npx serve dist -l 8080
 * (or the wasm-enabled dev server — any server that has the studio + wasm bundle)
 *
 * What this test does:
 *  1. Navigate to /studio (wasm runtime attached at <pyana-app#app>)
 *  2. Wait for pyana:ready + runtime attached
 *  3. Inject predicate.js module
 *  4. Test compact mode: "N facts · M rules" summary renders
 *  5. Test read mode: facts list + rules list render without errors
 *  6. Test editor mode: facts list, rules pane, evaluate button render
 *  7. Evaluate with a real wasm call: allow case — ALLOW badge appears, trace renders
 *  8. Evaluate deny case — DENY badge appears
 *  9. Verify derivation trace steps render (step rows with .pyana-pred__trace-step)
 * 10. JS error check: no unexpected errors during the run
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

  console.log('[test] Navigating to /studio ...');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Wait for Preact/signals + pyanaUi ready
  await page.waitForFunction(() => !!window.pyanaUi, { timeout: 20000 });
  console.log('[test] pyanaUi ready.');

  // Wait for wasm runtime attached to <pyana-app#app>
  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] wasm runtime attached.');

  // Inject predicate.js as a module
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/predicate.js`,
    type: 'module',
  });
  await page.waitForFunction(() => !!customElements.get('pyana-predicate'), { timeout: 8000 });
  console.log('[test] <pyana-predicate> custom element registered.');

  // ── Test 1: compact mode ────────────────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-predicate');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-pred-compact');
    el.setAttribute('data-predicate', JSON.stringify({
      facts: [
        { predicate: 'app', terms: ['my-app', 'read'] },
        { predicate: 'service', terms: ['dns', 'read'] },
      ],
    }));
    document.body.appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pred-compact');
    return el && el.innerHTML.trim().length > 0;
  }, { timeout: 5000 });

  const compactText = await page.$eval('#test-pred-compact', el => el.innerText.trim());
  console.log(`[test 1] Compact text: "${compactText}"`);
  if (!compactText.includes('fact')) throw new Error('TEST FAILED: compact mode should show "fact"');
  if (!compactText.includes('rule')) throw new Error('TEST FAILED: compact mode should show "rule"');
  console.log('[test 1] PASS: compact mode shows fact/rule summary.');

  // ── Test 2: read mode with facts ───────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-predicate');
    el.setAttribute('mode', 'default');
    el.setAttribute('id', 'test-pred-read');
    el.setAttribute('data-predicate', JSON.stringify({
      facts: [
        { predicate: 'action_allowed', terms: ['my-app', 'read'] },
        { predicate: 'action_allowed', terms: ['my-app', 'write'] },
        { predicate: 'svc_action_allowed', terms: ['dns', 'read'] },
      ],
    }));
    document.body.appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pred-read');
    return el && el.querySelector('.pyana-pred__badge');
  }, { timeout: 5000 });

  const hasBadge = await page.$eval('#test-pred-read', el => !!el.querySelector('.pyana-pred__badge'));
  if (!hasBadge) throw new Error('TEST FAILED: read mode missing badge');

  const factRowCount = await page.$eval('#test-pred-read', el =>
    el.querySelectorAll('.pyana-pred__fact-row').length
  );
  console.log(`[test 2] Fact rows in read mode: ${factRowCount}`);
  if (factRowCount < 3) throw new Error(`TEST FAILED: expected ≥3 fact rows, got ${factRowCount}`);

  const ruleRowCount = await page.$eval('#test-pred-read', el =>
    el.querySelectorAll('.pyana-pred__rule-row').length
  );
  console.log(`[test 2] Rule rows in read mode: ${ruleRowCount}`);
  if (ruleRowCount < 3) throw new Error(`TEST FAILED: expected ≥3 rule rows (incl. default), got ${ruleRowCount}`);

  console.log('[test 2] PASS: read mode renders facts list + rules list.');

  // ── Test 3: editor mode renders ────────────────────────────────────────────
  // Mount editor inside <pyana-app#app> so it can find the runtime
  await page.evaluate(() => {
    const el = document.createElement('pyana-predicate');
    el.setAttribute('mode', 'editor');
    el.setAttribute('id', 'test-pred-editor');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pred-editor');
    return el && el.querySelector('.pyana-pred__eval-btn');
  }, { timeout: 8000 });

  const hasEvalBtn = await page.$eval('#test-pred-editor', el =>
    !!el.querySelector('.pyana-pred__eval-btn')
  );
  if (!hasEvalBtn) throw new Error('TEST FAILED: editor mode missing evaluate button');

  const hasReqInputs = await page.$eval('#test-pred-editor', el =>
    el.querySelectorAll('.pyana-pred__req-input').length >= 2
  );
  if (!hasReqInputs) throw new Error('TEST FAILED: editor mode missing request inputs');

  const editorFactRows = await page.$eval('#test-pred-editor', el =>
    el.querySelectorAll('.pyana-pred__fact-row').length
  );
  console.log(`[test 3] Editor initial fact rows: ${editorFactRows}`);
  if (editorFactRows < 1) throw new Error('TEST FAILED: editor mode should start with default facts');

  console.log('[test 3] PASS: editor mode renders facts, request fields, evaluate button.');

  // ── Test 4: evaluate — ALLOW case ──────────────────────────────────────────
  // Default facts include app=my-app,read,write + request app_id=my-app action=read → ALLOW
  await page.click('#test-pred-editor .pyana-pred__eval-btn');

  // Wait for decision badge to appear
  await page.waitForFunction(() => {
    const el = document.getElementById('test-pred-editor');
    return el && el.querySelector('.pyana-pred__decision') !== null;
  }, { timeout: 8000 });

  const decisionText = await page.$eval('#test-pred-editor .pyana-pred__decision', el =>
    el.textContent.trim()
  );
  console.log(`[test 4] Decision badge: "${decisionText}"`);
  if (decisionText !== 'ALLOW') throw new Error(`TEST FAILED: expected ALLOW, got "${decisionText}"`);

  // Trace pane should be visible
  const traceVisible = await page.$eval('#test-pred-editor .pyana-pred__section--trace', el => {
    return window.getComputedStyle(el).display !== 'none';
  });
  if (!traceVisible) throw new Error('TEST FAILED: trace pane not visible after evaluation');

  console.log('[test 4] PASS: ALLOW decision badge appears after evaluation.');

  // ── Test 5: trace steps render ─────────────────────────────────────────────
  const traceStepCount = await page.$eval('#test-pred-editor', el =>
    el.querySelectorAll('.pyana-pred__trace-step').length
  );
  console.log(`[test 5] Trace step rows: ${traceStepCount}`);
  // The trace may have 0 or more steps depending on which rule matched.
  // Either trace-step rows OR trace-empty message should be present.
  const traceEmpty = await page.$eval('#test-pred-editor', el =>
    !!el.querySelector('.pyana-pred__trace-empty, .pyana-pred__trace-step')
  );
  if (!traceEmpty) throw new Error('TEST FAILED: neither trace steps nor empty message rendered');

  // If steps exist, verify first step has the expected structure
  if (traceStepCount > 0) {
    const firstStepHtml = await page.$eval('#test-pred-editor .pyana-pred__trace-step', el =>
      el.innerHTML
    );
    const hasRuleLabel = firstStepHtml.includes('rule #') || firstStepHtml.includes('allow_');
    if (!hasRuleLabel) throw new Error('TEST FAILED: trace step missing rule label');
    console.log('[test 5] PASS: trace step rows render with rule labels.');
  } else {
    console.log('[test 5] PASS: empty trace message rendered (rule matched without explicit steps).');
  }

  // ── Test 6: DENY case via "Try denied request" button ────────────────────
  await page.click('#test-pred-editor .pyana-pred__deny-btn');
  // Verify inputs were updated
  const appIdAfterDeny = await page.$eval(
    '#test-pred-editor .pyana-pred__req-input[name="app_id"]',
    el => el.value
  );
  console.log(`[test 6] App ID after deny-example: "${appIdAfterDeny}"`);
  if (appIdAfterDeny !== 'unknown-app') throw new Error(`TEST FAILED: expected "unknown-app", got "${appIdAfterDeny}"`);

  // Now evaluate
  await page.click('#test-pred-editor .pyana-pred__eval-btn');

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pred-editor');
    const badge = el && el.querySelector('.pyana-pred__decision');
    return badge && badge.textContent.trim() === 'DENY';
  }, { timeout: 8000 });

  const denyDecision = await page.$eval('#test-pred-editor .pyana-pred__decision', el =>
    el.textContent.trim()
  );
  console.log(`[test 6] Decision after deny example: "${denyDecision}"`);
  if (denyDecision !== 'DENY') throw new Error(`TEST FAILED: expected DENY, got "${denyDecision}"`);

  console.log('[test 6] PASS: DENY decision badge appears for unknown-app/delete request.');

  // ── Test 7: compact mode with last_result ─────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-predicate');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-pred-compact-result');
    el.setAttribute('data-predicate', JSON.stringify({
      facts: [{ predicate: 'app', terms: ['x', 'read'] }],
      last_result: { conclusion: 'allow' },
    }));
    document.body.appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pred-compact-result');
    return el && el.querySelector('.pyana-pred__decision');
  }, { timeout: 5000 });

  const compactDecision = await page.$eval(
    '#test-pred-compact-result .pyana-pred__decision',
    el => el.textContent.trim()
  );
  console.log(`[test 7] Compact with result: "${compactDecision}"`);
  if (compactDecision !== 'ALLOW') throw new Error(`TEST FAILED: compact should show ALLOW, got "${compactDecision}"`);
  console.log('[test 7] PASS: compact mode shows inline ALLOW badge from last_result.');

  // ── JS error check ─────────────────────────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM not available') &&
    !e.includes('net::ERR_') &&
    !e.includes('Failed to fetch')
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
